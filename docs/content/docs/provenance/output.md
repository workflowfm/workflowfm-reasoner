---
title: "Output Provenance"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-07T15:49:41+01:00
draft: false
weight: 620
---

Each process may only have a single, possibly composite output. When composing processes, the output of the composition often consists of parts of the outputs of its components.

In our example above, `P` has output `A ⊗ (C ⊕ D)` consisting of `A` coming from `P1` and `C ⊕ D` coming from `P2`. This is exactly what the provenance tree represents.

The output provenance tree of each process is stored in its structure and used during composition. It is also copied as an output provenance entry, which maps each process name to its output provenance, in the composition state. This allows the composition tactics to gain access to that information.

Apart from names of component atomic (or collapsed composite) processes who own part of the output, the leaves of an output provenance tree may have special values as described next.


## The `&` prefix {#OutputMerge}

Provenance leaves starting with a `&` prefix indicate a "merge node" as the source of the output.

When using `WITH` and in some cases of optional outputs in `JOIN` we need to introduce a "merge node" to indicate that 2 (or more) outputs are merged into a single (usually optional) output. This is one way of showing how the options come together, without showing disconnected outputs from different processes.

Outputs coming out of such a merge node can no longer be linked back to the components they came from without breaking the correlation between the options.

In other cases, two equivalent options are merged into a single output as an "optimization" step to avoid redundant case splits. A merge node is also used here, and the merged output has an unclear (double?) provenance.

Perhaps the simplest example is shown below:

{{< picture "provenance/SimplestMerge.png" "provenance/SimplestMerge.png" "Light blue diagram depicting an example of a simple merge of a process P with input X and optional output A or E and a process Q with input E and output A. The composite workflow shows P and Q connected with an edge labelled E and their outputs connected to a rhombus with the & symbol and a single output A." >}}

In this, the second option `E` of `P` is converted to the type of the first option `A` through `Q`. This fits the intuition of a recovery process that recovers from an exception `E` to produce an expected `A`. The result of the composition is a single `A` output, whether it came from `P` in the first place or from `Q` after "recovery".

If `A` gets connected to another process, whether the source will be `P` or `Q` is only determined at runtime. We therefore use the `&` merge node and label the output provenance to represent that the `A` output will be coming from this particular merge node.

In such cases we mark the provenance of the new output using `&` followed by the name of the composition that introduced the merge node.


## Unused inputs and the `:` tag {#unused-inputs-and-the-tag}

When dealing with optional outputs, the `JOIN` action often needs to build buffers for unused inputs. See the standard example below:

{{< picture "provenance/StandardOptionalJoin.png" "provenance/StandardOptionalJoin.png" "Light blue diagram depicting a process P with an optional output A or E. E is connected to a process Q, which also has another input B and an output Y. A and Y are connected to a triangle with an optional output, one with edges A and B and one consisting of Y." >}}

What should the output provenance for `B` be? Here it clearly should be `Q`. However, `Q` may not be atomic, but an intermediate composition instead. The reasoner does not know whether `Q` is composed of multiple components and which component `B` is coming from.

Mirroring the image above, here are 2 examples where `Q` is a composite process consisting of `Q1` and `Q2` (top) and `Q3` and `Q4` (bottom):

{{< picture "provenance/UnusedInputProvenance.png" "provenance/UnusedInputProvenance.png" "Light blue diagram depicting 2 worklflows of processes P, Q1, Q2 and P, Q3, Q4 respectively. P has an input X and connects to Q1 and Q3 through an edge E. Q1 and Q3 connect to Q2 and Q4 respectively through an edge C. P and Q2 connect to a triangle through edges A and Y respectively, and similarly for Q4 in the second workflow. The output of the triangle is an option between Y and two edges A and B. In the first workflow Q2 also has an input B, whereas in the second workflow Q3 has an input B instead." >}}

In the top case, `B` is an input of `Q2`, whereas in the bottom case `B` is an input of `Q3`. In both cases, the reasoner just sees an intermediate composition `Q` with inputs `B` and `E` and output `Y` as in the previous image. We therefore need a different way of tagging the provenance of `B` in a way that allows us to trace it back to `Q2` or `Q3`.

This is accomplished by reporting the channel `c` of the unused input `B`. In the example above, the reasoner will produce a provenance leaf `Q:c`, i.e. the name of the (possibly composite) process `Q` followed by a colon `:` followed by the name of the channel of the unused input `c`.

The reasoner is effectively telling the graph interface to search in the process `Q` for an input with channel `c` and use the owner of that input as the source of `B`.

This may cause issues when multiple identical components introduce the same channel name multiple times in the same composition. The reasoner does not currently diambiguate between those because it does not even have that information.
