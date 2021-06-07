---
title: "Input Provenance"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-07T15:49:42+01:00
draft: false
weight: 630
---

Each process can have multiple inputs, each with its own unique channel. This means we can generally track the owner of an input through the channel.

In our example above, `NEG (C ⊕ D)` of `Q2` will have a unique channel name, let's assume `cQ`. When composing `Q1` with `Q2`, this input is not affected. This means if we try to connect something to it, we already know `cQ` belongs to `Q2` so we can track its provenance and connect the graph appropriately.

The composition actions only affect input channels in 2 ways:

1.  The `WITH` action constructs new inputs that are options or merges of other inputs. These are reported in the composition step and their provenance is linked to the composite process, not its components.
2.  The `JOIN` action manipulates inputs in order to match the output of the other (left) component. This includes adding buffers, using inputs from different components and merging options. In this case, we need to track the provenance of each part in the constructed input.

Back to our example, when composing `P` with `Q`, we connect `NEG A` with `NEG (C ⊕ D)` to create a new input `NEG (A ⊗ (C ⊕ D))` that matches the output of `P`. At that point, we need to track that `NEG A` had some channel `cP` which can be traced back to `P`, whereas `NEG (C ⊕ D)` had channel `cQ` that we know belongs to `Q`. For this reason, we build the following provenance tree (shown next to the input parse tree), while ignoring the negation:

```text
⊗         ⊗
|\        |\
| \       | \
A  ⊕      cP ⊕
   |\        |\
   | \       | \
   C  D     cQ cQ
```

Note that the leaves of an input provenance tree, in principle, contain channels as opposed to those of an output provenance tree which contain process names.

There are a few particularities and special cases of leaves for input provenance, which we describe next.


## Disambiguating same channels with a `:` tag {#disambiguating-same-channels-with-a-tag}

Assume a process `Q` with an input `A ⊕ B` on channel `cQ`. In the image shown below, we `TENSOR` `Q` with itself and then `JOIN` it with a process `P` with output `(A ⊕ B) ⊗ (A ⊕ B)`:

{{< picture "provenance/SameChannelJoin.png" "provenance/SameChannelJoin.png" "Light blue diagram depicting a process P with input I connected to two processes both named Q, each through 2 dashed edges A and B. The 2 Q processes each have a X output which are connected to a triangle. The output of the triangle is 2 X edges." >}}

As we are joining `P` to the the 2 `Q` processes, the reasoner will apply the par rule to compose the 2 `A ⊗ B` inputs into one that matches the output of `P`. Sticking to the explanation of input provenance we provided above, the input provenance for the composite input will be `(cQ ⊕ cQ) ⊗ (cQ ⊕ cQ)`.

This would lead the graph engine to look for 4x `cQ` channels and fail because there are only 2 available, one for each instance of `Q`. The reasoner needs to somehow convey the information that the first 2 `cQ` channels in the provenance tree refer to the **same** channel, whereas the other 2 `cQ` channels refer to a single other channel.

This is accomplished by tagging each channel in the provenance tree with an integer. If 2 leaves in the provenance tree have the same channel **and** same number, they refer to the same, single channel. If hey have the same channel name, but a different number, they refer to 2 separate instances of that channel. Note that the actual number used has no other significance and is merely linked to an internal proof counter.

In our example, the reasoner will report an input provenance `(cQ:4 ⊕ cQ:4) ⊗ (cQ:7 ⊕ cQ:7)` (or some other numbers instead of 4 and 7). This is how the graph engine that generated the image above knew how to connect one `A` and one `B` to the top `Q`, corresponding to channel `cQ:4`, and the other `A` and the other `B` to the second `Q`, corresponding to channel `cQ:7`.


## The `#` provenance {#the-provenance}

In some cases, an input being connected does not feed to any (atomic) process, but belongs to a buffer that is introduced. Such an input will be forwarded to the output of the composite process without change.

The reasoner reports the input provenance of such buffers using a hash `#` label for the leaf.

In our [current composer implementation](https://github.com/PetrosPapapa/WorkflowFM-composer), we use a triangle "join" (or "terminator") node as a target to connect buffered resources to.


## The `&` prefix {#the-and-prefix}

The issue of [merged options in output provenance]({{< relref "output#OutputMerge" >}}) needs to be dealt with in input provenance too.

Let's revisit the same example:

{{< picture "provenance/SimplestMerge.png" "provenance/SimplestMerge.png" "Light blue diagram depicting an example of a simple merge of a process P with input X and optional output A or E and a process Q with input E and output A. The composite workflow shows P and Q connected with an edge labelled E and their outputs connected to a rhombus with the & symbol and a single output A." >}}

As we are joining `P` and `Q`, the reasoner constructs an optional input `A ⊕ E` for `Q` using its existing input `E` and introducing a buffer of type `A`. Once the new input is constructed, we need to provide its input provenance. This must be such that `E` gets connected to `Q`, whereas `A` is connected to the merge node.

The reported input provenance is `&_Step1 ⊕ cQ:5`, where `_Step1` the name of the composition, `cQ` the input channel of `Q`, and `5` some integer.
