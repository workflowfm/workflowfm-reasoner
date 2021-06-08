---
title: "Resources"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-08T00:15:38+01:00
draft: false
weight: 210
---

Processes are specified based on their input and output resources. Each resource is specified by its type and a &pi;-calculus channel that receives or sends it.


## Resource types {#resource-types}

Resource types are specified by a proposition in linear logic. In HOL Light these are propositions of type `` `:LinProp` ``.

Resource types can be composed using the following logical connectives:

| Connective   | HOL Light Syntax | Interpretation                                      |
|:------------:|:----------------:|:----------------------------------------------------|
| A &otimes; B | A \*\* B         | Two resources A and B in parallel.                  |
| A &oplus; B  | A ++ B           | Optional resource of either type A or B (not both). |

Different combinations of these operators can be used to express composite resource types of arbitrary complexity.

Typically, composite resource types involving these 2 operators represent **output** resources. In contrast, **input** resources are expressed as the _negation_ of output resources, using the operator `NEG`.

For exmaple, this means the type `` `NEG (A ** B)` `` represents two parallel _input_ resources.

Negated duals of the &otimes; and &oplus; operators do exist and are as follows:

| Connective   | Dual        | HOL Light Syntax |
|:------------:|:-----------:|:----------------:|
| A &otimes; B | A &#8523; B | A % B            |
| A &oplus; B  | A & B       | A & B            |

For example, this makes the followning expressions equivalent:
`NEG (A ** B) = NEG A % NEG B`

However, the reasoner is developed to work with _polarized_ types, i.e. resource types that only use the &otimes; and &oplus; connectives and the negations of such types.

{{< tip warning >}}
Mixing up input and output connectives and arbitrary negations may lead to unpredictable results.
{{< /tip >}}

This means that, for process specification and composition, you are expected to use atomic resource types or composite ones with the &otimes; and &oplus; operators. If you need to explicitly state that a resource type is an _input_, then negate the whole term using `NEG()`.

The reasoner often allows you to not even use `NEG` when a resource type is unambiguously expected to be an input.


## Channels {#channels}

Each resource type in a process specification is either received (input) or sent (output) through a &pi;-calculus channel. Generally, the reasoner aims to minimize the user's interaction with &pi;-calculus components. In the case of channels, the reasoner will automatically generate appropriate channel names for each resource. We present the channel syntax here for reference when it appears in various results.

{{< tip >}}
We say that a resource type or proposition is _annotated_ with a &pi;-calculus channel to form a _term_.
{{< /tip >}}

At a high level, annotations simply appear as pairs of resource types and channels.

At the logic level, the corresponding type of a _term_ in HOL Light is `` `:(num)LinTerm` ``.

Note the use of numbers (`num`) in that type. This represents the type of channels, which in principle could be any desired HOL Light type. Numbers make many reasoning tasks easier, though for the most part in practice we work with named variables for channels.

Resource annotation is accomplished in the logic with the HOL Light operator `<>`.

For example, the term `` `(A ** B) <> c` `` represents a channel `c` carrying an _output_ resource of type `A ** B` or, more specifically, _two_ output resources of type s `A` and `B` respectively in parallel.
