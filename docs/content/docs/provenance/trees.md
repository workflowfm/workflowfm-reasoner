---
title: "Provenance Trees"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-07T15:49:41+01:00
draft: false
weight: 620
---

We want to be able to track provenance of specific CLL resources. This means subterms of the same term can have different provenance. For this reason, we track provenance using a binary tree structure that matches the syntax tree of the term. The leaves of the tree contain provenance values instead of CLL propositions.

Here is the syntax and provenance trees for the output of `P` from the example:

```text
⊗         ⊗
|\        |\
| \       | \
A  ⊕      P1 ⊕
   |\        |\
   | \       | \
   C  D      P2 P2
```

If all the propositions in a (sub)tree have the same provenance, we can collapse the provenance (sub)tree to a single node:

```text
⊗         ⊗
|\        |\
| \       | \
A  ⊕      P1 P2
   |\
   | \
   C  D
```
