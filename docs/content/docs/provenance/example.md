---
title: "Example"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-07T15:49:41+01:00
draft: false
weight: 610
---

We begin with a motivating example to explain the purpose that provenance fulfils for the visualization of resource-based composition.


## Specification {#specification}

Assume the following process specifications:

-   `P1`: `⊢ NEG X, A ⊗ B`
-   `P2`: `⊢ NEG B, C ⊕ D`
-   `Q1`: `⊢ NEG A, E`
-   `Q2`: `⊢ NEG E, NEG (C ⊕ D), Y`

We then perform `JOIN` operations for each pair, obtaining the following intermediate compositions:

-   `P`: `⊢ NEG X, A ⊗ (C ⊕ D)`
-   `Q`: `⊢ NEG A, NEG (C ⊕ D), Y`

Finally, we `JOIN` the 2 results to obtain the final composition:

-   `R`: `⊢ NEG X, Y`


## Visualization {#visualization}

At the logical level, the composition above seems straightforward. The visualization, however, needs to reveal more information. We need to accurately depict how the individual components are connected to each other, and how resources flow between them.

The image below shows the following processes in this order: `P1`, `P2`, `P`, `Q`, and `R`.

{{< picture "provenance/ProvenanceExample.png" "provenance/ProvenanceExample.png" "Orange diagrams depicting the described processes P1, P2, P, Q, and R" >}}

In the visualization of `R`, the system has inferred that resource `A` connects `P1` to `Q1`, whereas `P2` and `Q2` are connected by `C ⊕ D`. This is achieved despite the fact that the last composition action joined intermediate processes `P` and `Q`, meaning the whole term `A ⊗ (C ⊕ D)` was "cut" in one go.

This is accomplished by tracking the **input** and **output** provenance of the involved processes. Specifically, when composing `P`, we track its output provenance for the output `A ⊗ (C ⊕ D)` is one where `A` came from `P1` and `(C ⊕ D)` came from `P2`. Similarly, when composing `Q`, we track the input provenance, i.e. that `NEG A` belongs to `Q1` and `NEG (C ⊕ D)` belongs to `Q2`. This way, when `P` and `Q` are joined, we know exactly where each connected resource is coming from and going to.
