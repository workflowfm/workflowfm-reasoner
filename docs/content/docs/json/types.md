---
title: "Main Types"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:18+01:00
draft: false
weight: 410
---

## Linear Propositions {#linprop}

`linprop`


#### Description: {#description}

[Linear terms](../../elements/resources) are either:

1.  atoms
2.  subterms connected by tensor or plus
3.  negations of terms


#### Structure: {#structure}

-   `type`: `string` = `"var" | "neg" | "times" | "plus"`
-   `name`: `string` = the name of the atom if `type = "var"`, otherwise ignored
-   `args`: `array` of [`linprop`](#linprop) = the list of arguments if `type` is `neg`, `times` or `plus`, otherwise ignored. Binary operators `times` and `plus` can have more than 2 arguments, in which case they are applied in a right associative way


## Annotated terms {#linterm}

`linterm`


#### Description: {#description}

Annotated terms are linear propositional terms annotated with a channel.


#### Structure: {#structure}

-   `cll`: [`linprop`](#linprop)
-   `channel`: `string`


## Composition actions {#action}

`action`


#### Description: {#description}

[Composition actions](../../elements/composition/#actions) describe a binary combination of 2 labelled processes.


#### Structure: {#structure}

-   `act`: `string` = the type of composition, currently `"JOIN" | "TENSOR" | "WITH"` for sequential, parallel, and conditional composition respectively
-   `larg`: `string` = the name of the first (or "left") component process
-   `lsel`: `string` = a string describing some relevant part of the left process component. This is different depending on the action type.
-   `rarg`: `string` = the name of the second (or "right") component process
-   `rsel`: `string` = a string describing some relevant part of the right process component. This is different depending on the action type.
-   `res`: `string` = the desired label for the resulting composition


## Provenance {#prov}

`prov`


#### Description: {#description}

[Provenance trees](../../elements/provenance) are used to determine the origin of each linear proposition in an input or output term.


#### Structure: {#structure}

-   `type`: `string` = `"source" | "times" | "plus"`
-   `name`: `string` = the provenance label if `type = "source"`, otherwise ignored
-   `args`: `array` of [`prov`](#prov) = the list of arguments if `type` is  `times` or `plus`, otherwise ignored. Binary operators `times` and `plus` can have more than 2 arguments, in which case they are applied in a right associative way


## Provenance entries {#proventry}

`prov_entry` and `iprov_entry`


#### Description: {#description}

[Provenance info](../../elements/provenance) is kept in the [actionstate](../../elements/composition/#actionstate). Provenance entries associate a provenance tree to the output (`prov_entry`) or input (`iprov_entry`) it corresponds to. Output provenance is associated with a process label whose output it describes. Input provenance is associated with an available input term.


#### Structure: {#structure}

`prov_entry`:

-   `name`: `string` = the name/label of the process whose output we are describing
-   `prov`: [`prov`](#prov) = the corresponding provenance tree

`iprov_entry`:

-   `term`: [`linprop`](#linprop) = the (non-negated) linear term of the input we are describing
-   `prov`: [`prov`](#prov) = the corresponding provenance tree


## Actionstate {#actionstate}

`actionstate`


#### Description: {#description}

The [actionstate](../../elements/composition/#actionstate) is used to convey state info to the prover and retrieve proof metadata afterwards.


#### Structure: {#structure}

-   `label`: `string` = a unique label identifying the composite process under contruction
-   `ctr`: `int` = a non-negative counter used to keep variables fresh. Expected to be initialized to `0`.
-   `buffered`: `array` of [`linprop`](#linprop) = the types of buffers that were constructed during proof. This used to be the way to determine buffered edges in the frontend, but is now obsolete thanks to the provenance trees.
-   `joined`: `array` of [`linterm`](#linterm) = the inputs that were used up/connected during a `JOIN` action.
-   `iprov`: `array` of [`iprov_entry`](#proventry) = input povenance entries
-   `prov`: `array` of [`prov_entry`](#proventry) = output provenance entries


## Agent {#agent}

`agent`

An agent refers to a &pi;-calculus definition corresponding to a process specification. Currently this is just a string, but we have plans to adopt a more structured representation in the near future.


## Process {#process}

`process`


#### Description: {#description}

The complete specification of a [process](../../elements/processes).


#### Structure: {#structure}

-   `name`: `string` = a name/label for the process
-   `inputs`: `array` of [`linterm`](#linterm)
-   `output`: [`linterm`](#linterm)
-   `prov`: [`prov`](#prov) = the output provenance
-   `proc`: [`agent`](#agent) = the pi-calculus specification
-   `actions`: `array` of [`action`](#action) = a list of composition actions that construct this process. Empty if the process is atomic.
-   `copier`: `bool` = true if the prover determines this to be a [copy node](../../elements/processes/#copynodes)
-   `intermediate`: `bool` = true if this is an [intermediate composition step](../../elements/processes/#intermediate) (as opposed to an atomic process or completed composition)
