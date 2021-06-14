---
title: "Composition"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:25:46+01:00
draft: false
weight: 230
---

Composition is achieved through binary _actions_ that compose 2 processes together. Although there is some high level user control over the actions, the composition is automated and strictly follows the rules of linear logic.

The result is an [intermediate composite process]({{< relref "processes#intermediate" >}}) specified by its input and output resources and a [correct-by-construction](../../), executable &pi;-calculus definition. These processes can then be further composed using subsequent actions.

Performing an action involved the production and maintenance of a temporary internal state called an _[actionstate](#actionstate)_. This provides additional metadata about how a composition was achieved.


## Actions {#actions}

Binary composition actions have the following [structure](https://github.com/workflowfm/workflowfm-reasoner/blob/master/src/processes/actions.ml):

```ocaml
module Action = struct

  type t = {
    act : string;
    larg : string;
    lsel : string;
    rarg : string;
    rsel : string;
    res : string ;
  }

(*...*)
end;;
```

The fields can be described briefly as follows:

| Field  | Description                                                           |
|--------|-----------------------------------------------------------------------|
| `act`  | The name of the composition action to be performed.                   |
| `larg` | The name of the _first_ process (or left-hand-side) to be composed.   |
| `lsel` | A selector argument for the _first_ process.                          |
| `rarg` | The name of the _second_ process (or right-hand-side) to be composed. |
| `rsel` | A selector argument for the _second_ process.                         |
| `res`  | The desired name for the resulting composite process.                 |

By default there are 3 available composition actions:

1.  `TENSOR`: Parallel composition.
2.  `WITH`: Conditional composition.
3.  `JOIN`: Sequential composition.

These are described in more detail below.

Each action is associated with an implemented reasoning process (or _tactic_) in HOL Light. There is an internal associative map between tactic names and their actual implementation.

These reasoning processes follow the rules of linear logic in a formally verified way, with the associated guarantees of correctness we have discussed. This may sometimes lead to results in terms of input and output types for the composite process that may be more complex than expected. Though such results may seem unintuitive at first, their correctness is mathematically guaranteed, with an enforced systematic accounting of all resources (linearity). Small examples of this appear in our description of the actions below.

_Selector arguments_ allow users to specify a specific part of each composed process. These arguments have a different use in each action, but allow a high level of user control.


### Parallel - `TENSOR` {#tensor}

The `TENSOR` action composes two processes in _parallel_. This results in a composite process with all the inputs of both processes and their two outputs composed in a single parallel output.

Its name corresponds to the &otimes; operator (pronounced _times_ or _tensor_), which denotes [parallel resources]({{< relref "resources" >}}).


#### Selector arguments {#selector-arguments}

_Selector arguments_ are unused in the `TENSOR` action.


#### Example {#example}

As an example, the result `R` of the parallel composition of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `Y` and `Z` and output `C` is the following process:

```ocaml
{name = "R";
  inputs = [(`X`, `cP_X_1`); (`Y`, `cQ_Y_1`); (`Z`, `cQ_Z_2`)];
  output = (`(A ++ B) ** C`, `c_Step0___Step0__z1`);
  prov =
    Provnode ("times", Provnode ("plus", Provleaf "P", Provleaf "P"),
              Provleaf "Q");
  proc =
    `R (cP_X_1,cQ_Y_1,cQ_Z_2,c_R___R__z1) =
      PiTimesProc (A ++ B) C c_R___R__z1 oP_lB_A_Plus_B_rB_ oQ_C_
        (P (cP_X_1,oP_lB_A_Plus_B_rB_))
        (Q (cQ_Y_1,cQ_Z_2,oQ_C_))`;
  actions =
      [{Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = "";
        res = "R"}];
  copier = false;
  intermediate = true}
```

The action used can be noticed in the `actions` field above and is as follows:

```ocaml
{Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = ""; res = "R"}
```


### Conditional - `WITH` {#with}

The `WITH` action composes two processes _conditionally_.

More specifically, given an input `X` of a process `P` and a `Y` input of a process `Q`, their conditional composition yields a process with an optional input `X ++ Y`, i.e. one that can accept `X` _or_ `Y` (but not both). If the composite process receives `X` then `P` will be executed. Otherwise if the composite process receives `Y` then `Q` will be executed.

Its name corresponds to the & operator (pronounced _with_), which denotes [optional _input_ resources]({{< relref "resources" >}}).


#### Selector arguments {#selector-arguments}

_Selector arguments_ are used in the `WITH` action to specify which inputs should be used in the composite conditional input. The user needs to provide the _resource type_ of the input to be used from each process.

{{< tip warning >}}
There is no differentiation between distinct inputs with the same resource type. If multiple inputs with the same type exist in the same component process, this may result to the wrong one being used to form the condition. There is currently no way to affect this outcome.
{{< /tip >}}


#### Example {#example}

As an example, the result `R` of the conditional composition of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `Y` and `Z` and output `C` with inputs `X` and `Y` selected is the following process:

```ocaml
{name = "R";
  inputs = [(`Z`, `cQ_Z_2`); (`X ++ Y`, `c_R___R__x3`)];
  output = (`((A ++ B) ** Z) ++ C`, `c_R___R__y3`);
  prov =
   Provnode ("plus",
    Provnode ("times",
     Provnode ("plus", Provleaf "&_R", Provleaf "&_R"),
     Provleaf "&_R"),
    Provleaf "&_R");
  proc = (*...*);
  actions =
   [{Action.act = "WITH"; larg = "P"; lsel = "X"; rarg = "Q"; rsel = "Y";
     res = "R"}];
  copier = false;
  intermediate = true}
```

The action used can be noticed in the `actions` field above and is as follows:

```ocaml
{Action.act = "WITH"; larg = "P"; lsel = "X"; rarg = "Q"; rsel = "Y"; res = "R"}
```

It is worth noting the output type of the composite process, namely `((A ++ B) ** Z) ++ C`. This is an _optional_ output consisting of the outputs `A ++ B` and `C` of the two components, each of which may be produced depending on which process is executed at runtime.

Note, however, that the output `A ++ B` is paired with a new output `Z`. This corresponds to the second input `Z` of `Q`. This needs to still be an input in the composite process `R` because without it `Q` would not be able to execute. However, if `P` is executed then the input `Z` will not be used.

The rules of linear logic guarantee that unused resources are accounted for and do not just disappear. This leads to `Z` appearing as an output parallel to the output of `P`.


#### Merged inputs {#merged-inputs}

A notable case is one where the two conditionally composed processes have common inputs. In that case, the common inputs merge into inputs of the composite process.

For example, both composed processes may have an input of type `A` each. This means both processes require a resource of type `A` in order to execute. No matter which of the 2 processes ends up executing in the conditional execution at runtime, the composite process will require an input of type `A`.

Therefore, the composite process will have a _single_ `A` input. We call such an input a _merged_ input. These are reported explicitly in the _[actionstate](#actionstate)_.


### Sequential - `JOIN` {#join}

The `JOIN` action composes two processes _sequentially_.

More specifically, given a selected sub-term of the output of the first process and a matching input of the second process, their sequential composition yields a composite process where the resource corresponding to the selected sub-term is connected from the output of the first process to the output of the second.

{{< tip >}}
A _matching_ input is not necessarily one that matches exactly, but rather one that _can accept_ the selected output sub-term. For instance, an input of type `A ++ B` _can accept_ an output of type `A`.
{{< /tip >}}


#### Selector arguments {#selector-arguments}

The **first/left** selector argument is used in the `JOIN` action to select the output sub-term of the first/left process.

This is specified as a _path in the syntax tree_ of the process's output. It should follow the syntax of [HOL Light's `find_path` function](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/find%5Fpath.html).

In short, the string `lr` means we should take the left path in the syntax tree, whereas the string `r` means we should take the right. An empty string indicates we should consider the type of the whole output.

For example, given an output `A ** (B ++ C)` we can select any sub-term as follows:

| Sub-term        | Selector string |
|-----------------|-----------------|
| `A`             | lr              |
| `B`             | rlr             |
| `C`             | rr              |
| `B ++ C`        | r               |
| `A ** (B ++ C)` | (empty)         |

The **second/right** selector argument is used to select the input type of the second/right process that is expected to match our selected sub-term. This can help disambiguate between 2 inputs that are both able to receive the selected output type.


#### Example {#example}

As an example, the result `R` of the sequential composition of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `A` and `Y` and output `C` is the following process:

```ocaml
{name = "R";
 inputs = [(`X`, `cP_X_1`); (`Y`, `cQ_Y_2`)];
 output = (`C ++ (Y ** B)`, `c_R___R__y3`);
 prov =
   Provnode ("plus", Provleaf "Q",
             Provnode ("times", Provleaf "Q:cQ_Y_2", Provleaf "P"));
 proc = (* ... *);
 actions =
   [{Action.act = "JOIN"; larg = "P"; lsel = "lr"; rarg = "Q"; rsel = "A"; res = "R"}];
 copier = false;
 intermediate = true}
```

The action used can be noticed in the `actions` field above and is as follows:

```ocaml
{Action.act = "JOIN"; larg = "P"; lsel = "lr"; rarg = "Q"; rsel = "A"; res = "R"}
```


#### Notes {#notes}

There are many different possible cases of interesting sequential compositions and edge cases. Depending on their types there may also be multiple ways that two specific processes can be composed together sequentially.

In our experience, it is not easy or practical for the user to control the sequential composition in such a fine grained way. Instead, the reasoner uses a set of heuristics to make its own decisions based on 2 key goals:

1.  **Connect the 2 processes maximally**: The reasoner attempts to connect as many of the inputs resources of the receiving process as possible.
2.  **Minimize the execution steps in the final composition**: The reasoner aims to make as few reasoning steps as possible, minimize the number of resources that are _buffered_ (i.e. forwarded explicitly from one process to the next), and reduce repeating resources.

The first goal means that if the left process has output `A ** B ** C` and the right process has inputs `B` and `C`, then both of the two inputs will be connected to their respective parallel outputs irrespective of the user selection.

The second goal affects multiple decisions in the sequential composition.

One example is when the optional output of the left process is converted to an optional output with identical options, such as `Y ++ Y`. This might occur for example when a process that may fail to produce resource `Y` and throw an exception is composed with a contingency process that can recover from the exception and produce `Y` after all. The reasoner will attempt to collapse that output to a single `Y` output, whether that is the result of the original or of the contingency process. In fact, this will also reduce the reasoning steps and the size of the generated executable term, making it more efficient. It may also reduce the branching in subsequent compositions further down the line.

The tradeoff is that it is no longer possible to determine whether `Y` was produced from the original component or from the contingency process, which may be useful in some cases. The reasoner makes this decision under the assumption that if such differentiation is to be made between the produced `Y` resources, it should be reflected in the their respective types, instead of them having the same type `Y`.


## Actionstate {#actionstate}

Each composition action corresponds to a reasoning tactic implemented in HOL Light. These tactics require an extended proof state to function appropriately. This extension is captured using the `Actionstate` structure.

{{< tip >}}
The user is not required to manipulate the actionstate themselves, unless they perform low level proofs. However, the actionstate does appear as a result of a composition action and carries additional metadata.
{{< /tip >}}

The final actionstate resulting from a composition proof is provided within the reasoner's response, so it may be useful to explain its structure briefly here.

The `Actionstate` structure is [defined as follows](https://github.com/workflowfm/workflowfm-reasoner/blob/master/src/processes/actions.ml):

```ocaml
module Actionstate = struct
  type t = {
      label : string;
      ctr : int;
      metas : term list;
      merged : (term * string * string) list;
      iprov : (term * provtree) list;
      prov : (string * provtree) list;
    }

(* ... *)
end;;
```

The fields can be described briefly as follows:

| Field          | Description                                                                             |
|----------------|-----------------------------------------------------------------------------------------|
| `label`        | A unique name for the given composition, typically the name of the resulting process.   |
| `ctr`          | A unique counter for each reasoning step during composition.                            |
| `metas`        | A list of metavariables used during composition.                                        |
| `merged`       | A list of merged inputs during a conditional composition.                               |
| `iprov & prov` | [Provenance tracking]({{< relref "provenance" >}}) for inputs and outputs respectively. |

The unique name and counter are used to guarantee uniqueness of introduced channel names.

Merged inputs occur during [conditional composition](#with), when both processes have the same input type, so that the final composition does not duplicate inputs. Each entry consists of the input term as it appears in the composition paired with the names of the 2 input channels that got merged.
