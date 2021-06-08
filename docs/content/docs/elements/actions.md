---
title: "Actions"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-08T00:15:39+01:00
draft: false
weight: 220
---

Before we introduce process specifications, we need to discuss how composition is broken down into binary _actions_ and how _state_ is managed for each action.


## Actionstate {#actionstate}

Each composition action corresponds to a reasoning tactic implemented in HOL Light. These tactics require an extended proof state to function appropriately. This is extension is captured iusing the `Actionstate` structure.

{{< tip >}}
The user is not required to manipulate the actionstate themselves, unless they perform low level proofs.
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

| Field              | Description                                                                           |
|--------------------|---------------------------------------------------------------------------------------|
| `label`            | A unique name for the given composition, typically the name of the resulting process. |
| `ctr`              | A unique counter for each reasoning step during composition.                          |
| `metas`            | A list of metavariables used during composition.                                      |
| `merged`           | A list of merged inputs during a conditional composition.                             |
| `iprov` and `prov` | [Provenance tracking](../provenance) for inputs and outputs respectively.             |

The unique name and counter are used to guarantee uniqueness of introduced channel names.

Merged inputs occur during conditional composition, when both processes have the same input type, so that the final composition does not duplicate inputs. Each entry consists of the input term as it appears in the composition paired with the names of the 2 input channels that got merged.
