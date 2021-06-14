---
title: "Processes"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:25:44+01:00
draft: false
weight: 220
---

Processes are defined based on their input and outputs [resources]({{< relref "resources" >}}), as well as some additional metadata.

The [full process data structure](https://github.com/workflowfm/workflowfm-reasoner/blob/master/src/processes/processes.ml) is the following:

```ocaml
module type Process_type =
sig
  type t = {
    name : string;
    inputs : (term * term) list;
    output : term * term;
    prov : provtree;
    proc : term;
    actions : Action.t list;
    copier : bool;
    intermediate : bool;
  }
(* ... *)
end;;
```

Each process is assumed to have a unique name. Attempting to construct a composite process with the same name as one of its components will result in a failure.

{{< tip >}}
Resource type names need to follow the same naming restrictions as HOL Light variables, i.e. they need to start with a letter and contain only letters and numbers.
{{< /tip >}}

Here is an example atomic process `P` with 2 inputs, `X ++ Y` and `Z`, and an output of type `A ** B ** C` (or 3 parallel outputs of types `A`, `B`, and `C`):

```ocaml
{name = "P";
 inputs = [(`X ++ Y`, `cP_lB_X_Plus_Y_rB_1`); (`Z`, `cP_Z_2`)];
 output = (`A ** B ** C`, `oP_lB_A_x_lB_B_x_C_rB_rB_`);
 prov =
  Provnode ("times", Provleaf "P",
   Provnode ("times", Provleaf "P", Provleaf "P"));
 proc =
  `P (cP_lB_X_Plus_Y_rB_1,cP_Z_2,oP_lB_A_x_lB_B_x_C_rB_rB_) =
   Comp
   (Res [cP_lB_X_Plus_Y_rB_1__opt_X; cP_lB_X_Plus_Y_rB_1__opt_Y]
   (Out cP_lB_X_Plus_Y_rB_1
  (* ... *)
   ))`;
 actions = []; copier = false; intermediate = false}
```

We explain each of the fields next.


## Input / Output {#input-output}

Input and output resources are described as annotated terms (see [resources]({{< relref "resources" >}})). More specifically, each resource is a pair of terms `(term * term)`, the first one being the resource type and the second one the associated channel.

Channel names are generated automatically, yielding some fairly verbose names such as `oP_lB_A_x_lB_B_x_C_rB_rB_` seen in the example above.

{{< tip >}}
Each process can have **a list of input** resources and **a single, potentially composite output** resource.
{{< /tip >}}


## Provenance {#provenance}

The `prov` field captures the _output provenance_ for the process. See [Provenance]({{< relref "provenance" >}}) for more details.


## &pi;-calculus {#and-pi-calculus}

The `proc` field captures the &pi;-calculus process definition. This describes the process in an executable term of asynchronous communication through the available channels.

It involves a process definition as a function over the free channels, i.e. the channels involved in the inputs and outputs.

For atomic processes, the body of the definition is constructed automatically based on the input and output specification. It essentially provides a typechecked term for parallel reception of all the inputs and sending of the output.

For composite processes, the body of the definition is constructed via proof, with all the associated guarantees of correctness.


## Actions {#actions}

Composite processes include a list of [composition actions]({{< relref "composition#actions" >}}) that were used to construct them.

This allows us to reconstruct or revalidate these composite processes at any point, for instance after updating the specification of one of their components. It also allows us to reload all the intermediate steps of the composition to be able to construct different variations without going through all of the same steps.

Atomic processes have an empty list of actions.


## Copy Nodes {#copynodes}

Copier processes or _Copy Nodes_ are processes that represent the ability of a particular resource, such as an electronic document, to be copied.

We do not include exponentials in our linear logic formalisation, so this mechanism enables us to copy resources in an explicit way. If it is not actually possible to copy a resource (e.g. a physical resource or currency), then it will not be possible to provide a concrete implementation of the specification of the copier process.

More specifically, Copy Nodes are processes that receive a single input (e.g. `A`) and provide several copies of the same resource (e.g. `A ** A ** A`).

The `copier` field automatically identifies processes with a Copy Node specification.

This may also catch processes with a Copy Node specification but a different intended purpose (e.g. a process that splits a document in half and yields two different documents). At the logical level it is not possible to disambiguate between the two.

Nonetheless, Copy Nodes are not treated any differently than normal processes by the reasoner. This field is only a flag to facilitate the identification of processes with this type of specification. For instance, this is useful in our diagrammatic composer tool, where Copy Nodes are depicted with a special round symbol.


## Intermediate Processes {#intermediate}

Composite processes are differentiated into _intermediate_ and _stored_ processes.

Every time a composition action is performed between 2 processes, an _intermediate_ composite process is produced. Subsequent composition steps will produce further intermediate processes. Once a composition is completed, we _store_ the final process among the other atomic processes and completed compositions. The intermediate processes can then be deleted, to keep the list of available processes short.

As the size of the composed workflows increases, a large number of intermediate processes may be produced. Separating intermediate from stored processes enables better housekeeping and a smoother user interaction. Besides, the user has the option to store every single intermediate process produced if they so choose.

Other than managing the processes at the user level, the reasoner does not treat intermediate processes any differently than atomic or stored processes.
