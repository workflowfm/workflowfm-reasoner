---
title: "Commands"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:05+01:00
draft: false
weight: 320
---

This section covers the main process specification and composition commands.

It is worth noting that the result of these commands is of type `Composer.Response`, which is [defined as follows](https://github.com/workflowfm/workflowfm-reasoner/blob/master/src/api/composer.ml):

```ocaml
module Response :
  sig
    type t =
      | Ping of float
      | Create of Process.t
      | Compose of Process.t * Action.t * Actionstate.t
      | Verify of Process.t
      | Deploy of string * (string * string * bool) list
      | Failed of string
      | Exception of string
    (*...*)
  end
```

Upon failure a `Failed` or an `Exception` response will be issued with an associated message describing the failure. Otherwise, one of the other responses will be returned, as explained in the normal operation of each command below.


## create {#create}

The `create` command constructs a new atomic process given the types of its desired inputs and output.

It takes 3 arguments:

1.  `string`: The name of the process.
2.  `term list`: The list of types of its inputs.
3.  `term`: The type of its output.

All terms are expected to be [resources](../../elements/resources/) involving HOL Light propositions and the operators `++` and `**` operators. No negative operators (`NEG`, `&`, `%`) should be used, including in the input types.

The command returns a `Create` response with the specification of the created process.


#### Notes {#notes}

-   Terms in HOL Light must be surrounded by back-ticks `` ` ``.
-   If a process with the same name already exists, a warning will be shown and the old process will be replaced.
-   All the elements of the process other than its name and its types, including channel names, &pi;-calculus specification, and provenance are constructed automatically.


#### Example {#example}

The following invocation of `create` constructs a process named `"P"` with two inputs of types `X` and `Y++Z` respectively and an output of type `A**B**C`:

```ocaml
create "P" [`X`; `Y ++ Z`] `A ** B ** C`;;
```

```ocaml
Console.Composer.Response.Create
   {Console.Composer.Process.name = "P";
    inputs = [(`X`, `cP_X_1`); (`Y ++ Z`, `cP_lB_Y_Plus_Z_rB_2`)];
    output = (`A ** B ** C`, `oP_lB_A_x_lB_B_x_C_rB_rB_`);
    prov =
     Provnode ("times", Provleaf "P",
      Provnode ("times", Provleaf "P", Provleaf "P"));
    proc =
     `P (cP_X_1,cP_lB_Y_Plus_Z_rB_2,oP_lB_A_x_lB_B_x_C_rB_rB_) =
      Comp (In cP_X_1 [cP_X_1__a_X] Zero)
      (Comp
       (Res [cP_lB_Y_Plus_Z_rB_2__opt_Y; cP_lB_Y_Plus_Z_rB_2__opt_Z]
       (Out cP_lB_Y_Plus_Z_rB_2
        [cP_lB_Y_Plus_Z_rB_2__opt_Y; cP_lB_Y_Plus_Z_rB_2__opt_Z]
       (Plus
        (In cP_lB_Y_Plus_Z_rB_2__opt_Y [cP_lB_Y_Plus_Z_rB_2_Y]
        (In cP_lB_Y_Plus_Z_rB_2_Y [cP_lB_Y_Plus_Z_rB_2_l_a_Y] Zero))
       (In cP_lB_Y_Plus_Z_rB_2__opt_Z [cP_lB_Y_Plus_Z_rB_2_Z]
       (In cP_lB_Y_Plus_Z_rB_2_Z [cP_lB_Y_Plus_Z_rB_2_r_a_Z] Zero)))))
      (Res
       [oP_lB_A_x_lB_B_x_C_rB_rB__A; oP_lB_A_x_lB_B_x_C_rB_rB__lB_B_x_C_rB]
      (Out oP_lB_A_x_lB_B_x_C_rB_rB_
       [oP_lB_A_x_lB_B_x_C_rB_rB__A; oP_lB_A_x_lB_B_x_C_rB_rB__lB_B_x_C_rB]
      (Comp
       (Res [oP_lB_A_x_lB_B_x_C_rB_rB__l_a_A]
       (Out oP_lB_A_x_lB_B_x_C_rB_rB__A [oP_lB_A_x_lB_B_x_C_rB_rB__l_a_A]
       Zero))
      (Res [oP_lB_A_x_lB_B_x_C_rB_rB__rB; oP_lB_A_x_lB_B_x_C_rB_rB__rC]
      (Out oP_lB_A_x_lB_B_x_C_rB_rB__lB_B_x_C_rB
       [oP_lB_A_x_lB_B_x_C_rB_rB__rB; oP_lB_A_x_lB_B_x_C_rB_rB__rC]
      (Comp
       (Res [oP_lB_A_x_lB_B_x_C_rB_rB__rl_a_B]
       (Out oP_lB_A_x_lB_B_x_C_rB_rB__rB [oP_lB_A_x_lB_B_x_C_rB_rB__rl_a_B]
       Zero))
      (Res [oP_lB_A_x_lB_B_x_C_rB_rB__rr_a_C]
      (Out oP_lB_A_x_lB_B_x_C_rB_rB__rC [oP_lB_A_x_lB_B_x_C_rB_rB__rr_a_C]
      Zero)))))))))`;
    actions = []; copier = false; intermediate = false}
```


## tensor {#tensor}

The `tensor` command composes two processes in parallel with the [`TENSOR` action](../../elements/composition/#tensor).

It takes 2 arguments:

1.  `string`: The name of the first process to compose.
2.  `string`: The name of the second process to compose.

The command returns a `Compose` response with the specification of the created intermediate composition, the composition action that was applied, and the [resulting actionstate](../../elements/composition/#actionstate) with additional metadata.


#### Notes {#notes}

-   The name of the resulting intermediate composition is automatically determined using the `"_Step"` prefix and an internal [step counter]({{< relref "state#step" >}}).


#### Example {#example}

The following invocation of `tensor` performs the parallel composition `_Step0` of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `Y` and `Z` and output `C`:

```ocaml
create "P" [`X`] `A ++ B` ;;
create "Q" [`Y`; `Z`] `C` ;;
tensor "P" "Q" ;;
```

```ocaml
Console.Composer.Response.Compose
 ({Console.Composer.Process.name = "_Step0";
   inputs = [(`X`, `cP_X_1`); (`Y`, `cQ_Y_1`); (`Z`, `cQ_Z_2`)];
   output = (`(A ++ B) ** C`, `c_Step0___Step0__z1`);
   prov =
    Provnode ("times", Provnode ("plus", Provleaf "P", Provleaf "P"),
     Provleaf "Q");
   proc =
    `_Step0 (cP_X_1,cQ_Y_1,cQ_Z_2,c_Step0___Step0__z1) =
     PiTimesProc (A ++ B) C c_Step0___Step0__z1 oP_lB_A_Plus_B_rB_ oQ_C_
     (P (cP_X_1,oP_lB_A_Plus_B_rB_))
     (Q (cQ_Y_1,cQ_Z_2,oQ_C_))`;
   actions =
    [{Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = "";
      res = "_Step0"}];
   copier = false; intermediate = true},
 {Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = "";
  res = "_Step0"},
 {Actionstate.label = "_Step0"; ctr = 0;
  metas =
   [`c_Step0___Step0__z1`; `c_Step0___Step0__y1`; `c_Step0___Step0__Q1`;
    `cQ_Y_1`; `cQ_Z_2`; `oQ_C_`; `cP_X_1`; `oP_lB_A_Plus_B_rB_`];
  merged = []; iprov = [];
  prov =
   [("_Step0",
     Provnode ("times", Provnode ("plus", Provleaf "P", Provleaf "P"),
      Provleaf "Q"));
    ("P", Provnode ("plus", Provleaf "P", Provleaf "P"));
    ("Q", Provleaf "Q")]})
```


## cwith {#with}

The `cwith` command composes two processes conditionally with the [`WITH` action](../../elements/composition/#with).

It takes 4 arguments:

1.  `string`: The name of the first process to compose.
2.  `string`: The type of the input to use from the first process.
3.  `string`: The name of the second process to compose.
4.  `string`: The type of the input to use from the second process.

The command returns a `Compose` response with the specification of the created intermediate composition, the composition action that was applied, and the [resulting actionstate](../../elements/composition/#actionstate) with additional metadata.


#### Notes {#notes}

-   The name of the resulting intermediate composition is automatically determined using the `"_Step"` prefix and an internal [step counter]({{< relref "state#step" >}}).
-   The types of the selected inputs need to be provided as **strings** and not as terms.


#### Example {#example}

The following invocation of `cwith` performs the conditional composition `_Step0` of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `Y` and `Z` and output `C` with inputs `X` and `Y` selected:

```ocaml
create "P" [`X`] `A ++ B` ;;
create "Q" [`Y`; `Z`] `C` ;;
cwith "P" "X" "Q" "Y" ;;
```

```ocaml
Console.Composer.Response.Compose
 ({Console.Composer.Process.name = "_Step0";
   inputs = [(`Z`, `cQ_Z_2`); (`X ++ Y`, `c_Step0___Step0__x3`)];
   output = (`((A ++ B) ** Z) ++ C`, `c_Step0___Step0__y3`);
   prov =
    Provnode ("plus",
     Provnode ("times",
      Provnode ("plus", Provleaf "&_Step0", Provleaf "&_Step0"),
      Provleaf "&_Step0"),
     Provleaf "&_Step0");
   proc =
    `_Step0 (cQ_Z_2,c_Step0___Step0__x3,c_Step0___Step0__y3) =
     PiWithProc (NEG X) (NEG Y) c_Step0___Step0__x3 cP_X_1 cQ_Y_1
     c_Step0___Step0__uI3
     c_Step0___Step0__vI3
     (PiPlusLProc ((A ++ B) ** Z) C c_Step0___Step0__y3 c_Step0___Step0__z1
      c_Step0___Step0__uR3
      c_Step0___Step0__vR3
     (PiTimesProc (A ++ B) Z c_Step0___Step0__z1 oP_lB_A_Plus_B_rB_
      c_Step0___Step0__y1
      (P (cP_X_1,oP_lB_A_Plus_B_rB_))
     (PiIdProc Z cQ_Z_2 c_Step0___Step0__y1 c_Step0___Step0__m2)))
     (PiPlusRProc ((A ++ B) ** Z) C c_Step0___Step0__y3 oQ_C_
      c_Step0___Step0__uE3
      c_Step0___Step0__vE3
     (Q (cQ_Y_1,cQ_Z_2,oQ_C_)))`;
   actions =
    [{Action.act = "WITH"; larg = "P"; lsel = "X"; rarg = "Q"; rsel = "Y";
      res = "_Step0"}];
   copier = false; intermediate = true},
 {Action.act = "WITH"; larg = "P"; lsel = "X"; rarg = "Q"; rsel = "Y";
  res = "_Step0"},
 {Actionstate.label = "_Step0"; ctr = 0;
  metas =
   [`c_Step0___Step0__x3`; `c_Step0___Step0__uI3`; `c_Step0___Step0__vI3`;
    `c_Step0___Step0__uR3`; `c_Step0___Step0__vR3`; `c_Step0___Step0__y3`;
    `c_Step0___Step0__d3`; `c_Step0___Step0__uE3`; `c_Step0___Step0__vE3`;
    `c_Step0___Step0__Q3`; `c_Step0___Step0__m2`; `c_Step0___Step0__z1`;
    `c_Step0___Step0__y1`; `c_Step0___Step0__Q1`; `cQ_Y_1`; `cQ_Z_2`;
    `oQ_C_`; `cP_X_1`; `oP_lB_A_Plus_B_rB_`];
  merged = [(`NEG (X ++ Y) <> c_Step0___Step0__x3`, "cP_X_1", "cQ_Y_1")];
  iprov = [];
  prov =
   [("_Step0",
     Provnode ("plus",
      Provnode ("times",
       Provnode ("plus", Provleaf "&_Step0", Provleaf "&_Step0"),
       Provleaf "&_Step0"),
      Provleaf "&_Step0"));
    ("P", Provnode ("plus", Provleaf "P", Provleaf "P"));
    ("Q", Provleaf "Q")]})
```


## join {#join}

The `join` command composes two processes in sequence with the [`JOIN` action](../../elements/composition/#join).

It takes 4 arguments:

1.  `string`: The name of the first process to compose.
2.  `string`: The path to a sub-term of the output of the first process.
3.  `string`: The name of the second process to compose.
4.  `string`: The type of the input to use from the second process.

The command returns a `Compose` response with the specification of the created intermediate composition, the composition action that was applied, and the [resulting actionstate](../../elements/composition/#actionstate) with additional metadata.


#### Notes {#notes}

-   The name of the resulting intermediate composition is automatically determined using the `"_Step"` prefix and an internal [step counter]({{< relref "state#step" >}}).
-   The path to a sub-type of the output of the first process must follow the syntax of [HOL Light's `find_path` function](https://www.cl.cam.ac.uk/~jrh13/hol-light/HTML/find%5Fpath.html).
-   The types of the selected input need to be provided as a **string** and not as a term.


#### Example {#example}

The following invocation of `join` performs the sequential composition `_Step0` of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `A` and `Y` and output `C`:

```ocaml
create "P" [`X`] `A ++ B` ;;
create "Q" [`A`; `Z`] `C` ;;
join "P" "lr" "Q" "A" ;;
```

```ocaml
Console.Composer.Response.Compose
 ({Console.Composer.Process.name = "_Step0";
   inputs = [(`X`, `cP_X_1`); (`Z`, `cQ_Z_2`)];
   output = (`C ++ (Z ** B)`, `c_Step0___Step0__y3`);
   prov =
    Provnode ("plus", Provleaf "Q",
     Provnode ("times", Provleaf "Q:cQ_Z_2", Provleaf "P"));
   proc =
    `_Step0 (cP_X_1,cQ_Z_2,c_Step0___Step0__y3) =
     PiCutProc (A ++ B) c_Step0___Step0__z7 c_Step0___Step0__x3
     oP_lB_A_Plus_B_rB_
     (PiWithProc (NEG A) (NEG B) c_Step0___Step0__x3 cQ_A_1
      c_Step0___Step0__c3
      c_Step0___Step0__uI3
      c_Step0___Step0__vI3
      (PiPlusLProc C (Z ** B) c_Step0___Step0__y3 oQ_C_
       c_Step0___Step0__uR3
       c_Step0___Step0__vR3
      (Q (cQ_A_1,cQ_Z_2,oQ_C_)))
     (PiPlusRProc C (Z ** B) c_Step0___Step0__y3 c_Step0___Step0__d3
      c_Step0___Step0__uE3
      c_Step0___Step0__vE3
     (PiTimesProc Z B c_Step0___Step0__d3 c_Step0___Step0__x4
      c_Step0___Step0__y4
      (PiIdProc Z cQ_Z_2 c_Step0___Step0__x4 c_Step0___Step0__m5)
     (PiIdProc B c_Step0___Step0__c3 c_Step0___Step0__y4
     c_Step0___Step0__m6))))
     (P (cP_X_1,oP_lB_A_Plus_B_rB_))`;
   actions =
    [{Action.act = "JOIN"; larg = "P"; lsel = "lr"; rarg = "Q"; rsel = "A";
      res = "_Step0"}];
   copier = false; intermediate = true},
 {Action.act = "JOIN"; larg = "P"; lsel = "lr"; rarg = "Q"; rsel = "A";
  res = "_Step0"},
 {Actionstate.label = "_Step0"; ctr = 0;
  metas =
   [`c_Step0___Step0__z7`; `c_Step0___Step0__y7`; `c_Step0___Step0__Q7`;
    `c_Step0___Step0__m6`; `c_Step0___Step0__m5`; `c_Step0___Step0__x4`;
    `c_Step0___Step0__y4`; `c_Step0___Step0__P4`; `c_Step0___Step0__Q4`;
    `c_Step0___Step0__x3`; `c_Step0___Step0__c3`; `c_Step0___Step0__uI3`;
    `c_Step0___Step0__vI3`; `c_Step0___Step0__uR3`; `c_Step0___Step0__vR3`;
    `c_Step0___Step0__y3`; `c_Step0___Step0__d3`; `c_Step0___Step0__uE3`;
    `c_Step0___Step0__vE3`; `c_Step0___Step0__Q3`; `cQ_A_1`; `cQ_Z_2`;
    `oQ_C_`; `cP_X_1`; `oP_lB_A_Plus_B_rB_`];
  merged = [];
  iprov =
   [(`A ++ B`, Provnode ("plus", Provleaf "cQ_A_1:1", Provleaf "#"))];
  prov =
   [("Q", Provleaf "Q");
    ("_Step0",
     Provnode ("plus", Provleaf "Q",
      Provnode ("times", Provleaf "Q:cQ_Z_2", Provleaf "P")));
    ("P", Provnode ("plus", Provleaf "P", Provleaf "P"))]})
```


## compose1 {#compose1}

The `compose1` command composes two processes with an explicit [composition action](../../elements/composition/#actions).

It takes 1 argument:

1.  `Action.t`: The composition action to perform.

This command is intended for advanced usage, for instance with a custom action, or some other action parameter not handled by the other commands.

The command returns a `Compose` response with the specification of the created intermediate composition, the composition action that was applied, and the [resulting actionstate](../../elements/composition/#actionstate) with additional metadata.


#### Notes {#notes}

-   If an intermediate composition with the same name as the action's result already exists, a warning will be shown and the old process will be replaced.


#### Example {#example}

The following invocation of `compose1` performs the parallel composition `R` of a process `P` with input `X` and output `A ++ B` and a process `Q` with inputs `Y` and `Z` and output `C`:

```ocaml
create "P" [`X`] `A ++ B` ;;
create "Q" [`Y`; `Z`] `C` ;;
compose1 {Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = ""; res = "R"} ;;
```

```ocaml
Console.Composer.Response.Compose
 ({Console.Composer.Process.name = "R";
   inputs = [(`X`, `cP_X_1`); (`Y`, `cQ_Y_1`); (`Z`, `cQ_Z_2`)];
   output = (`(A ++ B) ** C`, `cR__R__z1`);
   prov =
    Provnode ("times", Provnode ("plus", Provleaf "P", Provleaf "P"),
     Provleaf "Q");
   proc =
    `R (cP_X_1,cQ_Y_1,cQ_Z_2,cR__R__z1) =
     PiTimesProc (A ++ B) C cR__R__z1 oP_lB_A_Plus_B_rB_ oQ_C_
     (P (cP_X_1,oP_lB_A_Plus_B_rB_))
     (Q (cQ_Y_1,cQ_Z_2,oQ_C_))`;
   actions =
    [{Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = "";
      res = "R"}];
   copier = false; intermediate = true},
 {Action.act = "TENSOR"; larg = "P"; lsel = ""; rarg = "Q"; rsel = "";
  res = "R"},
 {Actionstate.label = "R"; ctr = 0;
  metas =
   [`cR__R__z1`; `cR__R__y1`; `cR__R__Q1`; `cQ_Y_1`; `cQ_Z_2`; `oQ_C_`;
    `cP_X_1`; `oP_lB_A_Plus_B_rB_`];
  merged = []; iprov = [];
  prov =
   [("R",
     Provnode ("times", Provnode ("plus", Provleaf "P", Provleaf "P"),
      Provleaf "Q"));
    ("P", Provnode ("plus", Provleaf "P", Provleaf "P"));
    ("Q", Provleaf "Q")]})
```
