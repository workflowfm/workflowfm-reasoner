---
title: "Console"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:03+01:00
draft: false
weight: 300
---

This section covers the use of the reasoner through the console command interface running at the OCaml/HOL Light toplevel. This includes the available commands and responses.

The JSON API mode can be loaded using the following command:

```ocaml
loads (!hol_dir ^ "/workflowfm/make.console.ml");;
```

The entire interface is structured as the following module type:

```ocaml
module type Composer_console_type =
    sig
      module Composer : Composer_type

      val responses : unit -> Composer.Response.t list

      val add_process : Composer.Process.t -> Composer.Process.t
      val get_process : string -> Composer.Process.t
      val exists_process : string -> bool
      val del_process : string -> unit
      val reset_processes : unit -> unit
      val list : unit -> string list

      val add_intermediate : Composer.Process.t -> Composer.Process.t
      val get_intermediate : string -> Composer.Process.t
      val exists_intermediate : string -> bool
      val del_intermediate : string -> unit
      val reset_intermediates : unit -> unit
      val ilist : unit -> string list

      val get : string -> Composer.Process.t

      val resetstep : unit -> unit
      val reset : unit -> unit
      val full_reset : unit -> unit

      val create : string -> term list -> term -> Composer.Response.t
      val compose1 : Action.t -> Composer.Response.t
      val tensor : string -> string -> Composer.Response.t
      val cwith : string -> string -> string -> string -> Composer.Response.t
      val join : string -> string -> string -> string -> Composer.Response.t

      val store : string -> string -> Composer.Response.t
      val load : string -> unit
    end ;;
```

Each of these functions/commands is explained in more detail in the next sections.
