---
title: "Install HOL Light"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:25:26+01:00
draft: false
weight: 120
---

You can install HOL Light by following its [standard installation instructions](https://github.com/jrh13/hol-light/blob/master/READM).

We have included our own notes below in case they are helpful.

{{< tip >}}
Specific tips for DICE users at the University of Edinburgh are included below.
{{< /tip >}}


## Install OCaml {#install-ocaml}

OCaml 4.07.0 minimum is required. The easiest way to install this is through [opam](http://opam.ocaml.org/).

{{< tip >}}
On DICE, opam can be compiled from source and installed locally. It is better to use a locally installed OCaml than the centrally available one.
{{< /tip >}}

You also need to install the \`num\` and \`camlp5\` packages:

```sh
opam install num camlp5
```

In many cases (including on DICE) the toplevel loads `camlp4`. In order to load `camlp5` by default, you need to edit the `.ocamlinit` file in your home directory (opam usually creates one, otherwise add it yourself). Add the following to that file:

```ocaml
#use "topfind";;
#require "camlp5";;
#load "camlp5o.cma";;
```

Running `ocaml` should give you a `Camlp5 parsing version ...` at the end.


## Run HOL Light {#run-hol-light}

To install/run HOL Light, first create the `pa_j.ml` file:

```sh
make
```

The run `ocaml` and load HOL Light:

```ocaml
#use "hol.ml";;
```


## Checkpointing {#checkpointing}

Checkpointing eliminates loading times, which are otherwise relatively long, especially when you need to restart HOL Light during development.

We have been using [DMTCP](http://dmtcp.sourceforge.net/). Unfortunately, newer versions seem to be failing with HOL Light in a number of different platforms, but it is still worth trying.

{{< tip >}}
Version 2.0.0 and above does not seem to work on DICE. Try [version 1.2.4](https://sourceforge.net/projects/dmtcp/files/dmtcp/1.2.4/).
{{< /tip >}}

Once you have installed DMTCP, you can create the checkpoint as follows:

```sh
dmtcp_checkpoint ocaml
```

Then load HOL Light as usual:

```ocaml
#use "hol.ml";;
```

Wait for it to finish, then open a new terminal and checkpoint:

```sh
dmtcp_command -c
```

There is no notification when the checkpoint is complete other than the appearance of the `dmtcp_restart_script.sh` shortcut. You can then kill/exit OCaml.

Running `dmtcp_restart_script.sh` should load the checkpoint from where you left it. Issue a command to HOL Light/OCaml to make sure it works.

Subsequent uses of `dmtcp_command -c` will update your checkpoint.
