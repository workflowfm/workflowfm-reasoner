---
title: "State"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:04+01:00
draft: false
weight: 310
---

The console maintains an internal state of the introduced processes and compositions. This includes a list of atomic and stored processes and a separate list of intermediate processes. This allows the user to easily remove all intermediate processes when starting a new composition.


## General {#general}

The following commands are general purpose, spanning across the whole state:

| Command              | Result                                                                                                              |
|----------------------|---------------------------------------------------------------------------------------------------------------------|
| `get "P"`            | Returns the process named "P", whether it is atomic, intermediate or stored.                                        |
| `reset()`            | Resets intermediates and their [step counter](#step) in order to start a new composition.                           |
| `full_reset()`       | Resets the entire state in order to start a fresh session from scratch.                                             |
| `load "P"`           | Assuming a process named "P" is stored, the intermediate processes resulting from its composition steps are loaded. |
| `store "_Step4" "P"` | Assuming an intermediate process named "\_Step4" exists, it is stored as a new process named "P".                   |
| `responses()`        | Yields the history of all responses given by the reasoner in the current session.                                   |

{{< tip warning >}}
Commands that delete processes, such as `reset()` and `full_reset()` cannot be undone!
{{< /tip >}}


#### Notes: {#notes}

-   The `load` command performs a `reset()` first.


## Processes {#processes}

The list of atomic and stored processes can be managed with the following commands:

| Command              | Result                                        |
|----------------------|-----------------------------------------------|
| `add_process p`      | Adds a new process to the list.               |
| `get_process "P"`    | Retrieves the process named "P" if it exists. |
| `exists_process "P"` | Returns `true` if a process named "P" exists. |
| `del_process "P"`    | Deletes the process named "P" from the list.  |
| `reset_processes()`  | Resets the list by removing all processes.    |
| `list()`             | Returns a list of the names of all processes. |


#### Notes: {#notes}

-   It is easier to use [`create`]({{< relref "commands#create" >}}) rather than `add_process` so that the process specification is built automatically for you.
-   The commands `del_process` and `reset_processes` should be avoided or, at least, used carefully. There is a risk of reaching an inconsistent state where the components of a composition have been deleted.


## Intermediates {#intermediates}

The list of intermediate compositions can be managed with the following commands:

| Command                   | Result                                                      |
|---------------------------|-------------------------------------------------------------|
| `add_intermediate p`      | Adds a new intermediate process to the list.                |
| `get_intermediate "P"`    | Retrieves the intermediate process named "P" if it exists.  |
| `exists_intermediate "P"` | Returns `true` if an intermediate process named "P" exists. |
| `del_intermediate "P"`    | Deletes the intermediate process named "P" from the list.   |
| `reset_intermediates()`   | Resets the list by removing all intermediate processes.     |
| `ilist()`                 | Returns a list of the names of all intermediate processes.  |


#### Notes: {#notes}

-   It is easier to use the [composition commands]({{< relref "commands" >}}) rather than `add_intermediate` so that the process specifications are built automatically for you and mistakes are prevented.
-   The command `del_intermediate` should be avoided or, at least, used carefully. There is a risk of reaching an inconsistent state where the components of a composition have been deleted.
-   The use of the [`reset`](#general) command is suggested instead of `reset_intermediates`.


## Step counter {#step}

Fresh names can be automatically produced for intermediate processes using the prefix `"_Step"` and a _step counter_.

The command `resetstep()` can be used to reset the step counter. However, the use of the [`reset`](#general) command is suggested instead.
