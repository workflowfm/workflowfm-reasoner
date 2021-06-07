---
title: "Responses"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-07T15:16:57+01:00
draft: false
weight: 430
---

JSON responses are provided in standard output, wrapped between a line containing the string `JSON_START` and a line containing the string `JSON_END`. HOL Light will also yield additional output outside those 2 lines.

You can therefore parse JSON output using a regular expression of the form `"JSON_START(.*?)JSON_END"`.

{{< tip >}}
All responses include a `response` field of type `string` which defines the type of the response.
{{< /tip >}}


## Pong {#PongResponse}

**Description**:

The response to the [`Ping`]({{< relref "commands#PingCommand" >}}) command.

**Structure**:

-   `response`: `string` = `"Pong"`
-   `ping`: `float` = contains the original timestamp received by the prover in the [`Ping`]({{< relref "commands#PingCommand" >}}) command.


## Create {#create}

**Description**:

The response to the [`create`]({{< relref "commands#CreateCommand" >}}) command with a definition of a new atomic process.

**Structure**:

-   `response`: `string` = `"CreateProcess"`
-   `process`: [`process`]({{< relref "types#process" >}}) = the newly created process


## Compose {#ComposeResponse}

**Description**:

The result of a single binary composition action. The [`compose`]({{< relref "commands#ComposeCommand" >}}) command may produce multiple of these, one for each action.

**Structure**:

-   `response`: `string` = `"Compose"`
-   `action`: [`action`]({{< relref "types#action" >}}) = the composition action that was applied
-   `process`: [`process`]({{< relref "types#process" >}}) = the resulting composite process
-   `state`: [`actionstate`]({{< relref "types#actionstate" >}}) = the updated action state with the associated metadata


## Verify {#VerifyResponse}

**Description**:

The response of the [`verify`]({{< relref "commands#VerifyCommand" >}}) command with a reconstructed composite process.

**Structure**:

-   `response`: `string` = `"Verify"`
-   `process`: [`process`]({{< relref "types#process" >}}) = the reconstructed composition


## Deploy {##DeployResponse}

**Description**:

This is the response to the [`deploy`]({{< relref "commands#DeployCommand" >}}) commands. It describes the files that are required for deployment.

**Structure**:

First we need the structure for a single deployment file. This is a `file` object containing the following fields:

-   `path`: `string` = the full path of the file (including its name) in the deployment
-   `content`: `string` = the content of the file
-   `overwrite`: `bool` = the reasoner tags the files that are generated fully automatically so that they will be overwritten in consecutive deployments. Files that may be edited by the user (e.g. code templates) have this field marked as `false` to avoid overwritting user content.

Based on this, the `deploy` response is as follows:

-   `response`: `string` = `"Deploy"`
-   `type`: `string` = the type of deployment. Currently one of `PiViz`, `PiLib` or `PEW`.
-   `deployment`: `Array` of `file` = a list of deployment files.


## Failed {#failed}

**Description**:

This response is generated whenever the prover fails to perform a command. Unless there is a bug or associated limitation in the prover, this indicates a user or input error.

**Structure**:

-   `response`: `string` = `"CommandFailed"`
-   `content`: `string` = a (sometimes useful) description of the error that occured


## Exception {#exception}

**Description**:

This response is generated whenever the prover fails due to an internal exception. This indicates an expected failure in the system.

**Structure**:

-   `response`: `string` = `"Exception"`
-   `content`: `string` = the contents of the thrown exception
