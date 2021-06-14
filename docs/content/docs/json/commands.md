---
title: "Commands"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:20+01:00
draft: false
weight: 420
---

JSON commands can be issued to the WorkflowFM Reasoner using the following function:

```ocaml
Json_composer_io.execute "JSON";;
```

Replace `JSON` with one of the commands described below, in JSON format.

You can also execute a JSON command stored in a file as follows:

```ocaml
Json_composer_io.execute_file "path/to/file.json";;
```

{{< tip >}}
All commands include a `command` field of type `string` which defines the type of the command.
{{< /tip >}}


## Ping {#PingCommand}


#### Description: {#description}

Ping/keep-alive command. Gives a [`Pong`]({{< relref "responses#PongResponse" >}}) response.


#### Structure: {#structure}

-   `command`: `string` = `"ping"`
-   `ping`: `float` = a timestamp to measure ping


## Create {#CreateCommand}


#### Description: {#description}

A command to create a new atomic process.


#### Structure: {#structure}

-   `command`: `string` = `"create"`
-   `name`: `string` = the name of the process to be created
-   `inputs`: `array` of [`linprop`]({{< relref "types#linprop" >}}) = a list of inputs. Their channels will be created by the prover.
-   `output`: [`linprop`]({{< relref "types#linprop" >}}) = the process output. The channcel will be created by the prover.


## Binary compose (compose1) {#Compose1Command}


#### Description: {#description}

Binary composition of 2 processes with a single action.

Although a more general [composition command](#ComposeCommand) is provided, when it comes to simple binary compositions this command executes faster.


#### Structure: {#structure}

-   `command`: `string` = `"compose1"`
-   `action`: [`action`]({{< relref "types#action" >}}) = the composition action to be performed. The labels of the 2 arguments must match the labels of the processes provided in the next fields.
-   `lhs`: [`process`]({{< relref "types#process" >}}) = the process corresponding to the first (left) argument of the action
-   `rhs`: [`process`]({{< relref "types#process" >}}) = the process corresponding to the second (right) argument of the action


## Compose {#ComposeCommand}


#### Description: {#description}

Construction of a complex composition with one or more actions. Although more general than the binary composition command [`compose1`](#Compose1Command), it is slower.


#### Structure: {#structure}

-   `command`: `string` = `"compose"`
-   `name`: `string` = the name of the final composition
-   `components`: `array` of [`process`]({{< relref "types#process" >}}) = the list of all component processes that will be used
-   `actions`: `array` of [`action`]({{< relref "types#action" >}}) = the ordered list of actions to be performed


## Verify {#VerifyCommand}


#### Description: {#description}

A command used to reconstruct a process composition.

This is legacy command which has now devolved into the [`compose`](#ComposeCommand) command. The only difference is that `verify` does not produce [`compose`]({{< relref "responses#ComposeResponse" >}}) responses for intermediate steps. It will only generate one [`verify`]({{< relref "responses#VerifyResponse" >}}) response for the final process.


#### Structure: {#structure}

-   `command`: `string` = `"verify"`
-   `name`: `string` = the name of the final composition
-   `components`: `array` of [`process`]({{< relref "types#process" >}}) = the list of all component processes that will be used
-   `actions`: `array` of [`action`]({{< relref "types#action" >}}) = the ordered list of actions to be performed


## Deploy {#DeployCommand}


#### Description: {#description}

This is a family of commands that produce executable process deployments.

There are currently 3 types of possible deployments:

1.  `PiViz`: This produces a file for the PiVizTool and/or MWB.
2.  `PiLib`: This produces a deployment and code templates using the old PiLib library.
3.  `PEW`: This produces a deployment and code templates with the newer [PEW library](https://github.com/workflowfm/pew).


#### Structure: {#structure}


#### `PiViz` {#piviz}

-   `command`: `string` = `"piviz"`
-   `process`: [`process`]({{< relref "types#process" >}}) = the process to be deployed
-   `components`: `array` of [`process`]({{< relref "types#process" >}}) = the list of all dependencies/components required in the composition


#### `PiLib` {#pilib}

-   `command`: `string` = `"pilib"`
-   `process`: [`process`]({{< relref "types#process" >}}) = the process to be deployed
-   `components`: `array` of [`process`]({{< relref "types#process" >}}) = the list of all dependencies/components required in the composition
-   `separator`: `string` = the client OS-specific file path separator
-   `path`: `string` = the base path for the deployment
-   `pkg`: `string` = the desired name for the Scala package that will contain the code
-   `project`: `string` = an identifiable name for the deployment. This will be used to identify certain types and classes.
-   `main`: `bool` = `true` if the generation of a template for a main class is required.
-   `java`: `bool` = `true` if the generation of a java runner class is required. This can help integrate the Scala deployment with Java code.


#### `PEW` {#pew}

-   `command`: `string` = `"piviz"`
-   `process`: [`process`]({{< relref "types#process" >}}) = the process to be deployed
-   `components`: `array` of [`process`]({{< relref "types#process" >}}) = the list of all dependencies/components required in the composition
-   `separator`: `string` = the client OS-specific file path separator
-   `path`: `string` = the base path for the deployment
-   `pkg`: `string` = the desired name for the Scala package that will contain the code
-   `project`: `string` = an identifiable name for the deployment. This will be used to identify certain types and classes.
-   `main`: `bool` = `true` if the generation of a template for a main class is required.
-   `java`: `bool` = `true` if the generation of a java runner class is required. This can help integrate the Scala deployment with Java code.
