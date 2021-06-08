---
title: "Reference"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-08T00:15:28+01:00
draft: false
menu:
  main:
    identifier: "reference"
    weight: 100
---

Welcome to the **WorkflowFM Reasoner documentation**. This is a [HOL Light](https://github.com/jrh13/hol-light) library that allows for rigorous, formally verified process specification and composition. Processes can be specified based on the types of their input and output resources, using Classical [Linear Logic](https://en.wikipedia.org/wiki/Linear%5Flogic) (CLL) sequents. Composition can then be achieved using forward chaining/inference of CLL rules.

Inference can be applied directly using the standard HOL Light interactive proof setting and the [embed library](https://github.com/PetrosPapapa/hol-light-embed). Alternatively, the WorkflowFM Reasoner also provides its own interface with intuitive commands that greatly facilitate process specification and composition.

CLL proofs are annotated with [&pi;-calculus](https://en.wikipedia.org/wiki/%CE%A0-calculus) process terms based on the [proofs-as-processes](https://www.sciencedirect.com/science/article/pii/0304397594001030) paradigm. These provide an executable translation of the logical composition. The resulting workflows are **correct-by-construction** with the following verified properties:

-   **Systematic resource accounting**: The linearity of CLL guarantees that no resources appear out of nowhere or disappear into thin air.
-   **Deadlock and livelock freedom**: The proofs-as-processes paradigm guarantees that the constructed workflows have no deadlocks or livelocks.
-   **Type checked composition**: Even though the generated &pi;-calculus term is untyped, the correctness of the types of all connected resources is ensured via the logical proof.
-   **Fully asynchronous and concurrent execution**: The &pi;-calculus naturally offers a workflow execution style where each component process can be executed fully asynchronously (see the [PEW engine](http://docs.workflowfm.com/pew) for more details) and concurrently, without introducing any conflicts, race conditions, or deadlocks.

The constructed workflows can be exported either for visualization using the [PiVizTool](http://frapu.de/bpm/piviztool.html) or as Scala code for execution using the [PEW engine](http://docs.workflowfm.com/pew).

{{< button "./install/" "Get started" >}}
