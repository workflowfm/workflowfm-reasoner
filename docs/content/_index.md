---
title: "WorkflowFM Reasoner"
author: ["Petros Papapanagiotou"]
draft: false
---

[![img](https://img.shields.io/badge/version-{{< version >}}-brightgreen.svg)](https://github.com/workflowfm/workflowfm-reasoner/releases/latest) [![img](https://img.shields.io/badge/license-Apache%202.0-yellowgreen.svg)](https://opensource.org/licenses/Apache-2.0)

{{< tip >}}
A logic-based library for correct-by-construction process modelling and composition.
{{< /tip >}}

{{< button "docs/" "Read the Docs" >}}{{< button "https://github.com/workflowfm/workflowfm-reasoner" "Source" >}}

## About

This is a [HOL Light](https://github.com/jrh13/hol-light) library that allows for rigorous, formally verified process specification and composition. Processes can be specified based on the types of their input and output resources, using Classical [Linear Logic](https://en.wikipedia.org/wiki/Linear_logic) (CLL) sequents. Composition can then be achieved using forward chaining/inference of CLL rules.

Inference can be applied directly using the standard HOL Light interactive proof setting and the [embed library](https://github.com/PetrosPapapa/hol-light-embed). Alternatively, the WorkflowFM Reasoner also provides its own interface with intuitive commands that greatly facilitate process specification and composition.

CLL proofs are annotated with [&pi;-calculus](https://en.wikipedia.org/wiki/%CE%A0-calculus) process terms based on the [proofs-as-processes](https://www.sciencedirect.com/science/article/pii/0304397594001030) paradigm. These provide an executable translation of the logical composition. The resulting workflows are **correct-by-construction** with the following verified properties:

-   **Systematic resource accounting**: The linearity of CLL guarantees that no resources appear out of nowhere or disappear into thin air.
-   **Deadlock and livelock freedom**: The proofs-as-processes paradigm guarantees that the constructed workflows have no deadlocks or livelocks.
-   **Type checked composition**: Even though the generated &pi;-calculus term is untyped, the correctness of the types of all connected resources is ensured via the logical proof.
-   **Fully asynchronous and concurrent execution**: The &pi;-calculus naturally offers a workflow execution style where each component process can be executed fully asynchronously (see the [PEW engine](http://docs.workflowfm.com/pew) for more details) and concurrently, without introducing any conflicts, race conditions, or deadlocks.

The constructed workflows can be exported either for visualization using the [PiVizTool](http://frapu.de/bpm/piviztool.html) or as Scala code for execution using the [PEW engine](http://docs.workflowfm.com/pew).

The [references](#references) provide more in depth details of the theory behind the WorkflowFM Reasoner.


### Key Features

-   Process specification using Classical Linear Logic (CLL).
-   Process composition using formally verified forward inference.
-   Interactive theorem proving in CLL.
-   Intuitive high-level actions for sequential, conditional, and parallel composition.
-   Proof translation to [&pi;-calculus](https://en.wikipedia.org/wiki/%CE%A0-calculus).
-   Modular encoding allows different CLL translations (e.g. to session types), automatically reconstructing the entire process reasoning framework.
-   Tracking of [provenance metadata](./docs/provenance.md) during proof to guide visualization.
-   Export &pi;-calculus to [PiVizTool](http://frapu.de/bpm/piviztool.html) format.
-   Export Scala code to execute workflows using the [PEW engine](http://docs.workflowfm.com/pew).
-   Modular API allows extensions with new composition actions, export options and commands.


### Modes

The reasoner can run in 2 modes:

-   **Console**: This mode is intended for standard use within HOL Light, i.e. at the OCaml toplevel. It provides a minimal console interface for process modelling and composition.
-   **JSON**: This mode is intended for use within a server environment, to allow interaction with web applications (including UIs). It expects input and produces output encoded in [JSON](https://en.wikipedia.org/wiki/JSON) format.


<a id="authors"></a>

## Authors


### Maintainer

[Petros Papapanagiotou](https://github.com/PetrosPapapa) - [{{< image "images/web.svg" "Home page" "icon nomargin">}}](https://homepages.inf.ed.ac.uk/ppapapan/) - [{{< image "images/email.svg" "Email" "icon nomargin">}}](mailto:petros@workflowfm.com?subject=WorkflowFM%20Reasoner) - [{{< image "images/twitter.svg" "Twitter" "icon nomargin">}}](https://twitter.com/petrospapapa)


### Contributors

A big thank you to the following contributors in order of appearance:

-   Jacques Fleuriot - [{{< image "images/web.svg" "Home page" "icon nomargin">}}](https://homepages.inf.ed.ac.uk/jdf/)


### Groups & Organizations


<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">
<tbody>
<tr>
<td class="org-left"><a href="https://aiml.inf.ed.ac.uk/">Artificial Intelligence Modelling Lab</a></td>
</tr>


<tr>
<td class="org-left"><a href="https://web.inf.ed.ac.uk/aiai">Artificial Intelligence and its Applications Institute</a></td>
</tr>


<tr>
<td class="org-left"><a href="https://www.ed.ac.uk/informatics/">School of Informatics, University of Edinburgh</a></td>
</tr>
</tbody>
</table>


<a id="references"></a>

## References

Please cite the following publication in reference to this project:

-   P. Papapanagiotou, J. Fleuriot. [WorkflowFM: A Logic-Based Framework for Formal Process Specification and Composition](https://link.springer.com/chapter/10.1007/978-3-319-63046-5%5F22). CADE, 2017.

Sample of other relevant references:

-   P. Papapanagiotou, J. Fleuriot. [Formal Verification of Web Services Composition Using Linear Logic and the pi-calculus](https://ieeexplore.ieee.org/document/6061099). ECOWS, 2011.
-   P. Papapanagiotou. [A formal verification approach to process modelling and composition](https://era.ed.ac.uk/handle/1842/17863). PhD Thesis, 2014.
-   P. Papapanagiotou, J. Fleuriot. [A Pragmatic, Scalable Approach to Correct-by-construction Process Composition Using Classical Linear Logic Inference](https://link.springer.com/chapter/10.1007/978-3-030-13838-7%5F5). LOPSTR, 2019.


## License

Distributed under the Apache 2.0 license. See [LICENSE](https://github.com/workflowfm/workflowfm-reasoner/blob/master/LICENSE) for more information.

Copyright &copy; 2009-2021 [The University of Edinburgh](https://www.ed.ac.uk/) and [contributors](#authors)
