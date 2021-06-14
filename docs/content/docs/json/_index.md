---
title: "JSON API"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:26:16+01:00
draft: false
weight: 400
---

The second mode of the WorkflowFM Reasoner exposes a [JSON](https://en.wikipedia.org/wiki/JSON) API that can enable interaction with external and web based systems.

The JSON API mode can be loaded using the following command:

```ocaml
loads (!hol_dir ^ "/workflowfm/make.ml");;
```

The rest of this section describes the main types involved in the JSON schema, as well as the format for providing commands and the responses the reasoner can generate.
