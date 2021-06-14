---
title: "Loading the reasoner"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:25:28+01:00
draft: false
weight: 130
---

Once you have HOL Light up and running, you can load the reasoner in **console mode** using the following command:

```ocaml
loads (!hol_dir ^ "/workflowfm/make.console.ml");;
```

If you need to use the **JSON mode**, you can use this command instead:

```ocaml
loads (!hol_dir ^ "/workflowfm/make.ml");;
```
