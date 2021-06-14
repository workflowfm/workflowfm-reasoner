---
title: "Setup"
author: ["Petros Papapanagiotou"]
lastmod: 2021-06-14T23:25:24+01:00
draft: false
weight: 110
---

## Quick setup {#quick-setup}

Clone the following repository:
<https://github.com/workflowfm/hol-light>

```sh
git clone https://github.com/workflowfm/hol-light.git
```

Then make sure all the submodules are initialised and updated:

```sh
git submodule update --init --recursive
```


## Manual setup {#manual-setup}

Assuming an existing installation of HOL Light, you can setup the reasoner manually by installing the following libraries:

1.  The [Isabelle Light](https://bitbucket.org/petrospapapa/isabelle-light) library. This also comes bundled with HOL Light by default.
2.  Additional [HOL Light tools](https://github.com/PetrosPapapa/hol-light-tools). This consists of useful snippets of code, libraries, and theorems. This should be installed in a `tools/` directory within HOL Light.
3.  The [HOL Light embed](https://github.com/PetrosPapapa/hol-light-embed) library which enables reasoning with encoded logics. This should be installed in a `embed/` directory within HOL Light.

{{< tip "warning">}}
It is important to use the correct directory names, as the reasoner will seek to load specific files from each library.
{{< /tip >}}

Finally, install the reasoner itself by cloning the repository to a `workflowfm/` directory within HOL Light:

```sh
git clone https://github.com/workflowfm/workflowfm-reasoner.git worklfowfm
```
