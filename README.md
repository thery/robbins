<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Robbins

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/robbins/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/robbins/actions/workflows/docker-action.yml




All Robbins algebras are Boolean algebras

A transcription in Coq of : `A Complete Proof of the Robbins Conjecture` 
Allen L. Mann  

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 9.0 or later
- Additional dependencies:
  - [MathComp ssreflect 2.4 or later](https://math-comp.github.io)
- Coq namespace: `robbins`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/robbins.git
cd robbins
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



