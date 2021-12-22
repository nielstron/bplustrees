# A Verified Imperative Implementation of B+-Trees

This repository contains all definitions, lemmas and proofs
related to the paper "A Verified Imperative Implementation of B+-Trees in Isabelle/HOL"
by Niels Mündler and Tobias Nipkow.

For a detailed description of the project, [see the thesis](paper).

## Overview

A functional specification of B+-trees and B+-tree operations may be found in
the files `BPlusTree*.thy` that do not contain `Imp`.

An imperative specification of B+-trees may be found in `BPlusTree_Imp*.thy`.
This imperative specification makes use of the auxiliary definition
of "Partially Filled Arrays" as list refinements, which may be found in `Partially_Filled_Array.thy`.

The files `BPlusTree_Iter.thy` and `*Range*` introduce efficient iterators
and range queries on the imperative B+-Tree.
They make use of the auxiliary definition of the "Flattening Iterator" that
is found in `Flatten_Iter.thy`.

The remaining files contain auxiliary lemmas and definitions and proof tacs that are due to
Peter Lammich, Manuel Eberl or me. 

All above mentioned files contain definitions as well as proofs of functional correctness.


## Usage

These theories have been tested with [Isabelle2021](https://isabelle.in.tum.de/website-Isabelle2021/index.html).

The files `BPlusTree*.thy` that do not contain `Imp` only need a regular Isabelle setup.

The rest of the theories build upon [Refine_Imperative_HOL](https://www.isa-afp.org/entries/Refine_Imperative_HOL.html), you will need to succesfully set up that project first as described in the [Archive of Formal Proofs](https://www.isa-afp.org/using.html).
The script `start_isabelle.sh` uses and if not available compiles a session
containing the content of the Refinement Framework which significantly enhances
working with the files provided in this project.
