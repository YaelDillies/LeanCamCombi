# Cambridge combinatorics in Lean

[![.github/workflows/push_master.yml](https://github.com/YaelDillies/LeanCamCombi/actions/workflows/push_master.yml/badge.svg)](https://github.com/YaelDillies/LeanCamCombi/actions/workflows/push_master.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/YaelDillies/LeanCamCombi)

This repository aims at formalising the mathematics courses relevant to combinatorics that are lectured in Cambridge, UK.

## What is formalisation?

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements and theorem proofs. Digitisation, or formalisation, is a process where the source material, typically a mathematical textbook or a PDF file is transformed into definitions in a target system consisting of a computer implementation of a logical theory (such as set theory or type theory).

### The source

The definitions, theorems and proofs in this repository are (mostly) taken from five Cambridge courses:
* Part II Graph Theory, Michaelmas 2022, lectured by Julian Sahasrabudhe
* Part III Combinatorics, Michaelmas 2022 & Michaelmas 2023, lectured by Béla Bollobás
* Part III Extremal and Probabilistic Combinatorics, lectured by Julian Sahasrabudhe
* Part III Ramsey Theory on Graphs, Michaelmas 2024, lectured by Julian Sahasrabudhe
* Part III Additive Combinatorics, Lent 2024, lectured by Julia Wolf

### The target

The formal system which we are using as a target is [Lean 4](https://github.com/leanprover/lean4). Lean is a dependently typed theorem prover and programming language based on the Calculus of Inductive Constructions. It is being developed at AWS and Microsoft Research by Leonardo de Moura and his team.

Our project is backed by [mathlib](https://github.com/leanprover-community/mathlib4), the major classical maths library written in Lean 4.

## Content

The project contains

* **Prerequisites** to be upstreamed to mathlib: Lemmas that belong in existing mathlib files and background theories. Those are located in the `Mathlib` subfolder.
* **Formal translations of example sheets**: Every course in Cambridge comes with 3 or 4 "example sheets", which are lists of questions/exercises/problems for the students to solve. Those are located in the `ExampleSheets` subfolder.
* **Theory developments**: Formalisation of the courses per se. The mathlib philosophy of proving the most general result accessible applies here as well. This means that not all proofs follow the lecture notes, and might instead derive a result from the lectures from a more general theorem. Those make up the other subfolders and standalone lemmas.
* **Archived results**: It sometimes happens in mathlib that a long argument gets replaced by a shorter one, with a different proof. When the long argument was proved in a lecture, we salvage it to `LeanCamCombi` for conservation purposes.

### Content under development

The following topics are under active development in LeanCamCombi.

* The Erdős-Rényi model for random graphs, aka binomial random graph
* The Littlewood-Offord problem
* The van den Berg-Kesten-Reimer inequality
* The impact function of a set
* Simplicial complexes and Sperner's lemma
* Discrete calculus
* The Birkhoff representation theorem, categorical version
* The Minkowski-Carathéodory theorem

### Current content

The following topics are covered in LeanCamCombi and could be upstreamed to mathlib.

* The Kruskal-Katona theorem and the Erdős-Ko-Rado theorem
<!-- * The Erdős-Ginzburg-Ziv theorem -->
* Kneser's addition theorem
* The Sylvester-Chvatal theorem
* The Ahlswede-Zhang inequality
* Containment of graphs
* Incidence algebras

The following topics are archived because they are already covered by mathlib, but nevertheless display interesting proofs:
* The Cauchy-Davenport theorem for `ℤ/pℤ` as a corollary of Kneser's theorem.

### Past content

The following topics have been upstreamed to mathlib and no longer live in LeanCamCombi.

* The four functions theorem and related discrete correlation inequalities: FKG inequality, Holley inequality, Daykin inequality, Marica-Schönheim inequality
* The Birkhoff representation theorem, non-categorical version
* The Cauchy-Davenport theorem for general groups, and also for linearly ordered cancellative semigroup
* Shatterings of sets, the Sauer-Shelah lemma and the Vapnik-Chervonenkis dimension
* Sublattices
* Strongly convex functions
* The Marica-Schönheim proof of the squarefree special case of Graham's conjecture

## Interacting with the project

### Getting the project

At the moment, the recommended way of browsing this repository is by using a Lean development environment. Crucially, this will allow you to introspect Lean's "Goal state" during proofs, and easily jump to definitions or otherwise follow paths through the code.

We are looking into ways to setup an online interactive website that will provide the same experience without the hassle of installing a complete Lean development environment.

For the time being: please use the [installation instructions](https://leanprover-community.github.io/get_started) to install Lean and a supporting toolchain. After that, download and open a copy of the repository by executing the following commands in a terminal:
```
git clone https://github.com/YaelDillies/LeanCamCombi
cd LeanCamCombi
lake exe cache get
cd ../
code LeanCamCombi
```
If you are interested, here are [detailed instructions on how to work with Lean projects](https://leanprover-community.github.io/install/project).

### Browsing the project

With the project opened in VScode, you are all set to start exploring the code. There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": If you right-click on a name of a definition or lemma (such as `ErdosRenyi`, or `Finset.sups`), then you can choose "Go to definition" from the menu, and you will be taken to the relevant location in the source files. This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*, you can step through the proof line-by-line, and see the internals of Lean's "brain" in the Goal window. If the Goal window is not open, you can open it by clicking on the forall icon in the top right hand corner.

### Contributing

This project is open to contribution. You are in fact encouraged to have a look at the example sheet formalisations and try your hand at one of the problems. If you manage to prove one of them, please open a PR!

If you want to contribute a theorem or theory development, please open a PR! Note however that the standard of code is pretty high and that is not because you have formalised a concept/proved a theorem that it can be included into LeanCamCombi as is. Nonetheless I am willing to review your code and put it in shape for incorporation.
