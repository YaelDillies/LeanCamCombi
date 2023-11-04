---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
---

# Cambridge combinatorics in Lean

The purpose of this community-owned repository is to *digitise* some mathematical definitions, theorem statements and theorem proofs. Digitisation, or formalisation, is a process where the source material, typically a mathematical textbook or a pdf file or website or video, is transformed into definitions in a target system consisting of a computer implementation of a logical theory (such as set theory or type theory).

Much of the project infrastructure has been adapted from the [sphere eversion project](https://leanprover-community.github.io/sphere-eversion/), the [liquid tensor experiment](https://leanprover-community.github.io/lean-liquid/), and the [unit fractions project](https://github.com/b-mehta/unit-fractions/).

## Current progress

The project is not yet finished. The following table details live which files are unfinished, and how many 'sorry' (unproven statements) remain in each file.

{% include sorries.md %}

## Files to upstream to mathlib

{% include files_to_upstream.md %}

## The source

The definitions, theorems and proofs in this repository are taken from three Cambridge courses:
* Part II Graph Theory, lectured by Julian Sahasrabudhe
* Part III Combinatorics, lectured by Béla Bollobás
* Part III Extremal and Probabilistic Combinatorics, lectured by Julian Sahasrabudhe

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a project being developed at Microsoft Research by Leonardo de Moura and his team. Our formalisation could not have even started without a major classical mathematical library backing it up, and so we chose Lean 3 as the engine behind the project. Note that Lean 4's type theory is the same as Lean 3's type theory, however porting a million lines of mathematical library between languages is a *highly* nontrivial endeavour.

## How to browse this repository

### Blueprint

Below we explain how to engage with the Lean code directly.
We also provide a [blueprint](https://yaeldillies.github.io/leancamcombi/)
including a [dependency graph](https://yaeldillies.github.io/leancamcombi/blueprint/dep_graph.html)
of the main ingredients in the repository.
This blueprint is developed in sync with the Lean formalization,
and will hence see frequent updates during the length of the project.
More information on building the blueprint locally is given below.

### Getting the project

At the moment, the recommended way of browsing this repository,
is by using a Lean development environment.
Crucially, this will allow you to introspect Lean's "Goal state" during proofs,
and easily jump to definitions or otherwise follow paths through the code.

We are looking into ways to setup an online interactive website
that will provide the same experience without the hassle of installing a complete
Lean development environment.

For the time being: please use the
[installation instructions](https://leanprover-community.github.io/get_started.html#regular-install)
to install Lean and a supporting toolchain.
After that, download and open a copy of the repository
by executing the following command in a terminal:
```
leanproject get lean-cam-combi
code lean-cam-combi
```
For detailed instructions on how to work with Lean projects,
see [this](https://leanprover-community.github.io/install/project.html). The script `scripts/get-cache.sh`
in the folder `lean-cam-combi` will download the `olean` files created by our continuous integration. This
will save you some time by not havig to do `leanproject build`.

### Reading the project

With the project opened in VScode,
you are all set to start exploring the code.
There are two pieces of functionality that help a lot when browsing through Lean code:

* "Go to definition": If you right-click on a name of a definition or lemma
  (such as `normal_filter`, or `clans`), then you can choose "Go to definition" from the menu,
  and you will be taken to the relevant location in the source files.
  This also works by `Ctrl`-clicking on the name.
* "Goal view": in the event that you would like to read a *proof*,
  you can step through the proof line-by-line,
  and see the internals of Lean's "brain" in the Goal window.
  If the Goal window is not open,
  you can open it by clicking on one of the icons in the top right hand corner.

### Organization of the project

* The Lean code is contained in the directory `src/`.

## Building the blueprint locally

To build the web version of the blueprint locally, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev pandoc
pip3 install invoke
cd .. # go to a folder where you are happy to clone git repos
git clone https://github.com/plastex/plastex
pip3 install ./plastex
git clone https://github.com/PatrickMassot/leanblueprint
pip3 install ./leanblueprint
```

To actually build the blueprint, `cd` to the `LeanCamCombi` folder and run
```
leanproject get-mathlib-cache
leanproject build
inv all html
```

To view the web version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.

## Source reference

`[untangled]` : https://randall-holmes.github.io/Nfproof/untangled.pdf

[untangled]: https://randall-holmes.github.io/Nfproof/untangled.pdf
