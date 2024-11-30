# Upstreaming dashboard

The eventual goal of the LeanCamCombi project is to not contain any significant new formalisation, but instead to act as a shallow layer over [Mathlib](https://github.com/leanprover-community/mathlib4) showing concretely how to turn paper-combinatorics into Lean-combinatorics.

As such, it is crucial to continuously upstream code from LeanCamCombi to Mathlib. The way we organise this is with the following two lists, showing files with no LeanCamCombi dependencies depending on whether they contain the keyword `sorry` or not.

## Files ready to upstream

The following files are `sorry`-free and do not depend on any other LeanCamCombi, meaning they can be readily PRed to Mathlib.

{% include ready_to_upstream.md %}

## Files easy to unlock

The following files do not depend on any other LeanCamCombi file but still contain `sorry`, usually indicating that working on eliminating those sorries might unblock some part of the project.

{% include easy_to_unlock.md %}
