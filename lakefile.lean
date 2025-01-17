import Lake
open Lake DSL

package LeanCamCombi where
  leanOptions := #[
    ⟨`autoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`relaxedAutoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib LeanCamCombi
