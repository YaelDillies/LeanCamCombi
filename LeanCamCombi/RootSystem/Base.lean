import LeanCamCombi.RootSystem.Basic

open Set Function

namespace IsRootSystem

structure IsBase {k V ι : Type _} [LinearOrderedField k] [AddCommGroup V] [Module k V] {Φ : Set V}
    (h : IsRootSystem k Φ) (b : Basis ι k V) : Prop where
  Subset : range (b : ι → V) ⊆ Φ
  is_integral : ∀ α ∈ Φ, ∀ (i), b.Coord i α ∈ AddSubgroup.zmultiples (1 : k)
  same_sign : ∀ α ∈ Φ, (∀ i, 0 ≤ b.Coord i α) ∨ ∀ i, b.Coord i α ≤ 0

variable {k : Type _} {V : Type _} [LinearOrderedField k] [AddCommGroup V] [Module k V]

/-- Regular -/
structure IsRegular (Φ : Set V) (f : Module.Dual k V) : Prop where
  regularity : ∀ α ∈ Φ, f α ≠ 0

/-- Positive and Negative roots -/
def positiveRoots (Φ : Set V) (v : Module.Dual k V) (h : IsRegular Φ v) : Set V :=
  {α ∈ Φ | 0 < v α}

def negativeRoots (Φ : Set V) (v : Module.Dual k V) (h : IsRegular Φ v) : Set V :=
  {α ∈ Φ | v α < 0}

/-- Decomposable and Indecomposable roots -/
def IsDecomposable (Φ : Set V) (v : Module.Dual k V) (h : IsRegular Φ v) (α : V) : Prop :=
  α ∈ positiveRoots Φ v h ∧ ∃ β γ : V, β ∈ positiveRoots Φ v h ∧ γ ∈ positiveRoots Φ v h ∧ α = β + γ

def IsIndecomposable (Φ : Set V) (v : Module.Dual k V) (h : IsRegular Φ v) (α : V) : Prop :=
  α ∈ positiveRoots Φ v h ∧ ∀ β γ : V, β ∈ positiveRoots Φ v h ∧ γ ∈ positiveRoots Φ v h → α ≠ β + γ

-- lemma indecomposable_diff_not_root (Φ : set V) (v : module.dual k V) (h : is_regular Φ v) (α β : V) :
--   is_indecomposable Φ v h α ∧ is_indecomposable Φ v h β → α - β ∉ Φ :=
-- begin
--   sorry,
-- end
end IsRootSystem
