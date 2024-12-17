import Mathlib.ModelTheory.Semantics
import LeanCamCombi.StableCombi.Rel

namespace FirstOrder.Language
variable {L : Language}

namespace Formula
variable (n : ℕ) (M : Type*) [L.Structure M] (φ : L.Formula (Fin 2))

def IsOrderPropWith : Prop := IsOrderPropRelWith n fun x y : M ↦ φ.Realize ![x, y]

def IsOrderProp : Prop := IsOrderPropRel fun x y : M ↦ φ.Realize ![x, y]

def IsStableWith : Prop := IsStableRelWith n fun x y : M ↦ φ.Realize ![x, y]

def IsStable : Prop := IsStableRel fun x y : M ↦ φ.Realize ![x, y]

def IsTreeBoundedWith : Prop := IsTreeBoundedRelWith n fun x y : M ↦ φ.Realize ![x, y]

variable {n M φ}

@[simp] lemma not_isStableWith : ¬ IsStableWith n M φ ↔ IsOrderPropWith n M φ := not_isStableRelWith

@[simp] lemma not_isOrderPropWith : ¬ IsOrderPropWith n M φ ↔ IsStableWith n M φ :=
  not_isOrderPropRelWith

@[simp] lemma not_isStable : ¬ IsStable M φ ↔ IsOrderProp M φ := not_isStableRel

@[simp] lemma not_isOrderProp : ¬ IsOrderProp M φ ↔ IsStable M φ := not_isOrderPropRel

lemma IsStableWith.isTreeBoundedWith (hr : IsStableWith n M φ) :
    IsTreeBoundedWith (2 ^ n + 1) M φ := hr.isTreeBoundedRelWith

lemma IsTreeBoundedWith.isStableWith (hr : IsTreeBoundedWith n M φ) :
    IsStableWith (2 ^ n) M φ := hr.isStableRelWith

end Formula

namespace Theory
variable (T : L.Theory)

-- TODO: What universe should we set `M` to here?
def IsOrderProp : Prop :=
  ∃ (M : Type*) (_ : L.Structure M), M ⊨ T ∧ ∃ φ : L.Formula (Fin 2), φ.IsOrderProp M

def IsStable : Prop := ∀ ⦃M : Type*⦄ [L.Structure M], M ⊨ T → ∀ φ : L.Formula (Fin 2), φ.IsStable M

variable {T}

@[simp] lemma not_isStable : ¬ IsStable T ↔ IsOrderProp T := by simp [IsStable, IsOrderProp]

@[simp] lemma not_isOrderProp : ¬ IsOrderProp T ↔ IsStable T := by simp [← not_isStable]

end FirstOrder.Language.Theory
