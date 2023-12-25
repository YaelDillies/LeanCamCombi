/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pointwise.Smul
import Order.Grade
import Mathlib.Order.Chain
import Mathlib.Order.RelIso.Group

#align_import mathlib.order.flag

/-!
# Additional constructions about flags

This file defines the action of order isomorphisms on flags and grades the elements of a flag.

## TODO

The file structure doesn't seem optimal. Maybe all the `flag` material could move here, or to a
subfolder?
-/


open scoped Pointwise

variable {𝕆 α : Type _}

namespace Flag

/-!
### Action on flags

Order isomorphisms act on flags.
-/


section Preorder

variable [Preorder α]

instance : SMul (α ≃o α) (Flag α) :=
  ⟨fun e => map e⟩

@[simp, norm_cast]
theorem coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s :=
  rfl

instance : MulAction (α ≃o α) (Flag α) :=
  SetLike.coe_injective.MulAction _ coe_smul

end Preorder

/-!
### Grading a flag

A flag inherits the grading of its ambient order.
-/


section PartialOrder

variable [PartialOrder α] {s : Flag α}

@[simp]
theorem coe_covby_coe {a b : s} : (a : α) ⋖ b ↔ a ⋖ b :=
  by
  refine'
    and_congr_right'
      ⟨fun h c hac => h hac, fun h c hac hcb =>
        @h ⟨c, mem_iff_forall_le_or_ge.2 fun d hd => _⟩ hac hcb⟩
  classical
  obtain hda | had := le_or_lt (⟨d, hd⟩ : s) a
  · exact Or.inr ((Subtype.coe_le_coe.2 hda).trans hac.le)
  obtain hbd | hdb := le_or_lt b ⟨d, hd⟩
  · exact Or.inl (hcb.le.trans hbd)
  · cases h had hdb

@[simp]
theorem isMax_coe {a : s} : IsMax (a : α) ↔ IsMax a :=
  ⟨fun h b hab => h hab, fun h b hab =>
    @h
      ⟨b,
        mem_iff_forall_le_or_ge.2 fun c hc => by
          classical exact Or.inr (hab.trans' <| h.is_top ⟨c, hc⟩)⟩
      hab⟩

@[simp]
theorem isMin_coe {a : s} : IsMin (a : α) ↔ IsMin a :=
  ⟨fun h b hba => h hba, fun h b hba =>
    @h
      ⟨b,
        mem_iff_forall_le_or_ge.2 fun c hc => by
          classical exact Or.inl (hba.trans <| h.is_bot ⟨c, hc⟩)⟩
      hba⟩

variable [Preorder 𝕆]

instance [GradeOrder 𝕆 α] (s : Flag α) : GradeOrder 𝕆 s :=
  GradeOrder.liftRight coe (Subtype.strictMono_coe _) fun _ _ => coe_covby_coe.2

instance [GradeMinOrder 𝕆 α] (s : Flag α) : GradeMinOrder 𝕆 s :=
  GradeMinOrder.liftRight coe (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2) fun _ =>
    isMin_coe.2

instance [GradeMaxOrder 𝕆 α] (s : Flag α) : GradeMaxOrder 𝕆 s :=
  GradeMaxOrder.liftRight coe (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2) fun _ =>
    isMax_coe.2

instance [GradeBoundedOrder 𝕆 α] (s : Flag α) : GradeBoundedOrder 𝕆 s :=
  GradeBoundedOrder.liftRight coe (Subtype.strictMono_coe _) (fun _ _ => coe_covby_coe.2)
    (fun _ => isMin_coe.2) fun _ => isMax_coe.2

@[simp, norm_cast]
theorem grade_coe [GradeOrder 𝕆 α] (a : s) : grade 𝕆 (a : α) = grade 𝕆 a :=
  rfl

end PartialOrder

end Flag
