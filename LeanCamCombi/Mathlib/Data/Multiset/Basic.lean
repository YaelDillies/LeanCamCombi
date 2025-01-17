import Mathlib.Data.Multiset.Basic
import LeanCamCombi.Mathlib.Data.List.DropRight

/-!
## TODO

* Rename `Multiset.coe_attach` to `Multiset.attach_coe`
* Rename `Multiset.coe_countp` to `Multiset.countp_coe`
* Maybe change `Multiset.attach` to make `Multiset.coe_attach` refl?
-/

namespace Multiset
variable {α : Type*} {s t : Multiset α} {n : ℕ}

lemma exists_intermediate (hst : s ≤ t) (hs : card s ≤ n) (ht : n ≤ card t) :
    ∃ u, s ≤ u ∧ u ≤ t ∧ card u = n := by
  induction' s using Quotient.inductionOn with l₀
  induction' t using Quotient.inductionOn with l₂
  obtain ⟨l₁, h⟩ := hst.exists_intermediate hs ht
  exact ⟨l₁, h⟩

lemma exists_le_card_eq (hn : n ≤ card s) : ∃ t, t ≤ s ∧ card t = n := by
  simpa [zero_le] using exists_intermediate (zero_le _) (Nat.zero_le _) hn

variable [DecidableEq α]

lemma le_card_sub : card s - card t ≤ card (s - t) :=
  Nat.sub_le_iff_le_add'.2 $ (card_mono Multiset.le_add_sub).trans_eq $ card_add _ _

end Multiset
