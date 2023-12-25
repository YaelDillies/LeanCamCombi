import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Data.Zmod.Basic
import Mathlib.Algebra.CharP.Basic

#align_import mathlib.combinatorics.additive.salem_spencer

open Finset

section rothNumberNat

variable {s : Finset ℕ} {k n : ℕ}

theorem Fin.rothNumberNat_le_addRothNumber (hkn : 2 * k ≤ n) :
    rothNumberNat k ≤ addRothNumber (Iio k : Finset <| Fin n.succ) := by
  classical
  obtain ⟨s, hsm, hscard, hs⟩ := rothNumberNat_spec k
  simp only [subset_iff, mem_range] at hsm
  rw [two_mul] at hkn
  rw [← hscard, ←
    card_image_of_inj_on
      ((CharP.nat_cast_injOn_Iio (ZMod n.succ) n.succ).mono fun x hx =>
        Nat.lt_succ_iff.2 <| (hsm hx).le.trans <| le_add_self.trans hkn)]
  refine' AddSalemSpencer.le_addRothNumber _ _
  · rw [coe_image]
    rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ habc
    norm_cast at habc
    refine' congr_arg _ (hs ha hb hc <| CharP.nat_cast_injOn_Iio _ n.succ _ _ habc) <;>
          simp only [Nat.lt_succ_iff, Set.mem_Iio] <;>
        refine' (add_le_add (hsm _).le (hsm _).le).trans hkn <;>
      assumption
  · replace hkn := Nat.lt_succ_iff.2 (le_add_self.trans hkn)
    simp only [image_subset_iff, mem_Iio, Fin.lt_iff_val_lt_val, Fin.coe_ofNat_eq_mod]
    rintro x hx
    rw [Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt ((hsm hx).trans hkn)]
    exact hsm hx

end rothNumberNat
