import Mathlib.Data.Int.Defs

namespace Int
variable {a b c d : ℤ}

attribute [simp] Int.dvd_zero

protected lemma mul_dvd_mul : a ∣ b → c ∣ d → a * c ∣ b * d
  | ⟨e, he⟩, ⟨f, hf⟩ => ⟨e * f, by simp [he, hf, Int.mul_assoc, Int.mul_left_comm, Nat.mul_comm]⟩

protected lemma mul_dvd_mul_left (a : ℤ) (h : b ∣ c) : a * b ∣ a * c := Int.mul_dvd_mul a.dvd_refl h

lemma dvd_mul_of_div_dvd (h : b ∣ a) (hdiv : a / b ∣ c) : a ∣ b * c := by
  obtain ⟨e, rfl⟩ := hdiv
  rw [← Int.mul_assoc, Int.mul_comm _ (a / b), Int.ediv_mul_cancel h]
  exact Int.dvd_mul_right a e

@[simp] lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) : a / b ∣ c ↔ a ∣ b * c :=
  exists_congr <| fun d ↦ by
  have := Int.dvd_trans (Int.dvd_mul_left _ _) (Int.mul_dvd_mul_left d h)
  rw [eq_comm, Int.mul_comm, ← Int.mul_ediv_assoc d h, Int.ediv_eq_iff_eq_mul_right hb this,
    Int.mul_comm, eq_comm]

lemma mul_dvd_of_dvd_div (hcb : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have ⟨d, hd⟩ := h
  ⟨d, by simpa [Int.mul_comm, Int.mul_left_comm] using Int.eq_mul_of_ediv_eq_left hcb hd⟩

lemma dvd_div_of_mul_dvd (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by simp [ha]
  else
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d := Int.ediv_eq_of_eq_mul_right ha (by simpa [Int.mul_assoc] using hd)
    show ∃ d, c / a = b * d from ⟨d, h2⟩

-- TODO: Rename `Nat.dvd_div_iff` to `Nat.dvd_div_iff_mul_dvd`
@[simp] lemma dvd_div_iff_mul_dvd (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨mul_dvd_of_dvd_div hbc, dvd_div_of_mul_dvd⟩

end Int
