import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Rank

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] {α : ι → Type*} [Semiring R] {m n : ℕ}
  {f f₁ f₂ : (∀ i, α i) → R}

/-- A function `f` *has slice-rank at most* `n` if it can be written as the sum of `n` functions
of the form `x ↦ g (x i) * h (x 1, ..., x (i - 1), x (i + 1), ..., x k)`. -/
@[mk_iff hasSliceRankLE_iff]
inductive HasSliceRankLE : ℕ → ((∀ i, α i) → R) → Prop
  | zero : HasSliceRankLE 0 0
  | succ ⦃n f i⦄ (g : α i → R) (h : (∀ j ≠ i, α j) → R) :
    HasSliceRankLE n f → HasSliceRankLE (n + 1) (f + (fun x ↦ g (x i) * h (fun j _ ↦ x j)))

@[simp] lemma hasSliceRankLE_zero : HasSliceRankLE 0 f ↔ f = 0 := by
  rw [hasSliceRankLE_iff]; simp [@eq_comm _ 0]

lemma hasSliceRankLE_succ :
    HasSliceRankLE (n + 1) f ↔ ∃ f' i, ∃ (g : α i → R) (h : (∀ j ≠ i, α j) → R),
      HasSliceRankLE n f' ∧ f = f' + fun x ↦ g (x i) * h fun j _ ↦ x j := by
  rw [hasSliceRankLE_iff]
  sorry -- aesop

lemma hasSliceRankLE_one :
    HasSliceRankLE 1 f ↔ ∃ i, ∃ (g : α i → R) (h : (∀ j ≠ i, α j) → R),
      f = fun x ↦ g (x i) * h fun j _ ↦ x j := by simp [hasSliceRankLE_succ]

lemma hasSliceRankLE_iff_exists_sum :
    HasSliceRankLE n f ↔ ∃ (i : Fin n → ι) (g : ∀ k, α (i k) → R) (h : ∀ k, (∀ j ≠ i k, α j) → R),
      f = ∑ k, fun x ↦ g k (x (i k)) * h k fun j _ ↦ x j := by
  induction' n with n ih generalizing f
  · simp
  simp_rw [hasSliceRankLE_succ, ih]
  constructor
  · rintro ⟨f', iₙ, gₙ, hₙ, ⟨i, g, h, rfl⟩, rfl⟩
    refine ⟨Fin.cons iₙ i, Fin.cons gₙ g, Fin.cons hₙ h, ?_⟩
    ext x
    simp only [ne_eq, Pi.add_apply, Finset.sum_apply, add_comm (_ * _), Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    congr
  · rintro ⟨i, g, h, rfl⟩
    refine ⟨_, i 0, g 0, h 0, ⟨Fin.tail i, Fin.tail g, Fin.tail h, rfl⟩, ?_⟩
    ext x
    simp only [ne_eq, Pi.add_apply, Finset.sum_apply, add_comm (_ * _), Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    congr

lemma HasSliceRankLE.add (h₁ : HasSliceRankLE m f₁) :
    ∀ {n f₂}, HasSliceRankLE n f₂ → HasSliceRankLE (m + n) (f₁ + f₂)
  | _, _, .zero => by simpa
  | _, _, .succ g h h₂ => by simpa [add_assoc] using (h₁.add h₂).succ g h

/-- Any function has slice-rank bounded by the cardinality of its domain. -/
lemma hasSliceRankLE_card [Fintype ι] [∀ i, Fintype (α i)] (f : (∀ i, α i) → R) :
    HasSliceRankLE (Fintype.card (∀ i, α i)) f := by
  rw [hasSliceRankLE_iff_exists_sum]
  sorry

/-- Any function from a finite type has finite slice-rank. -/
lemma exists_hasSliceRankLE [Finite ι] [∀ i, Finite (α i)] (f : (∀ i, α i) → R) :
    ∃ n, HasSliceRankLE n f := by
  cases nonempty_fintype ι
  have (i) := Fintype.ofFinite (α i)
  exact ⟨_, hasSliceRankLE_card _⟩
