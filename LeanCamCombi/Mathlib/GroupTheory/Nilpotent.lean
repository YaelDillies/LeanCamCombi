import Mathlib.GroupTheory.Nilpotent

namespace Group
variable {G H : Type*} [Group G] [Group H]

@[simp] lemma comap_upperCentralSeries (e : H ≃* G) :
    ∀ n, (upperCentralSeries G n).comap e = upperCentralSeries H n
  | 0 => by simpa [MonoidHom.ker_eq_bot_iff] using e.injective
  | n + 1 => by
    ext
    simp [mem_upperCentralSeries_succ_iff, ← comap_upperCentralSeries e n,
      ← e.toEquiv.forall_congr_right]

attribute [mk_iff] IsNilpotent

lemma isNilpotent_congr (e : G ≃* H) : IsNilpotent G ↔ IsNilpotent H := by
  simp_rw [isNilpotent_iff]
  refine exists_congr fun n ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [← Subgroup.comap_top e.symm.toMonoidHom, ← h]
  · simp [← Subgroup.comap_top e.toMonoidHom, ← h]

@[simp] lemma isNilpotent_top : IsNilpotent (⊤ : Subgroup G) ↔ IsNilpotent G :=
  isNilpotent_congr Subgroup.topEquiv

variable (G) in
def IsVirtuallyNilpotent : Prop := ∃ N : Subgroup G, IsNilpotent N ∧ Finite (G ⧸ N)

lemma IsNilpotent.isVirtuallyNilpotent (hG : IsNilpotent G) : IsVirtuallyNilpotent G :=
  ⟨⊤, by simpa, inferInstance⟩

end Group
