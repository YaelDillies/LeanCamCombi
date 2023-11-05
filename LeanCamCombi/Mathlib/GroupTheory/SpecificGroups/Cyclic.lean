import Mathlib.GroupTheory.SpecificGroups.Cyclic

instance {n : ℕ} : IsAddCyclic (ZMod n) :=
  ⟨⟨1, fun x => (ZMod.int_cast_surjective x).imp <| by simp⟩⟩

instance {p : ℕ} [Fact p.Prime] : IsSimpleAddGroup (ZMod p) :=
  AddCommGroup.is_simple_iff_isAddCyclic_and_prime_card.2
    ⟨by infer_instance, by simpa using (Fact.out : p.Prime)⟩
