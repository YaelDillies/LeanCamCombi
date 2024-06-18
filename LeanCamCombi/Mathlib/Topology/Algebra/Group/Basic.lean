import Mathlib.Topology.Algebra.Group.Basic

variable {α G : Type*}

section ContinuousInv
variable [TopologicalSpace G] [InvolutiveInv G] [ContinuousInv G] [TopologicalSpace α]
  {f : α → G} {s : Set α} {x : α}

@[to_additive (attr := simp)]
lemma continuous_inv_iff : Continuous f⁻¹ ↔ Continuous f := (Homeomorph.inv G).comp_continuous_iff

@[to_additive (attr := simp)]
lemma continuousAt_inv_iff : ContinuousAt f⁻¹ x ↔ ContinuousAt f x :=
  (Homeomorph.inv G).comp_continuousAt_iff _ _

@[to_additive (attr := simp)]
lemma continuousOn_inv_iff : ContinuousOn f⁻¹ s ↔ ContinuousOn f s :=
  (Homeomorph.inv G).comp_continuousOn_iff _ _

end ContinuousInv
