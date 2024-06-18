import Mathlib.Analysis.Convex.Hull

section OrderedCommSemiring
variable {𝕜 E : Type*} [OrderedCommRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

open scoped Pointwise

-- TODO: Turn `convexHull_smul` around
lemma convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s :=
  (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s |>.symm

end OrderedCommSemiring

section pi
variable {𝕜 ι : Type*} {E : ι → Type*} [Fintype ι] [LinearOrderedField 𝕜]
  [Π i, AddCommGroup (E i)] [Π i, Module 𝕜 (E i)] {s : Set ι} {t : Π i, Set (E i)} {f : Π i, E i}

lemma mem_convexHull_pi (h : ∀ i ∈ s, f i ∈ convexHull 𝕜 (t i)) : f ∈ convexHull 𝕜 (s.pi t) :=
  sorry -- See `mk_mem_convexHull_prod`

@[simp] lemma convexHull_pi (s : Set ι) (t : Π i, Set (E i)) :
    convexHull 𝕜 (s.pi t) = s.pi (fun i ↦ convexHull 𝕜 (t i)) :=
  Set.Subset.antisymm (convexHull_min (Set.pi_mono fun _ _ ↦ subset_convexHull _ _) $ convex_pi $
    fun _ _ ↦ convex_convexHull _ _) fun _ ↦ mem_convexHull_pi

end pi
