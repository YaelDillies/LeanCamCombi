import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.TensorProduct.Free

open Polynomial TensorProduct

universe u v
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma LinearMap.charpoly_baseChange [Module.Free R M] [Module.Finite R M]
    {A} [CommRing A] [Algebra R A] (f : M →ₗ[R] M) :
    (f.baseChange A).charpoly = f.charpoly.map (algebraMap R A) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  let I := Module.Free.ChooseBasisIndex R M
  let b : Basis I R M := Module.Free.chooseBasis R M
  rw [← f.charpoly_toMatrix b, ← (f.baseChange A).charpoly_toMatrix (b.baseChange A),
    ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp [Matrix.map_apply, LinearMap.toMatrix_apply, ← Algebra.algebraMap_eq_smul_one]
