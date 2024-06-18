/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Basic
import LeanCamCombi.Mathlib.Analysis.Convex.Normed
import LeanCamCombi.Mathlib.Analysis.Normed.Group.Basic
import LeanCamCombi.Mathlib.Topology.Algebra.Group.Basic

/-!
# Convex functions are continuous

This file proves that a convex function from a finite dimensional real inner product space to `ℝ` is
continuous.

## TODO

Define `LocallyLipschitzOn`
-/

open FiniteDimensional Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {s : Set E} {f : E → ℝ}

protected lemma ConvexOn.continuousOn (hf : ConvexOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := by
  classical
  -- refine isOpen_interior.continuousOn_iff.2 (fun x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := isOpen_interior.exists_mem_interior_convexHull_finset hx,
  -- set M := t.sup' (convexHull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (fun ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convexHull
  --   (hf.subset (hts.trans interior_subset) $ convex_convexHull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, fun y hy, _⟩,
  -- sorry,
  sorry

protected lemma ConcaveOn.continuousOn (hf : ConcaveOn ℝ s f) :
    ContinuousOn f (intrinsicInterior ℝ s) := by simpa using hf.neg.continuousOn

protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  classical
  -- refine isOpen_interior.continuousOn_iff.2 (fun x hx, _),
  -- obtain ⟨t, hxt, hts⟩ := isOpen_interior.exists_mem_interior_convexHull_finset hx,
  -- set M := t.sup' (convexHull_nonempty_iff.1 $ nonempty.mono interior_subset ⟨x, hxt⟩) f,
  -- refine metric.continuous_at_iff.2 (fun ε hε, _),
  -- have : f x ≤ M := le_sup_of_mem_convexHull
  --   (hf.subset (hts.trans interior_subset) $ convex_convexHull _ _) (interior_subset hxt),
  -- refine ⟨ε / (M - f x), _, fun y hy, _⟩,
  -- sorry,
  sorry

protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.neg.locallyLipschitz
