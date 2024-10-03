import Mathlib.Order.Circular
import Mathlib.Topology.MetricSpace.Defs

/-!
### TODO

Axiomatic betweenness
-/

variable {V : Type*} [MetricSpace V] {u v w : V}

def MetricSBtw : SBtw V where
  sbtw u v w := u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ dist u v + dist v w = dist u w

scoped[MetricBetweenness] attribute [instance] MetricSBtw

open MetricBetweenness

lemma MetricSpace.sbtw_iff :
  sbtw u v w ↔ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ dist u v + dist v w = dist u w := Iff.rfl

lemma SBtw.sbtw.ne12 (h : sbtw u v w) : u ≠ v := h.1
lemma SBtw.sbtw.ne13 (h : sbtw u v w) : u ≠ w := h.2.1
lemma SBtw.sbtw.ne23 (h : sbtw u v w) : v ≠ w := h.2.2.1
lemma SBtw.sbtw.dist (h : sbtw u v w) : dist u v + dist v w = dist u w := h.2.2.2

lemma SBtw.sbtw.symm : sbtw u v w → sbtw w v u
| ⟨huv, huw, hvw, d⟩ => ⟨hvw.symm, huw.symm, huv.symm, by simpa [dist_comm, add_comm] using d⟩
lemma SBtw.comm : sbtw u v w ↔ sbtw w v u :=
⟨.symm, .symm⟩

lemma sbtw_iff_of_ne (h12 : u ≠ v) (h13 : u ≠ w) (h23 : v ≠ w) :
    sbtw u v w ↔ dist u v + dist v w = dist u w :=
  by simp [MetricSpace.sbtw_iff, h12, h13, h23]

lemma sbtw_mk (h12 : u ≠ v) (h23 : v ≠ w) (h : dist u v + dist v w ≤ dist u w) : sbtw u v w := by
  refine ⟨h12, ?_, h23, h.antisymm (dist_triangle _ _ _)⟩
  rintro rfl
  rw [dist_self] at h
  replace h : dist v u ≤ 0 := by linarith [dist_comm v u]
  simp only [dist_le_zero] at h
  exact h23 h

lemma SBtw.sbtw.right_cancel {u v w x : V} (h : sbtw u v x) (h' : sbtw v w x) : sbtw u v w :=
  sbtw_mk h.ne12 h'.ne12 (by linarith [h.dist, h'.dist, dist_triangle u w x, dist_triangle u v w])

lemma SBtw.sbtw.asymm_right {u v x : V} (h : sbtw u v x) (h' : sbtw v u x) : False := by
  have := h'.dist
  rw [dist_comm] at this
  have : Dist.dist u v = 0 := by linarith [h.dist]
  simp [h.ne12] at this

lemma SBtw.sbtw.trans_right' {u v w x : V} (h : sbtw u v x) (h' : sbtw v w x) : sbtw u w x :=
  have : u ≠ w := by rintro rfl; exact h.asymm_right h'
  sbtw_mk this h'.ne23 <| by linarith [h.dist, h'.dist, dist_triangle u v w]
