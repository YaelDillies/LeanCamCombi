import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-!

## Main declarations

* `simple_graph.edge_disjoint_triangles`: Predicate for a graph whose triangles are edge-disjoint.
* `simple_graph.locally_linear`: Predicate for each edge in a graph to be in a unique triangle.
-/


open Finset

open Fintype (card)

open Nat

namespace SimpleGraph

variable {α β 𝕜 : Type _} [LinearOrderedField 𝕜] {G H : SimpleGraph α} {ε δ : 𝕜} {n : ℕ}
  {s : Finset α}

section LocallyLinear

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
def EdgeDisjointTriangles (G : SimpleGraph α) : Prop :=
  (G.cliqueSet 3).Pairwise fun x y => (x ∩ y : Set α).Subsingleton

/-- A graph is locally linear if each edge belongs to exactly one triangle. -/
def LocallyLinear (G : SimpleGraph α) : Prop :=
  G.EdgeDisjointTriangles ∧ ∀ ⦃x y⦄, G.Adj x y → ∃ s, G.IsNClique 3 s ∧ x ∈ s ∧ y ∈ s

protected theorem LocallyLinear.edgeDisjointTriangles : G.LocallyLinear → G.EdgeDisjointTriangles :=
  And.left

theorem EdgeDisjointTriangles.mono (h : G ≤ H) (hH : H.EdgeDisjointTriangles) :
    G.EdgeDisjointTriangles :=
  hH.mono <| cliqueSet_mono h

@[simp]
theorem edgeDisjointTriangles_bot : (⊥ : SimpleGraph α).EdgeDisjointTriangles := by
  simp [edge_disjoint_triangles]

@[simp]
theorem locallyLinear_bot : (⊥ : SimpleGraph α).LocallyLinear := by simp [locally_linear]

theorem EdgeDisjointTriangles.map (f : α ↪ β) (hG : G.EdgeDisjointTriangles) :
    (G.map f).EdgeDisjointTriangles := by
  rw [edge_disjoint_triangles, clique_set_map (by norm_num : 3 ≠ 1),
    ((Finset.map_injective f).InjOn _).pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter, ← map_inter, coe_map, coe_inter]
  exact (hG hs ht hst).image _

theorem LocallyLinear.map (f : α ↪ β) (hG : G.LocallyLinear) : (G.map f).LocallyLinear := by
  refine' ⟨hG.1.map _, _⟩
  rintro _ _ ⟨a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩

@[simp]
theorem locallyLinear_comap {G : SimpleGraph β} {e : α ≃ β} :
    (G.comap e).LocallyLinear ↔ G.LocallyLinear := by
  refine' ⟨fun h => _, _⟩
  · rw [← comap_map_eq e.symm.to_embedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact locally_linear.map _

variable [DecidableEq α]

theorem edgeDisjointTriangles_iff_mem_sym2_subsingleton :
    G.EdgeDisjointTriangles ↔
      ∀ ⦃e : Sym2 α⦄, ¬e.IsDiag → {s ∈ G.cliqueSet 3 | e ∈ (s : Finset α).Sym2}.Subsingleton := by
  have :
    ∀ a b,
      a ≠ b →
        {s ∈ (G.clique_set 3 : Set (Finset α)) | ⟦(a, b)⟧ ∈ (s : Finset α).Sym2} =
          {s | G.adj a b ∧ ∃ c, G.adj a c ∧ G.adj b c ∧ s = {a, b, c}} := by
    rintro a b hab
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Set.sep_and,
      Set.mem_inter_iff, Set.mem_sep_iff, mem_clique_set_iff, Set.mem_setOf_eq,
      and_and_and_comm _ (_ ∈ _), and_self_iff, is_3_clique_iff]
    constructor
    · rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab⟩
      simp only [mem_insert, mem_singleton] at hab
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab <;>
            simp_all only [adj_comm, true_and_iff, Ne.def, eq_self_iff_true, not_true] <;>
          first
          | refine' ⟨c, _⟩
          | refine' ⟨d, _⟩
          | refine' ⟨e, _⟩ <;>
        simp [*, pair_comm, insert_comm]
    · rintro ⟨hab, c, hac, hbc, rfl⟩
      refine' ⟨⟨a, b, c, _⟩, _⟩ <;> simp [*]
  constructor
  · rw [Sym2.forall]
    rintro hG a b hab
    simp only [Sym2.isDiag_iff_proj_eq] at hab
    rw [this _ _ (sym2.mk_is_diag_iff.not.2 hab)]
    rintro _ ⟨hab, c, hac, hbc, rfl⟩ _ ⟨-, d, had, hbd, rfl⟩
    refine' hG.eq _ _ (Set.Nontrivial.not_subsingleton ⟨a, _, b, _, hab.ne⟩) <;>
      simp [is_3_clique_triple_iff, *]
  · simp only [edge_disjoint_triangles, is_3_clique_iff, Set.Pairwise, mem_clique_set_iff, Ne.def,
      forall_exists_index, and_imp, ← @Set.not_nontrivial_iff _ (_ ∩ _), not_imp_not,
      Set.Nontrivial, Set.mem_inter_iff, mem_coe]
    rintro hG _ a b c hab hac hbc rfl _ d e f hde hdf hef rfl g hg₁ hg₂ h hh₁ hh₂ hgh
    refine' hG (sym2.mk_is_diag_iff.not.2 hgh) _ _ <;> simp [is_3_clique_triple_iff, *]

alias ⟨edge_disjoint_triangles.mem_sym2_subsingleton, _⟩ :=
  edge_disjoint_triangles_iff_mem_sym2_subsingleton

variable [Fintype α] [DecidableRel G.Adj]

instance : Decidable G.EdgeDisjointTriangles :=
  decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y => (x ∩ y).card ≤ 1) <| by
    simpa only [coe_clique_finset, edge_disjoint_triangles, Finset.card_le_one, ← coe_inter]

instance : Decidable G.LocallyLinear :=
  And.decidable

theorem EdgeDisjointTriangles.card_edgeFinset_le (hG : G.EdgeDisjointTriangles) :
    3 * (G.cliqueFinset 3).card ≤ G.edgeFinset.card := by
  rw [mul_comm, ← mul_one G.edge_finset.card]
  refine' card_mul_le_card_mul (fun s e => e ∈ s.Sym2) _ fun e he => _
  · simp only [is_3_clique_iff, mem_clique_finset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : Finset.card ({⟦(a, b)⟧, ⟦(a, c)⟧, ⟦(b, c)⟧} : Finset <| Sym2 α) = 3 := by
      refine' card_eq_three.2 ⟨_, _, _, _, _, _, rfl⟩ <;> simp [hab.ne, hac.ne, hbc.ne]
    rw [← this]
    refine' card_mono _
    simp [insert_subset, *]
  ·
    simpa only [card_le_one, mem_bipartite_below, and_imp, Set.Subsingleton, Set.mem_sep_iff,
      mem_clique_finset_iff, mem_clique_set_iff] using
      hG.mem_sym2_subsingleton (G.not_is_diag_of_mem_edge_set <| mem_edge_finset.1 he)

theorem LocallyLinear.card_edgeFinset (hG : G.LocallyLinear) :
    G.edgeFinset.card = 3 * (G.cliqueFinset 3).card := by
  refine' hG.edge_disjoint_triangles.card_edge_finset_le.antisymm' _
  rw [← mul_comm, ← mul_one (Finset.card _)]
  refine' card_mul_le_card_mul (fun e s => e ∈ s.Sym2) _ _
  · simpa [Sym2.forall, Nat.succ_le_iff, card_pos, Finset.Nonempty] using hG.2
  simp only [mem_clique_finset_iff, is_3_clique_iff, forall_exists_index, and_imp]
  rintro _ a b c hab hac hbc rfl
  refine' (card_mono _).trans _
  · exact {⟦(a, b)⟧, ⟦(a, c)⟧, ⟦(b, c)⟧}
  · simp only [subset_iff, Sym2.forall, mem_sym2_iff, le_eq_subset, mem_bipartite_below, mem_insert,
      mem_edge_finset, mem_singleton, and_imp, mem_edge_set, Sym2.mem_iff, forall_eq_or_imp,
      forall_eq, Quotient.eq', Sym2.rel_iff]
    rintro d e hde (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp_all
  ·
    exact
      (card_insert_le _ _).trans
        (succ_le_succ <| (card_insert_le _ _).trans_eq <| by rw [card_singleton])

end LocallyLinear

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] [DecidableRel H.Adj]

@[simp]
theorem farFromTriangleFree_of_nonpos (hε : ε ≤ 0) : G.FarFromTriangleFree ε := fun H _ _ =>
  (mul_nonpos_of_nonpos_of_nonneg hε <| Nat.cast_nonneg _).trans <| Nat.cast_nonneg _

private theorem far_from_triangle_free_of_disjoint_triangles_aux {tris : Finset (Finset α)}
    (htris : tris ⊆ G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y => (x ∩ y : Set α).Subsingleton) (hHG : H ≤ G)
    (hH : H.CliqueFree 3) : tris.card ≤ G.edgeFinset.card - H.edgeFinset.card := by
  rw [← card_sdiff (edge_finset_mono hHG), ← card_attach]
  by_contra! hG
  have :
    ∀ ⦃t⦄, t ∈ tris → ∃ x y, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ ⟦(x, y)⟧ ∈ G.edge_finset \ H.edge_finset := by
    intro t ht
    by_contra! h
    refine' hH t _
    simp only [not_and, mem_sdiff, Classical.not_not, mem_edge_finset, mem_edge_set] at h
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := is_3_clique_iff.1 (G.mem_clique_finset_iff.1 <| htris ht)
    rw [is_3_clique_triple_iff]
    refine' ⟨h _ _ _ _ xy.ne xy, h _ _ _ _ xz.ne xz, h _ _ _ _ yz.ne yz⟩ <;> simp
  choose fx fy hfx hfy hfne fmem using this
  let f : { x // x ∈ tris } → Sym2 α := fun t => ⟦(fx t.2, fy t.2)⟧
  have hf : ∀ x, x ∈ tris.attach → f x ∈ G.edge_finset \ H.edge_finset := fun x hx => fmem _
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : ⟦_⟧ = ⟦_⟧⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hG hf
  dsimp at t
  have i := pd ht₁ ht₂ (subtype.val_injective.ne tne)
  rw [Sym2.eq_iff] at t
  cases t
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfx ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfy ht₂⟩)
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfy ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfx ht₂⟩)

/-- If there are `ε * (card α)^2` disjoint triangles, then the graph is `ε`-far from being
triangle-free. -/
theorem farFromTriangleFree_of_disjoint_triangles (tris : Finset (Finset α))
    (htris : tris ⊆ G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y => (x ∩ y : Set α).Subsingleton)
    (tris_big : ε * (card α ^ 2 : ℕ) ≤ tris.card) : G.FarFromTriangleFree ε := by
  rw [far_from_triangle_free_iff]
  intro H _ hG hH
  sorry

-- rw ←nat.cast_sub (card_le_of_subset $ edge_finset_mono hG),
-- exact tris_big.trans
--   (nat.cast_le.2 $ far_from_triangle_free_of_disjoint_triangles_aux htris pd hG hH),
protected theorem EdgeDisjointTriangles.farFromTriangleFree (hG : G.EdgeDisjointTriangles)
    (tris_big : ε * (card α ^ 2 : ℕ) ≤ (G.cliqueFinset 3).card) : G.FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles _ Subset.rfl (by simpa using hG) tris_big

variable [Nonempty α]

theorem FarFromTriangleFree.lt_half (hG : G.FarFromTriangleFree ε) : ε < 2⁻¹ := by
  by_contra! hε
  have := hG.le_card_sub_card bot_le (clique_free_bot <| by norm_num)
  simp only [Set.toFinset_card (edge_set ⊥), Fintype.card_ofFinset, edge_set_bot, cast_zero,
    Finset.card_empty, tsub_zero] at this
  have hε₀ : 0 < ε := hε.trans_lt' (by norm_num)
  rw [inv_pos_le_iff_one_le_mul (zero_lt_two' 𝕜)] at hε
  refine' (this.trans <| le_mul_of_one_le_left (by positivity) hε).not_lt _
  rw [mul_assoc, mul_lt_mul_left hε₀]
  norm_cast
  sorry

-- refine (mul_le_mul_left' (card_mono $ edge_finset_mono le_top) _).trans_lt _,
-- rw [edge_finset_top, filter_not, card_sdiff (subset_univ _), card_univ, sym2.card],
-- simp_rw [sym2.is_diag_iff_mem_range_diag, univ_filter_mem_range, mul_tsub,
--   nat.mul_div_cancel' (card α).even_mul_succ_self.two_dvd],
-- rw [card_image_of_injective _ sym2.diag_injective, card_univ, mul_add_one, two_mul, sq,
--   add_tsub_add_eq_tsub_right],
-- exact tsub_lt_self (mul_pos fintype.card_pos fintype.card_pos) fintype.card_pos,
theorem FarFromTriangleFree.lt_one (hG : G.FarFromTriangleFree ε) : ε < 1 :=
  hG.lt_half.trans <| by norm_num

end SimpleGraph
