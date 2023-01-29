/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import mathlib.combinatorics.simple_graph.subgraph
import mathlib.data.sym.sym2

/-!
# Containment of graphs

This file defines graph containment.

A graph is said to contain another if one of its subgraphs is isomorphic to it.
-/

open function
open_locale big_operators classical

namespace simple_graph
variables {α β γ : Type*} {G G₁ G₂ G₃ : simple_graph α} {H : simple_graph β} {I : simple_graph γ}

/-- A simple graph `G` is contained in a simple graph `H` if there exists a subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊑ H`. -/
def is_contained (G : simple_graph α) (H : simple_graph β) : Prop := ∃ f : G →g H, injective f

infix ` ⊑ `:50 := simple_graph.is_contained

lemma is_contained_of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨hom_of_le h, injective_id⟩
protected lemma iso.is_contained (e : G ≃g H) : G ⊑ H := ⟨e, e.injective⟩
protected lemma iso.is_contained' (e : G ≃g H) : H ⊑ G := e.symm.is_contained
lemma subgraph.coe_is_contained (G' : G.subgraph) : G'.coe ⊑ G := ⟨G'.hom, subtype.val_injective⟩

@[refl] lemma is_contained_refl (G : simple_graph α) : G ⊑ G := is_contained_of_le le_rfl
lemma is_contained_rfl : G ⊑ G := is_contained_refl _

lemma is_contained.trans : G ⊑ H → H ⊑ I → G ⊑ I :=
by { rintro ⟨f, hf⟩ ⟨g, hg⟩, exact ⟨g.comp f, hg.comp hf⟩ }

lemma is_contained.mono_left (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ⊑ G₃) : G₁ ⊑ G₃ :=
(is_contained_of_le h₁₂).trans h₂₃

lemma is_contained.mono_right (h₁₂ : G₁ ⊑ G₂) (h₂₃ : G₂ ≤ G₃) : G₁ ⊑ G₃ :=
h₁₂.trans $ is_contained_of_le h₂₃

alias is_contained.mono_right ← is_contained.trans_le

lemma is_contained_of_is_empty [is_empty α] : G ⊑ H :=
⟨{ to_fun := is_empty_elim, map_rel' := is_empty_elim }, is_empty_elim⟩

lemma bot_is_contained (f : α ↪ β) : (⊥ : simple_graph α) ⊑ H :=
⟨{ to_fun := f, map_rel' := λ _ _, false.elim }, f.injective⟩

lemma is_contained_iff_exists_subgraph : G ⊑ H ↔ ∃ H' : H.subgraph, nonempty $ G ≃g H'.coe :=
begin
  split,
  { rintro ⟨f, hf⟩,
    exact ⟨subgraph.map f ⊤, ⟨(subgraph.iso_map _ hf _).comp subgraph.top_iso.symm⟩⟩ },
  { rintro ⟨H', ⟨e⟩⟩,
    exact e.is_contained.trans H'.coe_is_contained }
end

private lemma aux (hG : G ≠ ⊥) {H' : H.subgraph} (f : G ≃g H'.coe) : H'.edge_set.nonempty :=
begin
  obtain ⟨e, he⟩ := nonempty_edge_set.2 hG,
  rw ←subgraph.image_coe_edge_set_coe,
  exact set.nonempty.image _ ⟨sym2.map f e, f.map_mem_edge_set_iff.2 he⟩,
end

/-- `G.kill H` is a subgraph of `H` where an edge from every subgraph isomorphic to `G` was removed.
As such, it is a big subgraph of `H` that does not contain any subgraph isomorphic to `G`.
-/
noncomputable def kill (G : simple_graph α) (H : simple_graph β) : simple_graph β :=
if hG : G = ⊥ then H else H.delete_edges $ ⋃ (H' : H.subgraph) (f : G ≃g H'.coe), {(aux hG f).some}

lemma kill_le : G.kill H ≤ H := by { rw kill, split_ifs, exacts [le_rfl, delete_edges_le _ _] }

@[simp] lemma bot_kill (H : simple_graph β) : (⊥ : simple_graph α).kill H = H := dif_pos rfl

lemma kill_eq_right (hG : G ≠ ⊥) : G.kill H = H ↔ ¬ G ⊑ H :=
begin
  rw [kill, dif_neg hG],
  simp only [set.disjoint_left, is_contained_iff_exists_subgraph, @forall_swap _ H.subgraph,
    set.Union_singleton_eq_range, delete_edges_eq, set.mem_Union, set.mem_range, not_exists,
    not_nonempty_iff],
  exact forall_congr (λ H', ⟨λ h,
    ⟨λ f, h _ (subgraph.edge_set_subset _ $ (aux hG f).some_spec) f rfl⟩, λ h _ _, h.elim⟩),
end

lemma kill_of_not_is_contained (hGH : ¬ G ⊑ H) : G.kill H = H :=
begin
  obtain rfl | hG := eq_or_ne G ⊥,
  { exact bot_kill _ },
  { exact (kill_eq_right hG).2 hGH }
end

lemma not_is_contained_kill (hG : G ≠ ⊥) : ¬ G ⊑ G.kill H :=
begin
  rw [kill, dif_neg hG, delete_edges_eq_sdiff_from_edge_set, is_contained_iff_exists_subgraph],
  rintro ⟨H', ⟨f⟩⟩,
  have hH' : (H'.map $ hom_of_le (sdiff_le : H \ _ ≤ H)).edge_set.nonempty,
  { rw subgraph.edge_set_map,
    exact (aux hG f).image _ },
  set e := hH'.some with he,
  have : e ∈ _ := hH'.some_spec,
  clear_value e,
  rw ←subgraph.image_coe_edge_set_coe at this,
  subst he,
  obtain ⟨e, he₀, he₁⟩ := this,
  let e' : sym2 H'.verts := sym2.map (subgraph.iso_map (hom_of_le _) injective_id _).symm e,
  have he' : e' ∈ H'.coe.edge_set := (iso.map_mem_edge_set_iff _).2 he₀,
  rw subgraph.edge_set_coe at he',
  have := subgraph.edge_set_subset _ he',
  simp only [edge_set_sdiff, edge_set_from_edge_set, edge_set_sdiff_sdiff_is_diag, set.mem_diff,
    set.mem_Union, not_exists] at this,
  refine this.2 (H'.map $ hom_of_le sdiff_le)
    ((subgraph.iso_map (hom_of_le _) injective_id _).comp f) _,
  rw [sym2.map_map, set.mem_singleton_iff, ←he₁],
  congr' 1 with x,
  refine congr_arg coe (equiv.set.image_symm_apply _ _ injective_id _ _),
  simpa using x.2,
end

variables [fintype H.edge_set]

noncomputable instance kill.edge_set.fintype : fintype (G.kill H).edge_set :=
fintype.of_injective (set.inclusion $ edge_set_mono kill_le) $ set.inclusion_injective _

end simple_graph
