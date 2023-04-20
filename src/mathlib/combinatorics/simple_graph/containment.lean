/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.basic
import mathlib.combinatorics.simple_graph.subgraph
import mathlib.data.fintype.basic
import mathlib.data.sym.sym2

/-!
# Containment of graphs

This file defines graph containment.

For two simple graph `G` and `H`, a *copy* of `G` in `H` is a (not necessarily induced) subgraph of
`H` isomorphic to `G`.

If there exists a copy of `G` in `H`, we say that `H` *contains* `G`. This is equivalent to saying
that there is an injective graph homomorphism `G → H` them (this is **not** the same as a graph
embedding, as we do not require the subgraph to be induced).

If there exists an induced copy of `G` in `H`, we say that `H` *inducingly contains* `G`. This is
equivalent to saying that there is a graph embedding `G ↪ H`.

## Main declarations

* `simple_graph.is_contained G H` : `G` is contained in `H`.
* `simple_graph.is_ind_contained G H` : `G` is contained as an induced subgraph in `H`.
* `simple_graph.copy_count G H`: Number of copies `G` in `H`.
* `simple_graph.kill G H`: Subgraph of `H` that does not contain `G`. Obtained by arbitrarily
  removing an edge from each copy of `G` in `H`.

## Notation

The following notation is declared in locale `simple_graph`:
* `G ⊑ H` for `simple_graph.is_contained G H`.
* `G ⊴ H` for `simple_graph.is_ind_contained G H`.
-/

open finset function
open_locale big_operators classical

namespace simple_graph
variables {α β γ : Type*} {G G₁ G₂ G₃ : simple_graph α} {H : simple_graph β} {I : simple_graph γ}

/-!
### Containment

A graph `H` *contains* a graph `G` if there is some injective graph homomorphism `G → H`. This
amounts to `H` having a (not necessarily induced) subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊑ H` (`\squ`).
-/

/-- A simple graph `G` is contained in a simple graph `H` if there exists a subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊑ H`. -/
def is_contained (G : simple_graph α) (H : simple_graph β) : Prop := ∃ f : G →g H, injective f

localized "infix ` ⊑ `:50 := simple_graph.is_contained" in simple_graph

lemma is_contained_of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨hom_of_le h, injective_id⟩
protected lemma iso.is_contained (e : G ≃g H) : G ⊑ H := ⟨e, e.injective⟩
protected lemma iso.is_contained' (e : G ≃g H) : H ⊑ G := e.symm.is_contained
lemma subgraph.coe_is_contained (G' : G.subgraph) : G'.coe ⊑ G := ⟨G'.hom, subtype.val_injective⟩

@[refl] lemma is_contained_refl (G : simple_graph α) : G ⊑ G := is_contained_of_le le_rfl
lemma is_contained_rfl : G ⊑ G := is_contained_refl _

lemma is_contained.trans : G ⊑ H → H ⊑ I → G ⊑ I := λ ⟨f, hf⟩ ⟨g, hg⟩, ⟨g.comp f, hg.comp hf⟩

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

alias is_contained_iff_exists_subgraph ↔ is_contained.exists_subgraph _

/-!
### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊴ H` (`\triangle_left_eq`).
-/

/-- A simple graph `G` is contained in a simple graph `H` if there exists an induced subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊴ H`. -/
def is_ind_contained (G : simple_graph α) (H : simple_graph β) : Prop := nonempty (G ↪g H)

localized "infix ` ⊴ `:50 := simple_graph.is_ind_contained" in simple_graph

protected lemma is_ind_contained.is_contained : G₁ ⊴ G₂ → G₁ ⊑ G₂ := λ ⟨f⟩, ⟨f, f.injective⟩
protected lemma iso.is_ind_contained (e : G ≃g H) : G ⊴ H := ⟨e⟩
protected lemma iso.is_ind_contained' (e : G ≃g H) : H ⊴ G := e.symm.is_ind_contained
protected lemma subgraph.is_induced'.is_ind_contained {G' : G.subgraph} (hG' : G'.is_induced') :
  G'.coe ⊴ G :=
⟨{ to_fun := coe,
  inj' := subtype.coe_injective,
  map_rel_iff' := λ a b, hG'.adj.symm }⟩

@[refl] lemma is_ind_contained_refl (G : simple_graph α) : G ⊴ G := ⟨embedding.refl⟩
lemma is_ind_contained_rfl : G ⊴ G := is_ind_contained_refl _

lemma is_ind_contained.trans : G ⊴ H → H ⊴ I → G ⊴ I := λ ⟨f⟩ ⟨g⟩, ⟨g.comp f⟩

lemma is_ind_contained_of_is_empty [is_empty α] : G ⊴ H :=
⟨{ to_fun := is_empty_elim, inj' := is_empty_elim, map_rel_iff' := is_empty_elim }⟩

lemma is_ind_contained_iff_exists_subgraph :
  G ⊴ H ↔ ∃ (H' : H.subgraph) (e : G ≃g H'.coe), H'.is_induced' :=
begin
  split,
  { rintro ⟨f⟩,
    refine ⟨subgraph.map f.to_hom ⊤, (subgraph.iso_map f.to_hom f.injective _).comp
      subgraph.top_iso.symm, _⟩,
    rintro _ _ ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    simp [relation.map_apply_apply, f.injective] },
  { rintro ⟨H', e, hH'⟩,
    exact e.is_ind_contained.trans hH'.is_ind_contained }
end

alias is_ind_contained_iff_exists_subgraph ↔ is_ind_contained.exists_subgraph _

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.
-/

section copy_count
variables [fintype β]

/-- `G.copy_count H` is the number of unlabelled copies of `G` in `H`.
See `simple_graph.labelled_copy_count` for the number of labelled copies. -/
noncomputable def copy_count (G : simple_graph α) (H : simple_graph β) : ℕ :=
(univ.filter $ λ H' : H.subgraph, nonempty (G ≃g H'.coe)).card

@[simp] lemma copy_count_bot (H : simple_graph β) : copy_count (⊥ : simple_graph β) H = 1 :=
begin
  rw copy_count,
  convert card_singleton
    ({ verts := set.univ,
       adj := ⊥,
       adj_sub := λ _ _, false.elim,
       edge_vert := λ _ _, false.elim } : H.subgraph),
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, subgraph.coe_bot, true_and,
    nonempty.forall],
  refine ⟨⟨⟨(equiv.set.univ _).symm, by simp only [Prop.bot_eq_false, subgraph.coe_adj,
    pi.bot_apply, bot_adj, iff_self, forall_2_true_iff]⟩⟩, λ H' e, subgraph.ext _ _
    ((set_fintype_card_eq_univ_iff _).1 $ fintype.card_congr e.to_equiv.symm) _⟩,
  ext a b,
  simp only [Prop.bot_eq_false, pi.bot_apply, iff_false],
  exact λ hab, e.symm.map_rel_iff.2 hab.coe,
end

@[simp] lemma copy_count_of_is_empty [is_empty α] (G : simple_graph α) (H : simple_graph β) :
  G.copy_count H = 1 :=
begin
  rw copy_count,
  convert card_singleton (⊥ : H.subgraph),
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, subgraph.coe_bot, true_and,
    nonempty.forall, subsingleton.elim G ⊥],
  haveI : is_empty (⊥ : H.subgraph).verts := by simp,
  refine ⟨⟨⟨⟨is_empty_elim, is_empty_elim, is_empty_elim, is_empty_elim⟩, is_empty_elim⟩⟩,
    λ H' e, subgraph.ext _ _ _ $ funext₂ $ λ a b, _⟩,
  { simpa [set.eq_empty_iff_forall_not_mem, filter_eq_empty_iff]
    using fintype.card_congr e.to_equiv.symm },
  { simp only [subgraph.not_bot_adj, eq_iff_iff, iff_false],
    exact λ hab, e.symm.map_rel_iff.2 hab.coe }
end

@[simp] lemma copy_count_eq_zero : G.copy_count H = 0 ↔ ¬ G ⊑ H :=
by simp [copy_count, is_contained_iff_exists_subgraph, card_pos, filter_eq_empty_iff]

@[simp] lemma copy_count_pos : 0 < G.copy_count H ↔ G ⊑ H :=
by simp [copy_count, is_contained_iff_exists_subgraph, card_pos, filter_nonempty_iff]

end copy_count

section labelled_copy_count
variables [fintype α] [fintype β]

/-- `G.labelled_copy_count H` is the number of labelled copies of `G` in `H`. See `simple_graph.copy_count` for the number of unlabelled copies. -/
noncomputable def labelled_copy_count (G : simple_graph α) (H : simple_graph β) : ℕ :=
by classical; exact fintype.card {f : G →g H // injective f}

@[simp] lemma labelled_copy_count_of_is_empty [is_empty α] (G : simple_graph α)
  (H : simple_graph β) :
  G.labelled_copy_count H = 1 :=
begin
  classical,
  haveI : unique {f : G →g H // injective f} :=
  { default := ⟨default, is_empty_elim⟩,
    uniq := λ _, subsingleton.elim _ _ },
  rw [labelled_copy_count, fintype.card_unique],
end

@[simp] lemma labelled_copy_count_eq_zero : G.labelled_copy_count H = 0 ↔ ¬ G ⊑ H :=
by simp [labelled_copy_count, is_contained, fintype.card_eq_zero_iff]

@[simp] lemma labelled_copy_count_pos : 0 < G.labelled_copy_count H ↔ G ⊑ H :=
by simp [labelled_copy_count, is_contained, fintype.card_pos_iff]

/-- There's more labelled copies of `H` of-`G` than unlabelled ones. -/
lemma copy_count_le_labelled_copy_count : G.copy_count H ≤ G.labelled_copy_count H :=
begin
  rw [copy_count, ←fintype.card_coe],
  refine fintype.card_le_of_injective (λ H', ⟨H'.val.hom.comp (mem_filter.1 H'.2).2.some.to_hom,
    subtype.coe_injective.comp (mem_filter.1 H'.2).2.some.injective⟩) _,
  sorry,
end

end labelled_copy_count

/-!
### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

`simple_graph.kill G H` is a subgraph of `H` where an edge was removed from each copy of `G` in `H`.
By construction, it doesn't contain `G` and has at most the number of copies of `G` edges less than
`H`
-/

private lemma aux (hG : G ≠ ⊥) {H' : H.subgraph} : nonempty (G ≃g H'.coe) → H'.edge_set.nonempty :=
begin
  obtain ⟨e, he⟩ := nonempty_edge_set.2 hG,
  rw ←subgraph.image_coe_edge_set_coe,
  exact λ ⟨f⟩, set.nonempty.image _ ⟨_, f.map_mem_edge_set_iff.2 he⟩,
end

/-- `G.kill H` is a subgraph of `H` where an edge from every subgraph isomorphic to `G` was removed.
As such, it is a big subgraph of `H` that does not contain any subgraph isomorphic to `G`, unless
`G` had no edges to start with. -/
@[irreducible]
noncomputable def kill (G : simple_graph α) (H : simple_graph β) : simple_graph β :=
if hG : G = ⊥ then H else
  H.delete_edges $ ⋃ (H' : H.subgraph) (hH' : nonempty (G ≃g H'.coe)), {(aux hG hH').some}

local attribute [semireducible] kill

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a subgraph of `H`. -/
lemma kill_le : G.kill H ≤ H := by { rw kill, split_ifs, exacts [le_rfl, delete_edges_le _ _] }

@[simp] lemma bot_kill (H : simple_graph β) : (⊥ : simple_graph α).kill H = H := dif_pos rfl

private lemma kill_of_ne_bot (hG : G ≠ ⊥) (H : simple_graph β) :
  G.kill H =
    H.delete_edges (⋃ (H' : H.subgraph) (hH' : nonempty (G ≃g H'.coe)), {(aux hG hH').some}) :=
dif_neg hG

lemma kill_eq_right (hG : G ≠ ⊥) : G.kill H = H ↔ ¬ G ⊑ H :=
begin
  simp only [kill_of_ne_bot hG, set.disjoint_left, is_contained_iff_exists_subgraph,
    @forall_swap _ H.subgraph, set.Union_singleton_eq_range, delete_edges_eq, set.mem_Union,
    set.mem_range, not_exists, not_nonempty_iff, nonempty.forall],
  exact forall_congr (λ H', ⟨λ h,
    ⟨λ f, h _ (subgraph.edge_set_subset _ $ (aux hG ⟨f⟩).some_spec) f rfl⟩, λ h _ _, h.elim⟩),
end

lemma kill_of_not_is_contained (hGH : ¬ G ⊑ H) : G.kill H = H :=
begin
  obtain rfl | hG := eq_or_ne G ⊥,
  { exact bot_kill _ },
  { exact (kill_eq_right hG).2 hGH }
end

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a graph that doesn't
contain `G`. -/
lemma not_is_contained_kill (hG : G ≠ ⊥) : ¬ G ⊑ G.kill H :=
begin
  rw [kill_of_ne_bot hG, delete_edges_eq_sdiff_from_edge_set, is_contained_iff_exists_subgraph],
  rintro ⟨H', hGH'⟩,
  have hH' : (H'.map $ hom_of_le (sdiff_le : H \ _ ≤ H)).edge_set.nonempty,
  { rw subgraph.edge_set_map,
    exact (aux hG hGH').image _ },
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
    ⟨(subgraph.iso_map (hom_of_le _) injective_id _).comp hGH'.some⟩ _,
  rw [sym2.map_map, set.mem_singleton_iff, ←he₁],
  congr' 1 with x,
  refine congr_arg coe (equiv.set.image_symm_apply _ _ injective_id _ _),
  simpa using x.2,
end

variables [fintype H.edge_set]

noncomputable instance kill.edge_set.fintype : fintype (G.kill H).edge_set :=
fintype.of_injective (set.inclusion $ edge_set_mono kill_le) $ set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edge_finset_kill [fintype β] :
  H.edge_finset.card - G.copy_count H ≤ (G.kill H).edge_finset.card :=
begin
  obtain rfl | hG := eq_or_ne G ⊥,
  { simp },
  simp only [kill_of_ne_bot, hG, ne.def, not_false_iff, set.Union_singleton_eq_range,
    set.to_finset_card, fintype.card_of_finset, filter_congr_decidable, edge_set_delete_edges],
  rw [←set.to_finset_card, ←edge_finset, copy_count, ←card_subtype, subtype_univ],
  refine (tsub_le_tsub_left (card_image_le.trans_eq' $ congr_arg card $ set.to_finset_range $
    λ H' : {H' : H.subgraph // nonempty (G ≃g H'.coe)}, (aux hG H'.2).some) _).trans
    ((le_card_sdiff _ _).trans_eq $ congr_arg card $ coe_injective _),
  simp only [set.diff_eq, ←set.Union_singleton_eq_range, coe_sdiff, set.coe_to_finset, coe_filter,
    set.sep_mem_eq, set.Union_subtype],
end

end simple_graph
