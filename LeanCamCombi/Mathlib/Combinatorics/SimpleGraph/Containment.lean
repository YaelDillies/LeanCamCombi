/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.BigOperators.Basic
import Project.Mathlib.Combinatorics.SimpleGraph.Subgraph
import Project.Mathlib.Data.Fintype.Basic
import Project.Mathlib.Data.Sym.Sym2

#align_import mathlib.combinatorics.simple_graph.containment

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


open Finset Function

open scoped BigOperators Classical

namespace SimpleGraph

variable {α β γ : Type _} {G G₁ G₂ G₃ : SimpleGraph α} {H : SimpleGraph β} {I : SimpleGraph γ}

/-!
### Containment

A graph `H` *contains* a graph `G` if there is some injective graph homomorphism `G → H`. This
amounts to `H` having a (not necessarily induced) subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊑ H` (`\squ`).
-/


/-- A simple graph `G` is contained in a simple graph `H` if there exists a subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊑ H`. -/
def IsContained (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ f : G →g H, Injective f

scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

theorem isContained_of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ :=
  ⟨homOfLe h, injective_id⟩

protected theorem Iso.isContained (e : G ≃g H) : G ⊑ H :=
  ⟨e, e.Injective⟩

protected theorem Iso.is_contained' (e : G ≃g H) : H ⊑ G :=
  e.symm.IsContained

theorem Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G :=
  ⟨G'.hom, Subtype.val_injective⟩

@[refl]
theorem isContained_refl (G : SimpleGraph α) : G ⊑ G :=
  isContained_of_le le_rfl

theorem isContained_rfl : G ⊑ G :=
  isContained_refl _

theorem IsContained.trans : G ⊑ H → H ⊑ I → G ⊑ I := fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g.comp f, hg.comp hf⟩

theorem IsContained.mono_left (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ⊑ G₃) : G₁ ⊑ G₃ :=
  (isContained_of_le h₁₂).trans h₂₃

theorem IsContained.mono_right (h₁₂ : G₁ ⊑ G₂) (h₂₃ : G₂ ≤ G₃) : G₁ ⊑ G₃ :=
  h₁₂.trans <| isContained_of_le h₂₃

alias is_contained.trans_le := is_contained.mono_right

theorem isContained_of_isEmpty [IsEmpty α] : G ⊑ H :=
  ⟨{  toFun := isEmptyElim
      map_rel' := isEmptyElim }, isEmptyElim⟩

theorem bot_isContained (f : α ↪ β) : (⊥ : SimpleGraph α) ⊑ H :=
  ⟨{  toFun := f
      map_rel' := fun _ _ => False.elim }, f.Injective⟩

theorem isContained_iff_exists_subgraph : G ⊑ H ↔ ∃ H' : H.Subgraph, Nonempty <| G ≃g H'.coe :=
  by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨subgraph.map f ⊤, ⟨(subgraph.iso_map _ hf _).comp subgraph.top_iso.symm⟩⟩
  · rintro ⟨H', ⟨e⟩⟩
    exact e.is_contained.trans H'.coe_is_contained

alias ⟨is_contained.exists_subgraph, _⟩ := is_contained_iff_exists_subgraph

/-!
### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊴ H` (`\triangle_left_eq`).
-/


/-- A simple graph `G` is contained in a simple graph `H` if there exists an induced subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊴ H`. -/
def IsIndContained (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  Nonempty (G ↪g H)

scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

protected theorem IsIndContained.isContained : G₁ ⊴ G₂ → G₁ ⊑ G₂ := fun ⟨f⟩ => ⟨f, f.Injective⟩

protected theorem Iso.isIndContained (e : G ≃g H) : G ⊴ H :=
  ⟨e⟩

protected theorem Iso.is_ind_contained' (e : G ≃g H) : H ⊴ G :=
  e.symm.IsIndContained

protected theorem Subgraph.IsInduced'.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced') :
    G'.coe ⊴ G :=
  ⟨{  toFun := coe
      inj' := Subtype.coe_injective
      map_rel_iff' := fun a b => hG'.Adj.symm }⟩

@[refl]
theorem isIndContained_refl (G : SimpleGraph α) : G ⊴ G :=
  ⟨Embedding.refl⟩

theorem isIndContained_rfl : G ⊴ G :=
  isIndContained_refl _

theorem IsIndContained.trans : G ⊴ H → H ⊴ I → G ⊴ I := fun ⟨f⟩ ⟨g⟩ => ⟨g.comp f⟩

theorem isIndContained_of_isEmpty [IsEmpty α] : G ⊴ H :=
  ⟨{  toFun := isEmptyElim
      inj' := isEmptyElim
      map_rel_iff' := isEmptyElim }⟩

theorem isIndContained_iff_exists_subgraph :
    G ⊴ H ↔ ∃ (H' : H.Subgraph) (e : G ≃g H'.coe), H'.IsInduced' :=
  by
  constructor
  · rintro ⟨f⟩
    refine'
      ⟨subgraph.map f.to_hom ⊤,
        (subgraph.iso_map f.to_hom f.injective _).comp subgraph.top_iso.symm, _⟩
    rintro _ _ ⟨a, -, rfl⟩ ⟨b, -, rfl⟩
    simp [Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.is_ind_contained.trans hH'.is_ind_contained

alias ⟨is_ind_contained.exists_subgraph, _⟩ := is_ind_contained_iff_exists_subgraph

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.
-/


section CopyCount

variable [Fintype β]

/-- `G.copy_count H` is the number of unlabelled copies of `G` in `H`.
See `simple_graph.labelled_copy_count` for the number of labelled copies. -/
noncomputable def copyCount (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  (univ.filterₓ fun H' : H.Subgraph => Nonempty (G ≃g H'.coe)).card

@[simp]
theorem copyCount_bot (H : SimpleGraph β) : copyCount (⊥ : SimpleGraph β) H = 1 :=
  by
  rw [copy_count]
  convert
    card_singleton
      ({  verts := Set.univ
          Adj := ⊥
          adj_sub := fun _ _ => False.elim
          edge_vert := fun _ _ => False.elim } : H.subgraph)
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, subgraph.coe_bot, true_and_iff,
    Nonempty.forall]
  refine'
    ⟨⟨⟨(Equiv.Set.univ _).symm, by
          simp only [Prop.bot_eq_false, subgraph.coe_adj, Pi.bot_apply, bot_adj, iff_self_iff,
            forall₂_true_iff]⟩⟩,
      fun H' e =>
      subgraph.ext _ _ ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.to_equiv.symm) _⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false_iff]
  exact fun hab => e.symm.map_rel_iff.2 hab.coe

@[simp]
theorem copyCount_of_isEmpty [IsEmpty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    G.copyCount H = 1 := by
  rw [copy_count]
  convert card_singleton (⊥ : H.subgraph)
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, subgraph.coe_bot, true_and_iff,
    Nonempty.forall, Subsingleton.elim G ⊥]
  haveI : IsEmpty (⊥ : H.subgraph).verts := by simp
  refine'
    ⟨⟨⟨⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩, isEmptyElim⟩⟩, fun H' e =>
      subgraph.ext _ _ _ <| funext₂ fun a b => _⟩
  ·
    simpa [Set.eq_empty_iff_forall_not_mem, filter_eq_empty_iff] using
      Fintype.card_congr e.to_equiv.symm
  · simp only [subgraph.not_bot_adj, eq_iff_iff, iff_false_iff]
    exact fun hab => e.symm.map_rel_iff.2 hab.coe

@[simp]
theorem copyCount_eq_zero : G.copyCount H = 0 ↔ ¬G ⊑ H := by
  simp [copy_count, is_contained_iff_exists_subgraph, card_pos, filter_eq_empty_iff]

@[simp]
theorem copyCount_pos : 0 < G.copyCount H ↔ G ⊑ H := by
  simp [copy_count, is_contained_iff_exists_subgraph, card_pos, filter_nonempty_iff]

end CopyCount

section LabelledCopyCount

variable [Fintype α] [Fintype β]

/--
`G.labelled_copy_count H` is the number of labelled copies of `G` in `H`. See `simple_graph.copy_count` for the number of unlabelled copies. -/
noncomputable def labelledCopyCount (G : SimpleGraph α) (H : SimpleGraph β) : ℕ := by
  classical exact Fintype.card { f : G →g H // injective f }

@[simp]
theorem labelledCopyCount_of_isEmpty [IsEmpty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    G.labelledCopyCount H = 1 := by
  classical
  haveI : Unique { f : G →g H // injective f } :=
    { default := ⟨default, isEmptyElim⟩
      uniq := fun _ => Subsingleton.elim _ _ }
  rw [labelled_copy_count, Fintype.card_unique]

@[simp]
theorem labelledCopyCount_eq_zero : G.labelledCopyCount H = 0 ↔ ¬G ⊑ H := by
  simp [labelled_copy_count, is_contained, Fintype.card_eq_zero_iff]

@[simp]
theorem labelledCopyCount_pos : 0 < G.labelledCopyCount H ↔ G ⊑ H := by
  simp [labelled_copy_count, is_contained, Fintype.card_pos_iff]

/-- There's more labelled copies of `H` of-`G` than unlabelled ones. -/
theorem copyCount_le_labelledCopyCount : G.copyCount H ≤ G.labelledCopyCount H :=
  by
  rw [copy_count, ← Fintype.card_coe]
  refine'
    Fintype.card_le_of_injective
      (fun H' =>
        ⟨H'.val.hom.comp (mem_filter.1 H'.2).2.some.toHom,
          subtype.coe_injective.comp (mem_filter.1 H'.2).2.some.Injective⟩)
      _
  sorry

end LabelledCopyCount

/-!
### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

`simple_graph.kill G H` is a subgraph of `H` where an edge was removed from each copy of `G` in `H`.
By construction, it doesn't contain `G` and has at most the number of copies of `G` edges less than
`H`
-/


private theorem aux (hG : G ≠ ⊥) {H' : H.Subgraph} :
    Nonempty (G ≃g H'.coe) → H'.edgeSetEmbedding.Nonempty :=
  by
  obtain ⟨e, he⟩ := nonempty_edge_set.2 hG
  rw [← subgraph.image_coe_edge_set_coe]
  exact fun ⟨f⟩ => Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

/-- `G.kill H` is a subgraph of `H` where an edge from every subgraph isomorphic to `G` was removed.
As such, it is a big subgraph of `H` that does not contain any subgraph isomorphic to `G`, unless
`G` had no edges to start with. -/
noncomputable irreducible_def kill (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph β :=
  if hG : G = ⊥ then H
  else H.deleteEdges <| ⋃ (H' : H.Subgraph) (hH' : Nonempty (G ≃g H'.coe)), {(aux hG hH').some}

attribute [local semireducible] kill

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a subgraph of `H`. -/
theorem kill_le : G.kill H ≤ H := by rw [kill]; split_ifs; exacts [le_rfl, delete_edges_le _ _]

@[simp]
theorem bot_kill (H : SimpleGraph β) : (⊥ : SimpleGraph α).kill H = H :=
  dif_pos rfl

private theorem kill_of_ne_bot (hG : G ≠ ⊥) (H : SimpleGraph β) :
    G.kill H =
      H.deleteEdges (⋃ (H' : H.Subgraph) (hH' : Nonempty (G ≃g H'.coe)), {(aux hG hH').some}) :=
  dif_neg hG

theorem kill_eq_right (hG : G ≠ ⊥) : G.kill H = H ↔ ¬G ⊑ H :=
  by
  simp only [kill_of_ne_bot hG, Set.disjoint_left, is_contained_iff_exists_subgraph,
    @forall_swap _ H.subgraph, Set.iUnion_singleton_eq_range, delete_edges_eq, Set.mem_iUnion,
    Set.mem_range, not_exists, not_nonempty_iff, Nonempty.forall]
  exact
    forall_congr' fun H' =>
      ⟨fun h => ⟨fun f => h _ (subgraph.edge_set_subset _ <| (aux hG ⟨f⟩).choose_spec) f rfl⟩,
        fun h _ _ => h.elim⟩

theorem kill_of_not_isContained (hGH : ¬G ⊑ H) : G.kill H = H :=
  by
  obtain rfl | hG := eq_or_ne G ⊥
  · exact bot_kill _
  · exact (kill_eq_right hG).2 hGH

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a graph that doesn't
contain `G`. -/
theorem not_isContained_kill (hG : G ≠ ⊥) : ¬G ⊑ G.kill H :=
  by
  rw [kill_of_ne_bot hG, delete_edges_eq_sdiff_from_edge_set, is_contained_iff_exists_subgraph]
  rintro ⟨H', hGH'⟩
  have hH' : (H'.map <| hom_of_le (sdiff_le : H \ _ ≤ H)).edgeSetEmbedding.Nonempty :=
    by
    rw [subgraph.edge_set_map]
    exact (aux hG hGH').image _
  set e := hH'.some with he
  have : e ∈ _ := hH'.some_spec
  clear_value e
  rw [← subgraph.image_coe_edge_set_coe] at this 
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 H'.verts := Sym2.map (subgraph.iso_map (hom_of_le _) injective_id _).symm e
  have he' : e' ∈ H'.coe.edge_set := (iso.map_mem_edge_set_iff _).2 he₀
  rw [subgraph.edge_set_coe] at he' 
  have := subgraph.edge_set_subset _ he'
  simp only [edge_set_sdiff, edge_set_from_edge_set, edge_set_sdiff_sdiff_is_diag, Set.mem_diff,
    Set.mem_iUnion, not_exists] at this 
  refine'
    this.2 (H'.map <| hom_of_le sdiff_le)
      ⟨(subgraph.iso_map (hom_of_le _) injective_id _).comp hGH'.some⟩ _
  rw [Sym2.map_map, Set.mem_singleton_iff, ← he₁]
  congr 1 with x
  refine' congr_arg coe (Equiv.Set.image_symm_apply _ _ injective_id _ _)
  simpa using x.2

variable [Fintype H.edgeSetEmbedding]

noncomputable instance kill.EdgeSet.fintype : Fintype (G.kill H).edgeSetEmbedding :=
  Fintype.ofInjective (Set.inclusion <| edgeSet_mono kill_le) <| Set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
theorem le_card_edgeFinset_kill [Fintype β] :
    H.edgeFinset.card - G.copyCount H ≤ (G.kill H).edgeFinset.card :=
  by
  obtain rfl | hG := eq_or_ne G ⊥
  · simp
  simp only [kill_of_ne_bot, hG, Ne.def, not_false_iff, Set.iUnion_singleton_eq_range,
    Set.toFinset_card, Fintype.card_ofFinset, filter_congr_decidable, edge_set_delete_edges]
  rw [← Set.toFinset_card, ← edge_finset, copy_count, ← card_subtype, subtype_univ]
  refine'
    (tsub_le_tsub_left
          (card_image_le.trans_eq' <|
            congr_arg card <|
              Set.toFinset_range fun H' : { H' : H.subgraph // Nonempty (G ≃g H'.coe) } =>
                (aux hG H'.2).some)
          _).trans
      ((le_card_sdiff _ _).trans_eq <| congr_arg card <| coe_injective _)
  simp only [Set.diff_eq, ← Set.iUnion_singleton_eq_range, coe_sdiff, Set.coe_toFinset, coe_filter,
    Set.sep_mem_eq, Set.iUnion_subtype]

end SimpleGraph

