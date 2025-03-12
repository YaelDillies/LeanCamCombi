/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import LeanCamCombi.Mathlib.Combinatorics.SimpleGraph.Subgraph

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

* `SimpleGraph.Copy A B` is the type of copies of `A` in `B`, implemented as the subtype of
  *injective* homomorphisms.
* `SimpleGraph.IsContained A B`, `A ⊑ B` is the relation that `B` contains a copy of `A`, that
  is, the type of copies of `A` in `B` is nonempty. This is equivalent to the existence of an
  isomorphism from `A` to a subgraph of `B`.

  This is similar to `SimpleGraph.IsSubgraph` except that the simple graphs here need not have the
  same underlying vertex type.
* `SimpleGraph.Free` is the predicate that `B` is `A`-free, that is, `B` does not contain a copy of
  `A`. This is the negation of `SimpleGraph.IsContained` implemented for convenience.

* `SimpleGraph.IsIndContained G H` : `G` is contained as an induced subgraph in `H`.
* `SimpleGraph.copyCount G H`: Number of copies `G` in `H`.
* `SimpleGraph.kill G H`: Subgraph of `H` that does not contain `G`. Obtained by arbitrarily
  removing an edge from each copy of `G` in `H`.

## Notation

The following notation is declared in locale `SimpleGraph`:
* `G ⊑ H` for `SimpleGraph.is_contained G H`.
* `G ⊴ H` for `SimpleGraph.isIndContained G H`.
-/

open Finset Function
open Fintype (card)
open scoped BigOperators Classical

namespace SimpleGraph

variable {V α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph V}
  {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

section Copy

/-- The type of copies as a subtype of *injective* homomorphisms. -/
abbrev Copy (A : SimpleGraph α) (B : SimpleGraph β) :=
  { f : A →g B // Function.Injective f }

/-- An injective homomorphism gives rise to a copy. -/
abbrev Hom.toCopy (f : A →g B) (h : Function.Injective f) : Copy A B := ⟨f, h⟩

/-- An embedding gives rise to a copy. -/
abbrev Embedding.toCopy (f : A ↪g B) : Copy A B := f.toHom.toCopy f.injective

/-- An isomorphism gives rise to a copy. -/
abbrev Iso.toCopy (f : A ≃g B) : Copy A B := f.toEmbedding.toCopy

namespace Copy

/-- A copy gives rise to a homomorphism. -/
abbrev toHom : Copy A B → A →g B := Subtype.val

@[simp] lemma coe_toHom (f : Copy A B) : ⇑f.toHom = f := rfl

lemma injective : (f : Copy A B) → (Function.Injective f.toHom) := Subtype.prop

instance : FunLike (Copy A B) α β where
  coe f := DFunLike.coe f.toHom
  coe_injective' _ _ h := Subtype.val_injective (DFunLike.coe_injective h)

@[simp] lemma coe_toHom_apply (f : Copy A B) (a : α) : ⇑f.toHom a = f a := rfl

/-- A copy induces an embedding of edge sets. -/
def mapEdgeSet (f : Copy A B) : A.edgeSet ↪ B.edgeSet where
  toFun := Hom.mapEdgeSet f.toHom
  inj' := Hom.mapEdgeSet.injective f.toHom f.injective

/-- A copy induces an embedding of neighbor sets. -/
def mapNeighborSet (f : Copy A B) (a : α) :
    A.neighborSet a ↪ B.neighborSet (f a) where
  toFun v := ⟨f v, f.toHom.apply_mem_neighborSet v.prop⟩
  inj' _ _ h := by
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.injective h

/-- A copy gives rise to an embedding of vertex types. -/
def toEmbedding (f : Copy A B) : α ↪ β := ⟨f, f.injective⟩

/-- The identity copy from a simple graph to itself. -/
@[refl] def id (G : SimpleGraph V) : Copy G G := ⟨Hom.id, Function.injective_id⟩

@[simp, norm_cast] lemma coe_id : ⇑(id G) = _root_.id := rfl

/-- The composition of copies is a copy. -/
def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
  use g.toHom.comp f.toHom
  rw [Hom.coe_comp]
  exact Function.Injective.comp g.injective f.injective

@[simp]
theorem comp_apply (g : Copy B C) (f : Copy A B) (a : α) : g.comp f a = g (f a) :=
  RelHom.comp_apply g.toHom f.toHom a

/-- The copy from a subgraph to the supergraph. -/
def ofLE (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) : Copy G₁ G₂ := ⟨Hom.ofLE h, Function.injective_id⟩

@[simp, norm_cast]
theorem coe_comp (g : Copy B C) (f : Copy A B) : ⇑(g.comp f) = g ∘ f := by ext; simp

@[simp, norm_cast] lemma coe_ofLE (h : G₁ ≤ G₂) : ⇑(ofLE G₁ G₂ h) = _root_.id := rfl

@[simp] theorem ofLE_refl : ofLE G G (le_refl G) = id G := by ext; simp

@[simp]
theorem ofLE_comp (h₁₂ : G₁ ≤ G₂) (h₂₃ : G₂ ≤ G₃) :
  (ofLE _ _ h₂₃).comp (ofLE _ _ h₁₂) = ofLE _ _ (h₁₂.trans h₂₃) := by ext; simp

/-- The copy from an induced subgraph to the initial simple graph. -/
def induce (G : SimpleGraph V) (s : Set V) : Copy (G.induce s) G :=
  (Embedding.induce s).toCopy

end Copy

/-- A `Subgraph G` gives rise to a copy from the coercion to `G`. -/
def Subgraph.coeCopy (G' : G.Subgraph) : Copy G'.coe G :=
  G'.hom.toCopy Subgraph.hom.injective

end Copy

section IsContained

/-- The relation `IsContained A B`, `A ⊑ B` says that `B` contains a copy of `A`.

This is equivalent to the existence of an isomorphism from `A` to a subgraph of `B`. -/
abbrev IsContained (A : SimpleGraph α) (B : SimpleGraph β) := Nonempty (Copy A B)

@[inherit_doc] scoped infixl:50 " ⊑ " => SimpleGraph.IsContained

/-- A simple graph contains itself. -/
@[refl] protected theorem IsContained.refl (G : SimpleGraph V) : G ⊑ G := ⟨.id G⟩

protected theorem IsContained.rfl : G ⊑ G := IsContained.refl G

/-- A simple graph contains its subgraphs. -/
theorem isContained_of_le (h : G₁ ≤ G₂) : G₁ ⊑ G₂ := ⟨Copy.ofLE G₁ G₂ h⟩

/-- If `A` contains `B` and `B` contains `C`, then `A` contains `C`. -/
theorem IsContained.trans : A ⊑ B → B ⊑ C → A ⊑ C := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

/-- If `B` contains `C` and `A` contains `B`, then `A` contains `C`. -/
theorem IsContained.trans' : B ⊑ C → A ⊑ B → A ⊑ C := flip IsContained.trans

lemma IsContained.mono_right {B' : SimpleGraph β} (h_isub : A ⊑ B) (h_sub : B ≤ B') : A ⊑ B' :=
  h_isub.trans <| isContained_of_le h_sub

alias IsContained.trans_le := IsContained.mono_right

lemma IsContained.mono_left {A' : SimpleGraph α} (h_sub : A ≤ A') (h_isub : A' ⊑ B) : A ⊑ B :=
  (isContained_of_le h_sub).trans h_isub

alias IsContained.trans_le' := IsContained.mono_left

/-- If `A ≃g B`, then `A` is contained in `C` if and only if `B` is contained in `C`. -/
theorem isContained_congr (e : A ≃g B) : A ⊑ C ↔ B ⊑ C :=
  ⟨.trans ⟨e.symm.toCopy⟩, .trans ⟨e.toCopy⟩⟩

/-- A simple graph having no vertices is contained in any simple graph. -/
lemma IsContained.of_isEmpty [IsEmpty α] : A ⊑ B :=
  ⟨⟨isEmptyElim, fun {a} ↦ isEmptyElim a⟩, isEmptyElim⟩

/-- A simple graph having no edges is contained in any simple graph having sufficent vertices. -/
theorem isContained_of_isEmpty_edgeSet [IsEmpty A.edgeSet] [Fintype α] [Fintype β]
    (h : card α ≤ card β) : A ⊑ B := by
  haveI := Function.Embedding.nonempty_of_card_le h
  let ι : α ↪ β := Classical.arbitrary (α ↪ β)
  exact ⟨⟨ι, isEmptyElim ∘ fun hadj ↦ (⟨s(_, _), hadj⟩ : A.edgeSet)⟩, ι.injective⟩

lemma bot_isContained (f : α ↪ β) : (⊥ : SimpleGraph α) ⊑ B := ⟨⟨f, False.elim⟩, f.injective⟩

protected alias IsContained.bot := bot_isContained

/-- A simple graph `G` contains all `Subgraph G` coercions. -/
lemma Subgraph.coe_isContained (G' : G.Subgraph) : G'.coe ⊑ G := ⟨G'.coeCopy⟩

/-- The isomorphism from `Subgraph A` to its map under a copy `Copy A B`. -/
noncomputable def Subgraph.isoMap (f : Copy A B) (A' : A.Subgraph) :
    A'.coe ≃g (A'.map f.toHom).coe := by
  use Equiv.Set.image f.toHom _ f.injective
  simp_rw [map_verts, Equiv.Set.image_apply, coe_adj, map_adj, Relation.map_apply,
    Function.Injective.eq_iff f.injective, exists_eq_right_right, exists_eq_right, forall_true_iff]

/-- `B` contains `A` if and only if `B` has a subgraph `B'` and `B'` is isomorphic to `A`. -/
theorem isContained_iff_exists_iso_subgraph :
    A ⊑ B ↔ ∃ B' : B.Subgraph, Nonempty (A ≃g B'.coe) :=
  ⟨fun ⟨f⟩ ↦ ⟨Subgraph.map f.toHom ⊤, ⟨(Subgraph.isoMap f ⊤).comp Subgraph.topIso.symm⟩⟩,
    fun ⟨B', ⟨e⟩⟩ ↦ B'.coe_isContained.trans' ⟨e.toCopy⟩⟩

alias ⟨IsContained.exists_iso_subgraph, IsContained.of_exists_iso_subgraph⟩ :=
  isContained_iff_exists_iso_subgraph

end IsContained

section Free

/-- The proposition that a simple graph does not contain a copy of another simple graph. -/
abbrev Free (A : SimpleGraph α) (B : SimpleGraph β) := ¬A ⊑ B

lemma not_free : ¬A.Free B ↔ A ⊑ B := not_not

/-- If `A ≃g B`, then `C` is `A`-free if and only if `C` is `B`-free. -/
theorem free_congr (e : A ≃g B) : A.Free C ↔ B.Free C := by
  rw [not_iff_not]
  exact isContained_congr e

lemma free_bot (h : A ≠ ⊥) : A.Free (⊥ : SimpleGraph β) := by
  rw [← edgeSet_nonempty] at h
  intro ⟨f, hf⟩
  absurd f.map_mem_edgeSet h.choose_spec
  rw [edgeSet_bot]
  exact Set.not_mem_empty (h.choose.map f)

end Free

variable {α β γ : Type*} {G G₁ G₂ G₃ : SimpleGraph α} {H : SimpleGraph β} {I : SimpleGraph γ}

/-!
### Induced containment

A graph `H` *inducingly contains* a graph `G` if there is some graph embedding `G ↪ H`. This amounts
to `H` having an induced subgraph isomorphic to `G`.

We denote "`G` is contained in `H`" by `G ⊴ H` (`\triangle_left_eq`).
-/

/-- A simple graph `G` is contained in a simple graph `H` if there exists an induced subgraph of `H`
isomorphic to `G`. This is denoted by `G ⊴ H`. -/
def IsIndContained (G : SimpleGraph α) (H : SimpleGraph β) : Prop := Nonempty (G ↪g H)

scoped infixl:50 " ⊴ " => SimpleGraph.IsIndContained

protected lemma IsIndContained.isContained : G₁ ⊴ G₂ → G₁ ⊑ G₂ := fun ⟨f⟩ ↦ ⟨f, f.injective⟩
protected lemma Iso.isIndContained (e : G ≃g H) : G ⊴ H := ⟨e⟩
protected lemma Iso.isIndContained' (e : G ≃g H) : H ⊴ G := e.symm.isIndContained

protected lemma Subgraph.IsInduced'.isIndContained {G' : G.Subgraph} (hG' : G'.IsInduced') :
    G'.coe ⊴ G :=
  ⟨{  toFun := (↑)
      inj' := Subtype.coe_injective
      map_rel_iff' := hG'.adj.symm }⟩

@[refl] lemma IsIndContained.refl (G : SimpleGraph α) : G ⊴ G := ⟨Embedding.refl⟩
lemma IsIndContained.rfl : G ⊴ G := .refl _
lemma IsIndContained.trans : G ⊴ H → H ⊴ I → G ⊴ I := fun ⟨f⟩ ⟨g⟩ ↦ ⟨g.comp f⟩

lemma isIndContained_of_isEmpty [IsEmpty α] : G ⊴ H :=
  ⟨{  toFun := isEmptyElim
      inj' := isEmptyElim
      map_rel_iff' := fun {a} ↦ isEmptyElim a }⟩

lemma isIndContained_iff_exists_iso_subgraph :
    G ⊴ H ↔ ∃ (H' : H.Subgraph) (_e : G ≃g H'.coe), H'.IsInduced' := by
  constructor
  · rintro ⟨f⟩
    refine ⟨Subgraph.map f.toHom ⊤,
      (Subgraph.isoMap ⟨f.toHom, f.injective⟩ _).comp Subgraph.topIso.symm, ?_⟩
    rintro _ _ ⟨a, -, rfl⟩ ⟨b, -, rfl⟩
    simp [Relation.map_apply_apply, f.injective]
  · rintro ⟨H', e, hH'⟩
    exact e.isIndContained.trans hH'.isIndContained

alias ⟨IsIndContained.exists_iso_subgraph, IsIndContained.of_exists_iso_subgraph⟩ :=
  isIndContained_iff_exists_iso_subgraph

/-!
### Counting the copies

If `G` and `H` are finite graphs, we can count the number of unlabelled and labelled copies of `G`
in `H`.
-/
section CopyCount
variable [Fintype β]

/-- `G.copyCount H` is the number of unlabelled copies of `G` in `H`.
See `SimpleGraph.labelledCopyCount` for the number of labelled copies. -/
noncomputable def copyCount (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  #{H' : H.Subgraph | Nonempty (G ≃g H'.coe)}

@[simp] lemma copyCount_bot (H : SimpleGraph β) : copyCount (⊥ : SimpleGraph β) H = 1 := by
  rw [copyCount]
  convert
    card_singleton
      ({  verts := Set.univ
          Adj := ⊥
          adj_sub := False.elim
          edge_vert := False.elim } : H.Subgraph)
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, Subgraph.coe_bot, true_and,
    Nonempty.forall]
  refine
    ⟨⟨⟨(Equiv.Set.univ _).symm, by
      simp only [Prop.bot_eq_false, Subgraph.coe_adj, Pi.bot_apply, bot_adj, iff_self,
        forall₂_true_iff]⟩⟩, fun H' e ↦
      Subgraph.ext ((set_fintype_card_eq_univ_iff _).1 <| Fintype.card_congr e.toEquiv.symm) ?_⟩
  ext a b
  simp only [Prop.bot_eq_false, Pi.bot_apply, iff_false]
  exact fun hab ↦ e.symm.map_rel_iff.2 hab.coe

@[simp] lemma copyCount_of_isEmpty [IsEmpty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    G.copyCount H = 1 := by
  rw [copyCount]
  convert card_singleton (⊥ : H.Subgraph)
  simp only [eq_singleton_iff_unique_mem, mem_filter, mem_univ, Subgraph.coe_bot, true_and,
    Nonempty.forall, Subsingleton.elim G ⊥]
  haveI : IsEmpty (⊥ : H.Subgraph).verts := by simp
  refine ⟨⟨⟨⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim⟩, fun {a} ↦ isEmptyElim a⟩⟩,
    fun H' e ↦ Subgraph.ext ?_ <| funext₂ fun a b ↦ ?_⟩
  · simpa [Set.eq_empty_iff_forall_not_mem, filter_eq_empty_iff, ‹IsEmpty α›] using
      e.toEquiv.symm.isEmpty_congr
  · simp only [Subgraph.not_bot_adj, eq_iff_iff, iff_false]
    exact fun hab ↦ e.symm.map_rel_iff.2 hab.coe

@[simp] lemma copyCount_eq_zero : G.copyCount H = 0 ↔ ¬ G ⊑ H := by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_eq_empty_iff]

@[simp] lemma copyCount_pos : 0 < G.copyCount H ↔ G ⊑ H := by
  simp [copyCount, -nonempty_subtype, isContained_iff_exists_iso_subgraph, card_pos,
    filter_nonempty_iff]

end CopyCount

section LabelledCopyCount
variable [Fintype α] [Fintype β]

/-- `G.labelledCopyCount H` is the number of labelled copies of `G` in `H`. See
`SimpleGraph.copyCount` for the number of unlabelled copies. -/
noncomputable def labelledCopyCount (G : SimpleGraph α) (H : SimpleGraph β) : ℕ := by
  classical exact Fintype.card {f : G →g H // Injective f}

@[simp] lemma labelledCopyCount_of_isEmpty [IsEmpty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    G.labelledCopyCount H = 1 := by
  convert Fintype.card_unique
  exact { default := ⟨default, isEmptyElim⟩, uniq := fun _ ↦ Subsingleton.elim _ _ }

@[simp] lemma labelledCopyCount_eq_zero : G.labelledCopyCount H = 0 ↔ ¬ G ⊑ H := by
  simp [labelledCopyCount, IsContained, Fintype.card_eq_zero_iff, isEmpty_subtype]

@[simp] lemma labelledCopyCount_pos : 0 < G.labelledCopyCount H ↔ G ⊑ H := by
  simp [labelledCopyCount, IsContained, Fintype.card_pos_iff]

/-- There's more labelled copies of `H` of-`G` than unlabelled ones. -/
lemma copyCount_le_labelledCopyCount : G.copyCount H ≤ G.labelledCopyCount H := by
  rw [copyCount, ← Fintype.card_coe]
  refine Fintype.card_le_of_injective (fun H' ↦
    ⟨H'.val.hom.comp (mem_filter.1 H'.2).2.some.toHom,
      Subtype.coe_injective.comp (mem_filter.1 H'.2).2.some.injective⟩) ?_
  sorry

end LabelledCopyCount

/-!
### Killing a subgraph

An important aspect of graph containment is that we can remove not too many edges from a graph `H`
to get a graph `H'` that doesn't contain `G`.

`SimpleGraph.kill G H` is a subgraph of `H` where an edge was removed from each copy of `G` in `H`.
By construction, it doesn't contain `G` and has at most the number of copies of `G` edges less than
`H`
-/

private lemma aux (hG : G ≠ ⊥) {H' : H.Subgraph} :
    Nonempty (G ≃g H'.coe) → H'.edgeSet.Nonempty := by
  obtain ⟨e, he⟩ := edgeSet_nonempty.2 hG
  rw [← Subgraph.image_coe_edgeSet_coe]
  exact fun ⟨f⟩ ↦ Set.Nonempty.image _ ⟨_, f.map_mem_edgeSet_iff.2 he⟩

/-- `G.kill H` is a subgraph of `H` where an edge from every subgraph isomorphic to `G` was removed.
As such, it is a big subgraph of `H` that does not contain any subgraph isomorphic to `G`, unless
`G` had no edges to start with. -/
noncomputable irreducible_def kill (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph β :=
  if hG : G = ⊥ then H
  else H.deleteEdges <| ⋃ (H' : H.Subgraph) (hH' : Nonempty (G ≃g H'.coe)), {(aux hG hH').some}

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a subgraph of `H`. -/
lemma kill_le : G.kill H ≤ H := by rw [kill]; split_ifs; exacts [le_rfl, deleteEdges_le _]

@[simp] lemma bot_kill (H : SimpleGraph β) : (⊥ : SimpleGraph α).kill H = H := by
  rw [kill]; exact dif_pos rfl

private lemma kill_of_ne_bot (hG : G ≠ ⊥) (H : SimpleGraph β) :
    G.kill H =
      H.deleteEdges (⋃ (H' : H.Subgraph) (hH' : Nonempty (G ≃g H'.coe)), {(aux hG hH').some}) := by
  rw [kill]; exact dif_neg hG

lemma kill_eq_right (hG : G ≠ ⊥) : G.kill H = H ↔ ¬ G ⊑ H := by
  simp only [kill_of_ne_bot hG, Set.disjoint_left, isContained_iff_exists_iso_subgraph,
    @forall_swap _ H.Subgraph, Set.iUnion_singleton_eq_range, deleteEdges_eq_self, Set.mem_iUnion,
    Set.mem_range, not_exists, not_nonempty_iff, Nonempty.forall]
  exact forall_congr' fun H' ↦ ⟨fun h ↦ ⟨fun f ↦ h _
    (Subgraph.edgeSet_subset _ <| (aux hG ⟨f⟩).choose_spec) f rfl⟩, fun h _ _ ↦ h.elim⟩

lemma kill_of_not_isContained (hGH : ¬ G ⊑ H) : G.kill H = H := by
  obtain rfl | hG := eq_or_ne G ⊥
  · exact bot_kill _
  · exact (kill_eq_right hG).2 hGH

/-- Removing an edge from `H` for each subgraph isomorphic to `G` results in a graph that doesn't
contain `G`. -/
lemma not_isContained_kill (hG : G ≠ ⊥) : ¬ G ⊑ G.kill H := by
  rw [kill_of_ne_bot hG, deleteEdges, isContained_iff_exists_iso_subgraph]
  rintro ⟨H', hGH'⟩
  have hH' : (H'.map <| Hom.ofLE (sdiff_le : H \ _ ≤ H)).edgeSet.Nonempty := by
    rw [Subgraph.edgeSet_map]
    exact (aux hG hGH').image _
  set e := hH'.some with he
  have : e ∈ _ := hH'.some_mem
  clear_value e
  rw [← Subgraph.image_coe_edgeSet_coe] at this
  subst he
  obtain ⟨e, he₀, he₁⟩ := this
  let e' : Sym2 H'.verts := Sym2.map (Subgraph.isoMap (.ofLE _ _ _) _).symm e
  have he' : e' ∈ H'.coe.edgeSet := (Iso.map_mem_edgeSet_iff _).2 he₀
  rw [Subgraph.edgeSet_coe] at he'
  have := Subgraph.edgeSet_subset _ he'
  simp only [edgeSet_sdiff,  edgeSet_fromEdgeSet,  edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
    Set.mem_iUnion, not_exists] at this
  refine this.2 (H'.map <| Hom.ofLE sdiff_le) ⟨(Subgraph.isoMap (.ofLE _ _ _) _).comp hGH'.some⟩ ?_
  rw [Sym2.map_map, Set.mem_singleton_iff, ← he₁]
  congr 1 with x
  exact congr_arg _ (Equiv.Set.image_symm_apply _ _ injective_id _ _)

variable [Fintype H.edgeSet]

noncomputable instance kill.EdgeSet.fintype : Fintype (G.kill H).edgeSet :=
  Fintype.ofInjective (Set.inclusion <| edgeSet_mono kill_le) <| Set.inclusion_injective _

/-- Removing an edge from `H` for each subgraph isomorphic to `G` means that the number of edges
we've removed is at most the number of copies of `G` in `H`. -/
lemma le_card_edgeFinset_kill [Fintype β] :
    #H.edgeFinset - G.copyCount H ≤ (G.kill H).edgeFinset.card := by
  obtain rfl | hG := eq_or_ne G ⊥
  · simp
  let f (H' : {H' : H.Subgraph // Nonempty (G ≃g H'.coe)}) := (aux hG H'.2).some
  calc
    _ = #H.edgeFinset - card {H' : H.Subgraph // Nonempty (G ≃g H'.coe)} := ?_
    _ ≤ #H.edgeFinset - (univ.image f).card := Nat.sub_le_sub_left card_image_le _
    _ = #H.edgeFinset - (Set.range f).toFinset.card := by rw [Set.toFinset_range]
    _ ≤ (H.edgeFinset \ (Set.range f).toFinset).card := le_card_sdiff ..
    _ = (G.kill H).edgeFinset.card := ?_
  · simp only [Set.toFinset_card]
    rw [← Set.toFinset_card, ← edgeFinset, copyCount, ← card_subtype, subtype_univ, card_univ]
  simp only [kill_of_ne_bot, hG, Ne, not_false_iff, Set.iUnion_singleton_eq_range,
    Set.toFinset_card, Fintype.card_ofFinset, edgeSet_deleteEdges]
  simp only [Finset.sdiff_eq_inter_compl, Set.diff_eq, ← Set.iUnion_singleton_eq_range, coe_sdiff,
    Set.coe_toFinset, coe_filter, Set.sep_mem_eq, Set.iUnion_subtype, ← Fintype.card_coe,
    ← Finset.coe_sort_coe, coe_inter, coe_compl, Set.coe_toFinset, Set.compl_iUnion,
    Fintype.card_ofFinset, f]

end SimpleGraph
