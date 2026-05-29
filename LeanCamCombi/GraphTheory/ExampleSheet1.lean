/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Graph Theory, example sheet 1

Here are the statements (and hopefully soon proofs!) of the questions from the first example sheet
of the Cambridge Part II course Graph Theory.

If you solve a question in Lean, feel free to open a Pull Request on Github!
-/

public section

open Fintype (card)
open Function SimpleGraph
open scoped Cardinal SetRel

namespace GraphTheory
namespace ES1
variable {ι α β γ : Type*}

/-!
### Question 1

Show that a graph $$G$$ which contains an odd circuit, contains an odd cycle.
-/


lemma q1 (G : SimpleGraph α) (a : α) (w : G.Walk a a) (hw : Odd w.length) :
    ∃ (b : _) (p : G.Path b b), Odd (p : G.Walk b b).length :=
  sorry

/-!
### Question 2

Show there are infinitely many planar graphs for which $$e(G) = 3(|G| − 2)$$. Can you give a nice
description of all graphs that satisfy this equality?
-/


/-!
### Question 3

Show that every graph $$G$$, with $$|G| > 2$$, has two vertices of the same degree.
-/

-- Planarity is hard
lemma q3 [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ a b, a ≠ b ∧ G.degree a = G.degree b :=
  sorry

/-!
### Question 4

Show that in every connected graph with $$|G| ≥ 2$$ there exists a vertex $$v$$ so that $$G − v$$ is
connected.
-/

-- This looks a bit painful as a translation. Probably better stated using connectivity on a set.
lemma q4 [Finite α] [Nontrivial α] (G : SimpleGraph α) (hG : G.Connected) :
    ∃ a, ((⊤ : G.Subgraph).deleteVerts {a}).coe.Connected := by
  cases nonempty_fintype α
  sorry

/-!
### Question 5

Show that if $$G$$ is acyclic and $$|G| ≥ 1$$, then $$e(G) ≤ n − 1$$.
-/

-- Note: The statement is true without `nonempty α` due to nat subtraction.
lemma q5 [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ card α - 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim G ⊥]
  · classical
    obtain ⟨T, hGT, -, hT⟩ := connected_top.exists_isTree_le_of_le_of_isAcyclic le_top hG
    have h1 := Finset.card_le_card (edgeFinset_subset_edgeFinset.mpr hGT)
    have h2 := hT.card_edgeFinset
    lia

/-!
### Question 6

The degree sequence of a graph $$G = ({x_1, . . . , x_n}, E)$$ is the sequence
$$d(x_1), . . . , d(x_n)$$.
For $$n ≥ 2$$, let $$1 ≤ d_1 ≤ d_2 ≤ \dots ≤ d_n$$ be integers. Show that $$(d_i)_{i = 1}^n$$ is a
degree sequence of a tree if and only if $$\sum_{i=1}^n d_i = 2n − 2$$.
-/

/-- The finset of degrees of a finite graph. -/
def degreeSequence [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun a ↦ G.degree a

lemma q6 [Fintype α] (s : Multiset ℕ) (hs : Multiset.card s = card α) (h₀ : 0 ∉ s) :
    s.sum = 2 * card α - 2 ↔
      ∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj), degreeSequence G = s :=
  sorry

/-!
### Question 7

Let $$T_1, \dots, T_k$$ be subtrees of a tree $$T$$. Show that if $$V(T_i) ∩ V(T_j) ≠ ∅$$ for all
$$i, j ∈ [k]$$ then $$V(T_1) ∩ \dots ∩ V(T_k) ≠ ∅$$.
-/

lemma q7 (G : SimpleGraph α) (hG : G.IsAcyclic) (s : Finset ι) (f : ι → G.Subgraph)
    (hf : ∀ i ∈ s, (f i).coe.IsAcyclic) (h : ∀ i ∈ s, ∀ j ∈ s, f i ⊓ f j ≠ ⊥) :
    s.inf f ≠ ⊥ :=
  sorry

/-!
### Question 8

The average degree of a graph $$G = (V, E)$$ is $$n^{-1} \sum_{x ∈ V} d(x)$$. Show that if the
average degree of $$G$$ is $$d$$ then $$G$$ contains a subgraph with minimum degree $≥ d/2$$.
-/

/-- The average degree of a simple graph is the average of its degrees. -/
def averageDegree [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ :=
  ∑ a, G.degree a / card α

lemma q8 [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∃ (H : Subgraph G) (_ : DecidableRel H.Adj), ∀ a, averageDegree G / 2 ≤ H.degree a :=
  sorry

/-!
### Question 9

Say that a graph $$G = (V, E)$$ can be decomposed into cycles if $$E$$ can be partitioned
$$E = E_1 ∪ \dots ∪ E_k$$, where each $$E_i$$ is the edge set of a cycle. Show that $$G$$ can be
decomposed into cycles if and only if all degrees of $$G$$ are even.
-/

-- This looks painful as a translation. It will likely get better once we have Kyle's eulerian paths
lemma q9 [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ 𝒜 : Finset (Σ a, G.Path a a),
        (∀ p q : Σ a, G.Path a a,
            (p.2 : G.Walk p.1 p.1).edges.Disjoint (q.2 : G.Walk q.1 q.1).edges) ∧
          ∀ e, ∃ p : Σ a, G.Path a a, p ∈ 𝒜 ∧ e ∈ (p.2 : G.Walk p.1 p.1).edges) ↔
      ∀ a, Even (G.degree a) :=
  sorry

/-!
### Question 10

The clique number of a graph $$G$$ is the largest $$t$$ so that $$G$$ contains a complete graph on
$$t$$ vertices.
Show that the possible clique numbers for a regular graph on $$n$$ vertices are
$$1, 2, \dots, n/2$$ and $$n$$.
-/

lemma q10 [Fintype α] (n : ℕ) :
    (∃ (G : SimpleGraph α) (_ : DecidableRel G.Adj) (k : _),
        G.IsRegularOfDegree k ∧ cliqueNum G = n) ↔
      n ≤ card α / 2 ∨ n = card α :=
  sorry

/-!
### Question 11

Show that the Petersen graph is non-planar.
-/


/-!
### Question 12

Let $$G = (V, E)$$ be a graph. Show that there is a partition $$V = A ∪ B$$ so all the vertices in
the graphs $$G[A]$$ and $$G[B]$$ are of even degree.
-/

-- Note: This is a bit more general than the statement, because we allow partitioning any set of
-- vertices
lemma q12 [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] (s : Finset α) :
    ∃ u v, Disjoint u v ∧ u ∪ v = s ∧
      (∀ a ∈ u, Even #{b ∈ u | G.Adj a b}) ∧ ∀ a ∈ v, Even #{b ∈ v | G.Adj a b} :=
  sorry

/-!
### Question 13

A $$m × n$$ Latin rectangle is a $$m × n$$ matrix, with each entry from $${1, . . . , n}$$, such
that no two entries in the same row or column are the same. Prove that every $$m × n$$ Latin
rectangle may be extended to a $$n × n$$ Latin square.
-/

/-- A Latin rectangle is a binary function whose transversals are all injective. -/
def IsLatin (f : α → β → γ) : Prop :=
  (∀ a, Injective (f a)) ∧ ∀ b, Injective fun a ↦ f a b

lemma q13 [Finite α] (g : β ↪ α) (f : β → α → α) (hf : IsLatin f) :
    ∃ f', f' ∘ g = f ∧ IsLatin f :=
  sorry

/-!
### Question 14

Let $$G = (X ∪ Y, E)$$ be a countably infinite bipartite graph with the property that
$$|N(A)| ≥ |A|$$ for all $$A ⊆ X$$. Give an example to show that $$G$$ need not contain a matching
from $$X$$ to $$Y$$ . On the other hand, show that if all of the degrees of $$G$$ are finite then
$$G$$ does contain a matching from $$X$$ to $$Y$$. Does this remain true if $$G$$ is uncountable and
all degrees of $$X$$ are finite (while degrees in $$Y$$ have no restriction)?
-/

-- This translation looks slightly painful because of the `cardinal`.
lemma q14_part1 :
    ∃ r : SetRel ℕ ℕ,
      (∀ A : Finset ℕ, (A.card : Cardinal) ≤ #(r.image A)) ∧
        ∀ f : ℕ → ℕ, Injective f → ∃ n, ¬ n ~[r] f n :=
  sorry

lemma q14_part2 [DecidableEq β] [Countable α] [Countable β] (r : SetRel α β)
    [∀ a, Fintype (r.image {a})] (hr : ∀ A : Finset α, A.card ≤ card (r.image A)) :
    ∃ f : α → β, Injective f ∧ ∀ a, a ~[r] f a :=
  sorry

lemma q14_part3 [DecidableEq β] (r : SetRel α β) [∀ a, Fintype (r.image {a})]
    (hr : ∀ A : Finset α, A.card ≤ card (r.image A)) :
    ∃ f : α → β, Injective f ∧ ∀ a, a ~[r] f a :=
  sorry

/-!
### Question 15

Let $$(X, d_X)$$ be a metric space. We say that a function $$f : X → ℝ^2$$ has distortion
$$≤ D$$ if there exists an $$r > 0$$ so that
$$rd_X(x, y) ≤ ‖f(x) − f(y)‖_2 ≤ Drd_X(x, y)$$.
Show that there is some constant $$c > 0$$ such that for all $$n$$ there is a metric space
$$M = ({x_1, \dots, x_n}, d_M)$$ on $$n$$ points so that every function $$f : M → ℝ^2$$ has
distortion $$> cn^{1/2}$$. Does there exist some constant $$c > 0$$ such that for all $$n$$ there is
a metric space $$M = ({x_1, \dots, x_n}, d_M)$$ on $$n$$ points so that every function
$$f : M → ℝ^2$$ has distortion $$> cn$$?
-/

/-- The distortion of a function `f` between metric spaces is the ratio between the maximum and
minimum of `dist (f a) (f b) / dist a b`. -/
noncomputable def distortion [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) : ℝ :=
  (⨆ (a) (b), dist (f a) (f b) / dist a b) / ⨅ (a) (b), dist (f a) (f b) / dist a b

lemma q15_part1 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (α) [Fintype α],
      ∃ _ : MetricSpace α, ∀ f : α → ℝ × ℝ, ε * Real.sqrt (card α) ≤ distortion f :=
  sorry

lemma q15_part2 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (α) [Fintype α],
      ∃ _ : MetricSpace α, ∀ f : α → ℝ × ℝ, ε * card α ≤ distortion f :=
  sorry

end ES1
end GraphTheory
