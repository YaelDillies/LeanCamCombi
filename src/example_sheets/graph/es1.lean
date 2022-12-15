/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import combinatorics.hall.basic
import combinatorics.simple_graph.acyclic
import combinatorics.simple_graph.clique
import data.real.sqrt
import set_theory.cardinal.basic

/-!
# Graph Theory, example sheet 1

Here are the statements (and hopefully soon proofs!) of the questions from the first example sheet
of the Cambridge Part II course Graph Theory.

If you solve a question in Lean, feel free to open a Pull Request on Github!
-/

open fintype (card) function simple_graph
open_locale big_operators cardinal

namespace graph_theory
namespace es1

variables {ι α β γ : Type*}

/-!
### Question 1

Show that a graph $$G$$ which contains an odd circuit, contains an odd cycle.
-/

lemma q1 (G : simple_graph α) (a : α) (w : G.walk a a) (hw : odd w.length) :
  ∃ b (p : G.path b b), odd (p : G.walk b b).length :=
sorry

/-!
### Question 2

Show there are infinitely many planar graphs for which $$e(G) = 3(|G| − 2)$$. Can you give a nice
description of all graphs that satisfy this equality?
-/

-- PLanarity is hard

/-!
### Question 3

Show that every graph $$G$$, with $$|G| > 2$$, has two vertices of the same degree.
-/

lemma q3 [fintype α] (G : simple_graph α) [decidable_rel G.adj] :
  ∃ a b, a ≠ b ∧ G.degree a = G.degree b :=
sorry

/-!
### Question 4

Show that in every connected graph with $$|G| ≥ 2$$ there exists a vertex $$v$$ so that $$G − v$$ is
connected.
-/

-- This looks a bit painful as a translation. Probably better stated using connectivity on a set.
lemma q4 [finite α] [nontrivial α] (G : simple_graph α) (hG : G.connected) :
  ∃ a, ((⊤ : G.subgraph).delete_verts {a}).coe.connected :=
begin
  casesI nonempty_fintype α,
  sorry
end

/-!
### Question 5

Show that if $$G$$ is acyclic and $$|G| ≥ 1$$, then $$e(G) ≤ n − 1$$.
-/

-- Note: The statement is true without `nonempty α` due to nat subtraction.
lemma q5 [fintype α] [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj]
  (hG : G.is_acyclic) :
  G.edge_finset.card ≤ card α - 1 :=
begin
  casesI is_empty_or_nonempty α,
  { simp },
  sorry
end

/-!
### Question 6

The degree sequence of a graph $$G = ({x_1, . . . , x_n}, E)$$ is the sequence
$$d(x_1), . . . , d(x_n)$$.
For $$n ≥ 2$$, let $$1 ≤ d_1 ≤ d_2 ≤ \dots ≤ d_n$$ be integers. Show that $$(d_i)_{i = 1}^n$$ is a
degree sequence of a tree if and only if $$\sum_{i=1}^n d_i = 2n − 2$$.
-/

/-- The finset of degrees of a finite graph. -/
def degree_sequence [fintype α] (G : simple_graph α) [decidable_rel G.adj] : multiset ℕ :=
finset.univ.val.map $ λ a, G.degree a

lemma q6 [fintype α] (s : multiset ℕ) (hs : s.card = card α) (h₀ : 0 ∉ s) :
  s.sum = 2 * card α - 2 ↔
    ∃ (G : simple_graph α) [decidable_rel G.adj], by exactI degree_sequence G = s :=
sorry

/-!
### Question 7

Let $$T_1, \dots, T_k$$ be subtrees of a tree $$T$$. Show that if $$V(T_i) ∩ V(T_j) ≠ ∅$$ for all
$$i, j ∈ [k]$$ then $$V(T_1) ∩ \dots ∩ V(T_k) ≠ ∅$$.
-/

lemma q7 (G : simple_graph α) (hG : G.is_acyclic) (s : finset ι) (f : ι → G.subgraph)
  (hf : ∀ i ∈ s, (f i).coe.is_acyclic) (h : ∀ i j ∈ s, f i ⊓ f j ≠ ⊥) :
  s.inf f ≠ ⊥ :=
sorry

/-!
### Question 8

The average degree of a graph $$G = (V, E)$$ is $$n^{-1} \sum_{x ∈ V} d(x)$$. Show that if the
average degree of $$G$$ is $$d$$ then $$G$$ contains a subgraph with minimum degree $≥ d/2$$.
-/

/-- The average degree of a simple graph is the average of its degrees. -/
def average_degree [fintype α] (G : simple_graph α) [decidable_rel G.adj] : ℚ :=
∑ a, G.degree a / card α

lemma q8 [fintype α] (G : simple_graph α) [decidable_rel G.adj] :
  ∃ (H : subgraph G) [decidable_rel H.adj], ∀ a, by exactI average_degree G / 2 ≤ H.degree a :=
sorry

/-!
### Question 9

Say that a graph $$G = (V, E)$$ can be decomposed into cycles if $$E$$ can be partitioned
$$E = E_1 ∪ \dots ∪ E_k$$, where each $$E_i$$ is the edge set of a cycle. Show that $$G$$ can be
decomposed into cycles if and only if all degrees of $$G$$ are even.
-/

-- This looks painful as a translation. It will likely get better once we have Kyle's eulerian paths
lemma q9 [fintype α] (G : simple_graph α) [decidable_rel G.adj] :
  (∃ 𝒜 : finset (Σ a, G.path a a),
    (∀ p q : Σ a, G.path a a, (p.2 : G.walk p.1 p.1).edges.disjoint (q.2 : G.walk q.1 q.1).edges) ∧
      ∀ e, ∃ p : Σ a, G.path a a, p ∈ 𝒜 ∧ e ∈ (p.2 : G.walk p.1 p.1).edges)
        ↔ ∀ a, even (G.degree a) :=
sorry

/-!
### Question 10

The clique number of a graph $$G$$ is the largest $$t$$ so that $$G$$ contains a complete graph on
$$t$$ vertices.
Show that the possible clique numbers for a regular graph on $$n$$ vertices are
$$1, 2, \dots, n/2$$ and $$n$$.
-/

/-- The clique number of a graph is the size of its largest clique. -/
def clique_number [fintype α] [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj] : ℕ :=
nat.find_greatest (λ n, ∃ s, G.is_n_clique n s) $ card α

lemma q10 [fintype α] [decidable_eq α] (n : ℕ) :
  (∃ (G : simple_graph α) [decidable_rel G.adj] k, by exactI G.is_regular_of_degree k
    ∧ clique_number G = n)
      ↔ n ≤ card α / 2 ∨ n = card α :=
sorry

/-!
### Question 11

Show that the Petersen graph is non-planar.
-/

-- PLanarity is hard

/-!
### Question 12

Let $$G = (V, E)$$ be a graph. Show that there is a partition $$V = A ∪ B$$ so all the vertices in
the graphs $$G[A]$$ and $$G[B]$$ are of even degree.
-/

-- Note: This is a bit general than the statement, because we allow partitioning any set of vertices
lemma q12 [decidable_eq α] (G : simple_graph α) [decidable_rel G.adj] (s : finset α) :
  ∃ u v, disjoint u v ∧ u ∪ v = s ∧
    (∀ a ∈ u, even (u.filter $ G.adj a).card) ∧ (∀ a ∈ v, even (v.filter $ G.adj a).card) :=
sorry

/-!
### Question 13

A $$m × n$$ Latin rectangle is a $$m × n$$ matrix, with each entry from $${1, . . . , n}$$, such
that no two entries in the same row or column are the same. Prove that every $$m × n$$ Latin
rectangle may be extended to a $$n × n$$ Latin square.
-/

/-- A Latin rectangle is a binary function whose transversals are all injective. -/
def is_latin (f : α → β → γ) : Prop := (∀ a, injective (f a)) ∧ ∀ b, injective $ λ a, f a b

lemma q13 [finite α] (g : β ↪ α) (f : β → α → α) (hf : is_latin f) :
  ∃ f', f' ∘ g = f ∧ is_latin f :=
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
  ∃ r : ℕ → ℕ → Prop, (∀ A : finset ℕ, (A.card : cardinal) ≤ #(rel.image r A))
    ∧ ∀ f : ℕ → ℕ, injective f → ∃ n, ¬ r n (f n) :=
sorry

lemma q14_part2 [decidable_eq β] [countable α] [countable β] (r : α → β → Prop)
  [Π a, fintype (rel.image r {a})] (hr : ∀ A : finset α, A.card ≤ card ↥(rel.image r A)) :
  ∃ f : α → β, injective f ∧ ∀ a, r a (f a) :=
sorry

lemma q14_part3 [decidable_eq β] (r : α → β → Prop) [Π a, fintype (rel.image r {a})]
  (hr : ∀ A : finset α, A.card ≤ card ↥(rel.image r A)) :
  ∃ f : α → β, injective f ∧ ∀ a, r a (f a) :=
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
noncomputable def distortion [pseudo_metric_space α] [pseudo_metric_space β] (f : α → β) : ℝ :=
(⨆ a b, dist (f a) (f b) / dist a b) / ⨅ a b, dist (f a) (f b) / dist a b

lemma q15_part1 :
  ∃ (ε : ℝ), 0 < ε ∧ ∀ α [fintype α], ∃ (_ : metric_space α),
    by exactI ∀ f : α → ℝ × ℝ, ε * real.sqrt (card α) ≤ distortion f :=
sorry

lemma q15_part2 :
  ∃ (ε : ℝ), 0 < ε ∧ ∀ α [fintype α], ∃ (_ : metric_space α),
    by exactI ∀ f : α → ℝ × ℝ, ε * card α ≤ distortion f :=
sorry

end es1
end graph_theory
