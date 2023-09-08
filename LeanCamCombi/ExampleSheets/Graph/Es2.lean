/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Sqrt
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Graph Theory, example sheet 2

Here are the statements (and hopefully soon proofs!) of the questions from the second example sheet
of the Cambridge Part II course Graph Theory.

If you solve a question in Lean, feel free to open a Pull Request on Github!
-/


/-!
### Question 1

For a graph $$G$$, show that $$κ(G) ≤ λ(G) ≤ δ(G)$$.
-/


/-!
### Question 2

Let $$G be a graph. Show that $$e(G) > {χ(G) \choose 2}$$.
-/


/-!
### Question 3

Let $$G$$ be a $$k$$-connected graph and let $$y, x_1, \dots, x_k$$ be distinct vertices in $$G$$.
Show that there exists paths $$P_1, \dots, P_k$$, where $$P_i$$ is a $$y − x_i$$ path and
$$P_1, \dots, P_k$$ have no vertices in common, apart from the vertex $$y$$.
-/


/-!
### Question 4

An independent set in a graph $$G = (V, E)$$ is a subset $$I ⊆ V$$ so that $$x ≁ y$$ for all
$$x, y ∈ I$$. Let $$G = (V, E)$$ be a connected graph with $$∆(G) ≤ 3$$ and $$|V| ≥ 10$$. Show that
there exists an independent set $$I ⊆ V$$ so that every odd cycle in $$G$$ intersects $$I$$.
-/


/-!
### Question 5

Determine the chromatic polynomial of the $$n$$-cycle $$C_n$$.
-/


/-!
### Question 6

Let $$G$$ be a graph on $$n$$ vertices, show that the coefficients of the chromatic polynomial
$$P_G$$ alternate in sign. That is, if $$P_G = P_ni=0 cit
i
, Then cn−j > 0 for even j and cn−j 6 0 for odd j. Also
show that if G has m edges and k triangles then cn−2 =
m
2

− k.
-/


/-!
### Question 7

Determine $$χ(K_{n,n}$$). Determine $$χ(K_n)$$.
-/


/-!
### Question 8

Let $$G$$ be a graph that has an orientation where the longest directed path has length $$t$$ (that
is, a sequence of oriented edges $$(v_1, v_2), \dots, (v_t, v_{t + 1})$$. Then $$χ(G) ≤ t + 1$$.
-/


/-!
### Question 9

Can $$K_{4, 4}$$ be drawn on the torus? What about $$K_{5, 5}$$?
-/


/-!
### Question 10

Let $$G$$ be a bipartite graph with maximum degree $$∆$$. Must we have $$χ(G) = ∆(G)$$?
-/


/-!
### Question 11

Let $$G = (V, E)$$ be a graph where $$V$$, $$E$$ are countably infinite. Show that $$χ(G) ≤ k$$ if
and only if $$χ(H) ≤ k$$ for every finite subgraph $$H$$ of $$G$$.
-/


/-!
### Question 12

For $$k > 2$$, let $$G = (V, E)$$ be a $$k$$-connected graph and let $${x_1, \dots, x_k} ⊆ V$$. Show
that there exists a cycle containing each of the vertices $$x_1, \dots, x_k$$.
-/


/-!
### Question 13

For each $$r > 2$$, construct a graph $$G$$ that does not contain a $$K_{r + 1}$$ and $$χ(G) > r$$.
-/


/-!
### Question 14

A graph is outer-planar if it can be drawn in the plane so that all of its vertices are on the
infinite face. Articulate a conjecture of the form “Let $$G$$ be a graph with $$|G| > 5$$. $$G$$ is
outer-planar if and only if ...”. Prove your conjecture.
-/


/-!
### Question 15

Show there is a triangle free graph with chromatic number $$2022$$.
-/


/-!
### Question 16

Let $$G$$ be a triangulation (a plane graph where every face is a triangle) and let $$G◦$$ be the
planar dual of $$G$$: the vertices of $$G◦$$ are the faces of $$G$$ and edges in $$G◦$$ join faces
that share a boundary edge (in $$G$$). Prove that $$χ(G) ≤ 4$$ if and only if $$χ(G◦) ≤ 3$$.
-/
