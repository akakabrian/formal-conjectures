/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.WrittenOnTheWallII.GraphConjecture2AlternativeLocalBound

/-!
# Edge replacement for the alternative proof of WOWII Conjecture 2

This file replaces all edges incident to a vertex `v` by a finite star from
`v` to an independent subset `A` of its neighbourhood.  Edge maximality of the
chosen triangle-free spanning subgraph then forces `A.card ≤ H.degree v`.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Delete every edge of `H` incident to `v` and add the finite star from `v`
to `A`. -/
def centerReplacement (H : SimpleGraph α) (v : α) (A : Finset α) : SimpleGraph α :=
  H.deleteIncidenceSet v ⊔ finsetStar v A

lemma centerReplacement_le (G H : SimpleGraph α) (hHG : H ≤ G)
    {v : α} {A : Finset α} (hA : ∀ a ∈ A, G.Adj v a) :
    centerReplacement H v A ≤ G := by
  refine sup_le ?_ ?_
  · exact (H.deleteIncidenceSet_le v).trans hHG
  · exact finsetStar_le G hA

lemma deleteIncidenceSet_disjoint_finsetStar
    (H : SimpleGraph α) {v : α} {A : Finset α} (hv : v ∉ A) :
    Disjoint (H.deleteIncidenceSet v) (finsetStar v A) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hOld hStar
  have hOld' := SimpleGraph.deleteIncidenceSet_adj.mp hOld
  rw [finsetStar_adj hv] at hStar
  rcases hStar with hStar | hStar
  · rcases hStar with ⟨hx, _⟩
    subst x
    exact hOld'.2.1 rfl
  · rcases hStar with ⟨hy, _⟩
    subst y
    exact hOld'.2.2 rfl

lemma card_edgeFinset_centerReplacement
    (H : SimpleGraph α) {v : α} {A : Finset α} (hv : v ∉ A) :
    (centerReplacement H v A).edgeFinset.card =
      H.edgeFinset.card - H.degree v + A.card := by
  classical
  have hdisjGraph : Disjoint (H.deleteIncidenceSet v) (finsetStar v A) :=
    deleteIncidenceSet_disjoint_finsetStar H hv
  have hdisjEdges :
      Disjoint (H.deleteIncidenceSet v).edgeFinset (finsetStar v A).edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr hdisjGraph
  rw [centerReplacement, SimpleGraph.edgeFinset_sup,
    Finset.card_union_of_disjoint hdisjEdges,
    H.card_edgeFinset_deleteIncidenceSet v,
    card_edgeFinset_finsetStar hv]

lemma centerReplacement_cliqueFree
    (G H : SimpleGraph α) (hHG : H ≤ G) (hHtri : H.CliqueFree 3)
    {v : α} {A : Finset α} (hv : v ∉ A)
    (hAind : G.IsIndepSet (A : Set α)) :
    (centerReplacement H v A).CliqueFree 3 := by
  classical
  have hcenterNeighbor :
      ∀ {z : α}, (centerReplacement H v A).Adj v z → z ∈ A := by
    intro z hvz
    have hvz' :
        (H.deleteIncidenceSet v).Adj v z ∨ (finsetStar v A).Adj v z := by
      simpa [centerReplacement] using hvz
    rcases hvz' with hvzOld | hvzStar
    · exact False.elim ((SimpleGraph.deleteIncidenceSet_adj.mp hvzOld).2.1 rfl)
    · rw [finsetStar_adj hv] at hvzStar
      rcases hvzStar with hvzStar | hvzStar
      · exact hvzStar.2
      · exact False.elim (hv hvzStar.2)
  have hcenterTriangle :
      ∀ {y z : α}, y ∈ A →
        (centerReplacement H v A).Adj v z →
        (centerReplacement H v A).Adj y z → False := by
    intro y z hy hvz hyz
    have hz : z ∈ A := hcenterNeighbor hvz
    have hyne : y ≠ v := by
      intro hyv
      exact hv (hyv ▸ hy)
    have hzne : z ≠ v := by
      intro hzv
      exact hv (hzv ▸ hz)
    have hGyz : G.Adj y z := by
      have hyz' :
          (H.deleteIncidenceSet v).Adj y z ∨ (finsetStar v A).Adj y z := by
        simpa [centerReplacement] using hyz
      rcases hyz' with hyzOld | hyzStar
      · exact hHG ((H.deleteIncidenceSet_le v) hyzOld)
      · rw [finsetStar_adj hv] at hyzStar
        rcases hyzStar with hyzStar | hyzStar
        · exact False.elim (hyne hyzStar.1)
        · exact False.elim (hzne hyzStar.1)
    exact (hAind (Finset.mem_coe.mpr hy) (Finset.mem_coe.mpr hz) hGyz.ne) hGyz
  have hstarTriangle :
      ∀ {x y z : α}, (finsetStar v A).Adj x y →
        (centerReplacement H v A).Adj x z →
        (centerReplacement H v A).Adj y z → False := by
    intro x y z hxy hxz hyz
    rw [finsetStar_adj hv] at hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨hx, hy⟩
      subst x
      exact hcenterTriangle hy hxz hyz
    · rcases hxy with ⟨hy, hx⟩
      subst y
      exact hcenterTriangle hx hyz hxz
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  have hxy' :
      (H.deleteIncidenceSet v).Adj x y ∨ (finsetStar v A).Adj x y := by
    simpa [centerReplacement] using hxy
  have hxz' :
      (H.deleteIncidenceSet v).Adj x z ∨ (finsetStar v A).Adj x z := by
    simpa [centerReplacement] using hxz
  have hyz' :
      (H.deleteIncidenceSet v).Adj y z ∨ (finsetStar v A).Adj y z := by
    simpa [centerReplacement] using hyz
  rcases hxy' with hxyOld | hxyStar
  · rcases hxz' with hxzOld | hxzStar
    · rcases hyz' with hyzOld | hyzStar
      · exact hHtri {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr
          ⟨(SimpleGraph.deleteIncidenceSet_adj.mp hxyOld).1,
           (SimpleGraph.deleteIncidenceSet_adj.mp hxzOld).1,
           (SimpleGraph.deleteIncidenceSet_adj.mp hyzOld).1⟩)
      · exact hstarTriangle hyzStar hxy.symm hxz.symm
    · exact hstarTriangle hxzStar hxy hyz.symm
  · exact hstarTriangle hxyStar hxz hyz

/-- In a maximum-edge triangle-free spanning subgraph, every independent set
of neighbours of `v` has cardinality at most the degree of `v`. -/
lemma indepSet_card_le_degree_of_maxEdge_triangleFree
    (G H : SimpleGraph α) (hHG : H ≤ G) (hHtri : H.CliqueFree 3)
    (hmax : ∀ K : SimpleGraph α,
      K ≤ G → K.CliqueFree 3 → K.edgeFinset.card ≤ H.edgeFinset.card)
    {v : α} {A : Finset α}
    (hA : ∀ a ∈ A, G.Adj v a)
    (hAind : G.IsIndepSet (A : Set α)) :
    A.card ≤ H.degree v := by
  classical
  have hv : v ∉ A := by
    intro hvA
    exact G.loopless v (hA v hvA)
  have hKle : centerReplacement H v A ≤ G :=
    centerReplacement_le G H hHG hA
  have hKtri : (centerReplacement H v A).CliqueFree 3 :=
    centerReplacement_cliqueFree G H hHG hHtri hv hAind
  have hcard_le := hmax (centerReplacement H v A) hKle hKtri
  have hcard_eq := card_edgeFinset_centerReplacement H hv
  have hineq : H.edgeFinset.card - H.degree v + A.card ≤ H.edgeFinset.card := by
    calc
      H.edgeFinset.card - H.degree v + A.card =
          (centerReplacement H v A).edgeFinset.card := hcard_eq.symm
      _ ≤ H.edgeFinset.card := hcard_le
  have hdegree : H.degree v ≤ H.edgeFinset.card := H.degree_le_card_edgeFinset v
  omega

lemma indepSet_card_le_degree_maxEdgeTriangleFreeSubgraph
    (G : SimpleGraph α) {v : α} {A : Finset α}
    (hA : ∀ a ∈ A, G.Adj v a)
    (hAind : G.IsIndepSet (A : Set α)) :
    A.card ≤ (maxEdgeTriangleFreeSubgraph G).degree v := by
  apply indepSet_card_le_degree_of_maxEdge_triangleFree
      G (maxEdgeTriangleFreeSubgraph G)
  · exact maxEdgeTriangleFreeSubgraph_le G
  · exact maxEdgeTriangleFreeSubgraph_cliqueFree G
  · intro K hKG hKtri
    exact card_edgeFinset_le_maxEdgeTriangleFreeSubgraph G K hKG hKtri
  · exact hA
  · exact hAind

end WrittenOnTheWallII.GraphConjecture2.Alternative
