/-
Copyright 2026 Brian Akaka

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

import FormalConjecturesUtil

/-!
# An alternative approach to Written on the Wall II, Conjecture 2

This file develops an independent proof route based on a maximum-edge
triangle-free spanning subgraph.  It intentionally does not import or reuse the
AlphaProof Nexus proof of the conjecture.

The planned reduction is as follows.

1. Choose a triangle-free spanning subgraph `H ≤ G` with as many edges as
   possible.
2. Prove that `H` is connected and that
   `G.indepNeighborsCard v ≤ H.degree v` for every vertex `v`.
3. Prove the triangle-free leaf estimate
   `Ls H ≥ 4 * |E(H)| / |V(H)| - 2` using double-stars and Cauchy--Schwarz.
4. Use monotonicity of `Ls` under taking spanning supergraphs.

The first step is formalized below without any additional axioms.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite graph has a triangle-free subgraph with maximum edge count among
all triangle-free subgraphs contained in it.  Since all graphs here have the
same vertex type, this is a spanning-subgraph statement. -/
lemma exists_maxEdge_triangleFree_subgraph (G : SimpleGraph α) :
    ∃ H : SimpleGraph α,
      H ≤ G ∧
      H.CliqueFree 3 ∧
      ∀ K : SimpleGraph α,
        K ≤ G → K.CliqueFree 3 → K.edgeFinset.card ≤ H.edgeFinset.card := by
  classical
  let candidates : Finset (SimpleGraph α) :=
    Finset.univ.filter fun H => H ≤ G ∧ H.CliqueFree 3
  have hbot : (⊥ : SimpleGraph α) ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, bot_le, ?_⟩
    exact SimpleGraph.cliqueFree_bot (by decide : 2 ≤ 3)
  obtain ⟨H, hH, hmax⟩ :=
    Finset.exists_max_image candidates (fun K : SimpleGraph α => K.edgeFinset.card)
      ⟨⊥, hbot⟩
  have hHprop : H ≤ G ∧ H.CliqueFree 3 := (Finset.mem_filter.mp hH).2
  refine ⟨H, hHprop.1, hHprop.2, ?_⟩
  intro K hKG hKtri
  apply hmax K
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKG, hKtri⟩

/-- A chosen maximum-edge triangle-free subgraph of `G`. -/
noncomputable def maxEdgeTriangleFreeSubgraph (G : SimpleGraph α) : SimpleGraph α :=
  Classical.choose (exists_maxEdge_triangleFree_subgraph G)

lemma maxEdgeTriangleFreeSubgraph_le (G : SimpleGraph α) :
    maxEdgeTriangleFreeSubgraph G ≤ G :=
  (Classical.choose_spec (exists_maxEdge_triangleFree_subgraph G)).1

lemma maxEdgeTriangleFreeSubgraph_cliqueFree (G : SimpleGraph α) :
    (maxEdgeTriangleFreeSubgraph G).CliqueFree 3 :=
  (Classical.choose_spec (exists_maxEdge_triangleFree_subgraph G)).2.1

lemma card_edgeFinset_le_maxEdgeTriangleFreeSubgraph
    (G K : SimpleGraph α) (hKG : K ≤ G) (hKtri : K.CliqueFree 3) :
    K.edgeFinset.card ≤ (maxEdgeTriangleFreeSubgraph G).edgeFinset.card :=
  (Classical.choose_spec (exists_maxEdge_triangleFree_subgraph G)).2.2 K hKG hKtri

end WrittenOnTheWallII.GraphConjecture2.Alternative
