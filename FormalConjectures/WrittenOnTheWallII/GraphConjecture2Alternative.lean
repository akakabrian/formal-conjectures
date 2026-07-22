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
triangle-free spanning subgraph. It intentionally does not import or reuse the
AlphaProof Nexus proof of the conjecture.

The planned reduction is as follows.

1. Choose a triangle-free spanning subgraph `H ≤ G` with as many edges as
   possible.
2. Prove that `H` is connected and that
   `G.indepNeighborsCard v ≤ H.degree v` for every vertex `v`.
3. Prove the triangle-free leaf estimate
   `Ls H ≥ 4 * |E(H)| / |V(H)| - 2` using double-stars and Cauchy--Schwarz.
4. Use monotonicity of `Ls` under taking spanning supergraphs.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite graph has a triangle-free subgraph with maximum edge count among
all triangle-free subgraphs contained in it. Since all graphs here have the
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

/-- If a connected graph `G` has a disconnected spanning subgraph `H`, some
edge of `G` joins two distinct connected components of `H`. -/
lemma exists_adj_not_reachable_of_connected_of_not_connected
    (G H : SimpleGraph α) (hG : G.Connected) (hH : ¬ H.Connected) :
    ∃ a b : α, G.Adj a b ∧ ¬ H.Reachable a b := by
  classical
  by_contra h
  push_neg at h
  apply hH
  letI := hG.nonempty
  refine ⟨?_⟩
  intro u v
  exact (hG u v).elim fun p => by
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj p ih => exact (h _ _ hadj).trans ih

/-- Adding an edge between distinct components of a triangle-free graph cannot
create a triangle. -/
lemma cliqueFree_sup_edge_of_not_reachable
    (H : SimpleGraph α) (hHtri : H.CliqueFree 3) {a b : α}
    (hunreach : ¬ H.Reachable a b) :
    (H ⊔ SimpleGraph.edge a b).CliqueFree 3 := by
  classical
  have hnew :
      ∀ {x y z : α},
        (SimpleGraph.edge a b).Adj x y →
        (H ⊔ SimpleGraph.edge a b).Adj x z →
        (H ⊔ SimpleGraph.edge a b).Adj y z →
        H.Reachable a b := by
    intro x y z hxy hxz hyz
    rcases (SimpleGraph.edge_adj a b x y).mp hxy with ⟨hxy, hab⟩
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have haz : H.Adj a z := by
        rcases hxz with hxz | hxz
        · exact hxz
        · have hz : z = b := by simpa [SimpleGraph.edge_adj, hab] using hxz
          subst z
          exact False.elim ((H ⊔ SimpleGraph.edge a b).loopless b hyz)
      have hbz : H.Adj b z := by
        rcases hyz with hyz | hyz
        · exact hyz
        · have hz : z = a := by simpa [SimpleGraph.edge_adj, hab] using hyz
          subst z
          exact False.elim ((H ⊔ SimpleGraph.edge a b).loopless a hxz)
      exact haz.reachable.trans hbz.symm.reachable
    · have hbz : H.Adj b z := by
        rcases hxz with hxz | hxz
        · exact hxz
        · have hz : z = a := by simpa [SimpleGraph.edge_adj, hab.symm] using hxz
          subst z
          exact False.elim ((H ⊔ SimpleGraph.edge a b).loopless a hyz)
      have haz : H.Adj a z := by
        rcases hyz with hyz | hyz
        · exact hyz
        · have hz : z = b := by simpa [SimpleGraph.edge_adj, hab.symm] using hyz
          subst z
          exact False.elim ((H ⊔ SimpleGraph.edge a b).loopless b hxz)
      exact haz.reachable.trans hbz.symm.reachable
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  simp only [SimpleGraph.sup_adj] at hxy hxz hyz
  rcases hxy with hxy | hxy
  · rcases hxz with hxz | hxz
    · rcases hyz with hyz | hyz
      · exact hHtri {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
      · exact hunreach (hnew hyz (Or.inl hxy.symm) (Or.inl hxz.symm))
    · exact hunreach (hnew hxz (Or.inl hxy) hyz.symm)
  · exact hunreach (hnew hxy hxz hyz)

/-- Every maximum-edge triangle-free spanning subgraph of a connected graph is
connected. -/
lemma connected_of_maxEdge_triangleFree
    (G H : SimpleGraph α) (hG : G.Connected) (hHG : H ≤ G)
    (hHtri : H.CliqueFree 3)
    (hmax : ∀ K : SimpleGraph α,
      K ≤ G → K.CliqueFree 3 → K.edgeFinset.card ≤ H.edgeFinset.card) :
    H.Connected := by
  classical
  by_contra hHconn
  obtain ⟨a, b, hab, hunreach⟩ :=
    exists_adj_not_reachable_of_connected_of_not_connected G H hG hHconn
  have hne : a ≠ b := hab.ne
  have hnH : ¬ H.Adj a b := fun h => hunreach h.reachable
  let K : SimpleGraph α := H ⊔ SimpleGraph.edge a b
  have hKG : K ≤ G := by
    refine sup_le hHG ?_
    exact (SimpleGraph.edge_le_iff).2 (Or.inr hab)
  have hKtri : K.CliqueFree 3 :=
    cliqueFree_sup_edge_of_not_reachable H hHtri hunreach
  have hcard_le := hmax K hKG hKtri
  have hcard_eq : K.edgeFinset.card = H.edgeFinset.card + 1 := by
    exact H.card_edgeFinset_sup_edge hnH hne
  omega

lemma maxEdgeTriangleFreeSubgraph_connected
    (G : SimpleGraph α) (hG : G.Connected) :
    (maxEdgeTriangleFreeSubgraph G).Connected := by
  apply connected_of_maxEdge_triangleFree G (maxEdgeTriangleFreeSubgraph G) hG
  · exact maxEdgeTriangleFreeSubgraph_le G
  · exact maxEdgeTriangleFreeSubgraph_cliqueFree G
  · intro K hKG hKtri
    exact card_edgeFinset_le_maxEdgeTriangleFreeSubgraph G K hKG hKtri

end WrittenOnTheWallII.GraphConjecture2.Alternative
