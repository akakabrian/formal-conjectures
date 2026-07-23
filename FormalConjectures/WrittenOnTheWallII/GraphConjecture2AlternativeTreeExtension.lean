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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture2AlternativeAverageBound
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree

/-!
# Spanning-tree extension for the alternative proof of WOWII Conjecture 2

This file records two generic facts needed for the triangle-free leaf bound:
an acyclic subgraph of a connected graph extends to a spanning tree, and the
leaf count of any spanning tree is bounded above by `Ls`.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every acyclic subgraph of a connected graph is contained in a spanning
tree of that graph. Since all simple graphs here use the same vertex type,
`IsTree T` already means that the resulting tree spans every vertex. -/
lemma exists_isTree_le_containing
    (G F : SimpleGraph α) (hG : G.Connected)
    (hFG : F ≤ G) (hFacyc : F.IsAcyclic) :
    ∃ T : SimpleGraph α, T ≤ G ∧ T.IsTree ∧ F ≤ T := by
  obtain ⟨T, hFT, hmax⟩ :=
    G.exists_maximal_isAcyclic_of_le_isAcyclic hFG hFacyc
  have hTG : T ≤ G := hmax.prop.1
  have hTtree : T.IsTree :=
    (hG.maximal_le_isAcyclic_iff_isTree hTG).mp hmax
  exact ⟨T, hTG, hTtree, hFT⟩

/-- The number of degree-one vertices in any spanning tree of `G` is at most
`Ls G`. -/
lemma leafCount_le_Ls_of_isTree_le
    (G T : SimpleGraph α) (hTG : T ≤ G) (hTtree : T.IsTree) :
    ((Finset.univ.filter (fun v => T.degree v = 1)).card : ℝ) ≤ G.Ls := by
  classical
  let S : G.Subgraph := SimpleGraph.toSubgraph T hTG
  have hspan : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have htreeSpan : S.spanningCoe.IsTree := by
    simpa [S] using hTtree
  have htreeCoe : S.coe.IsTree :=
    (S.spanningCoeEquivCoeOfSpanning hspan).isTree_iff.mp htreeSpan
  unfold SimpleGraph.Ls
  apply le_csSup
  · refine ⟨Fintype.card α, ?_⟩
    rintro x ⟨U, hU, rfl⟩
    exact_mod_cast
      (Finset.card_le_univ
        (U.verts.toFinset.filter (fun v => U.degree v = 1)))
  · refine ⟨S, ⟨hspan, htreeCoe⟩, ?_⟩
    simp [S]

end WrittenOnTheWallII.GraphConjecture2.Alternative
