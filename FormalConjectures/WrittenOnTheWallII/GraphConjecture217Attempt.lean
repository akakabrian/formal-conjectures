/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture217

/-!
# WOWII Conjecture 217 isolated formalization attempt

This scratch module preserves the upstream target and records only kernel-checkable
reductions. It is intentionally kept off `main` and is not a submission artifact.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- A graph has a Hamiltonian path in the exact form used by Conjecture 217. -/
abbrev HasHamiltonianPath (G : SimpleGraph α) : Prop :=
  ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

/-- The indicator is one exactly in the residue-two branch. -/
@[category test, AMS 5]
theorem residueEqTwoIndicator_eq_one_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 1 ↔ residue G = 2 := by
  simp [residueEqTwoIndicator]

/-- The indicator is zero exactly outside the residue-two branch. -/
@[category test, AMS 5]
theorem residueEqTwoIndicator_eq_zero_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 0 ↔ residue G ≠ 2 := by
  simp [residueEqTwoIndicator]

/-- Outside the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 2`. -/
@[category test, AMS 5]
theorem Ls_le_two_of_residue_ne_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G ≠ 2) : Ls G ≤ 2 := by
  simpa [residueEqTwoIndicator, hr] using hL

/-- In the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 6`. -/
@[category test, AMS 5]
theorem Ls_le_six_of_residue_eq_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G = 2) : Ls G ≤ 6 := by
  norm_num [residueEqTwoIndicator, hr] at hL
  exact hL

/-- Every individual spanning-tree leaf count is bounded by the `sSup` defining `Ls`. -/
@[category test, AMS 5]
theorem spanningTree_leafCount_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : G.Subgraph) (hT : T.IsSpanning ∧ IsTree T.coe) :
    ((T.verts.toFinset.filter (fun v => T.degree v = 1)).card : ℝ) ≤ Ls G := by
  classical
  unfold Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro x ⟨S, hS, rfl⟩
    change ((S.verts.toFinset.filter (fun v => S.degree v = 1)).card : ℝ) ≤
      (Fintype.card α : ℝ)
    exact_mod_cast
      (Finset.card_le_univ (S.verts.toFinset.filter (fun v => S.degree v = 1)))
  · exact ⟨T, hT, rfl⟩

/-- A connected graph with `Ls ≤ 2` has a concrete spanning tree with at most two leaves. -/
@[category test, AMS 5]
theorem exists_spanningTree_leafCount_le_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hL : Ls G ≤ 2) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧
        (T.verts.toFinset.filter (fun v => T.degree v = 1)).card ≤ 2 := by
  classical
  obtain ⟨T, hTG, hTtree⟩ := hG.exists_isTree_le
  let S : G.Subgraph := SimpleGraph.toSubgraph (G := G) T hTG
  have hSspan : S.IsSpanning := by
    simpa [S] using SimpleGraph.toSubgraph.isSpanning T hTG
  have hStree : IsTree S.coe := by
    apply (S.spanningCoeEquivCoeOfSpanning hSspan).isTree_iff.mp
    simpa [S, SimpleGraph.toSubgraph] using hTtree
  have hcountR := spanningTree_leafCount_le_Ls G S ⟨hSspan, hStree⟩
  refine ⟨S, hSspan, hStree, ?_⟩
  exact_mod_cast hcountR.trans hL

/-- The exact conjecture follows once its two mathematical branches are supplied. -/
@[category test, AMS 5]
theorem conjecture217_of_branch_theorems
    (hNonResidue :
      ∀ (H : SimpleGraph α) [DecidableRel H.Adj],
        H.Connected → Ls H ≤ 2 → HasHamiltonianPath H)
    (hResidueTwo :
      ∀ (H : SimpleGraph α) [DecidableRel H.Adj],
        H.Connected → residue H = 2 → Ls H ≤ 6 → HasHamiltonianPath H)
    (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    HasHamiltonianPath G := by
  by_cases hr : residue G = 2
  · exact hResidueTwo G h hr (Ls_le_six_of_residue_eq_two G hL hr)
  · exact hNonResidue G h (Ls_le_two_of_residue_ne_two G hL hr)

end WrittenOnTheWallII.GraphConjecture217
