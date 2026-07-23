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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture2AlternativeTreeExtension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Tree leaf counting for the alternative proof of WOWII Conjecture 2

For an edge `uv` of a finite tree, the number of leaves is at least
`degree u + degree v - 2`. The proof partitions vertices into leaves and
non-leaves and uses the degree-sum identity.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma tree_pair_degree_le_leafCount_add_two
    (T : SimpleGraph α) (hT : T.IsTree) {u v : α} (huv : T.Adj u v) :
    (T.degree u : ℤ) + T.degree v ≤
      ((Finset.univ.filter (fun x => T.degree x = 1)).card : ℤ) + 2 := by
  classical
  let L : Finset α := Finset.univ.filter (fun x => T.degree x = 1)
  let I : Finset α := Finset.univ.filter (fun x => T.degree x ≠ 1)
  let f : α → ℤ := fun x => (T.degree x : ℤ) - 2
  haveI : Nontrivial α := ⟨⟨u, v, huv.ne⟩⟩
  have huniv : (Finset.univ : Finset α) = L ∪ I := by
    rw [L, I, Finset.filter_union_filter_neg_eq]
  have hdisj : Disjoint L I := by
    exact Finset.disjoint_filter_filter_neg
  have hedge := hT.card_edgeFinset
  have hsumdegNat := T.sum_degrees_eq_twice_card_edges
  have hedgeZ : (T.edgeFinset.card : ℤ) + 1 = Fintype.card α := by
    exact_mod_cast hedge
  have hsumdegZ :
      (∑ x, (T.degree x : ℤ)) = 2 * (Fintype.card α : ℤ) - 2 := by
    calc
      (∑ x, (T.degree x : ℤ)) = ((∑ x, T.degree x : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
      _ = (2 * T.edgeFinset.card : ℕ) := by rw [hsumdegNat]
      _ = 2 * (T.edgeFinset.card : ℤ) := by norm_num
      _ = 2 * (Fintype.card α : ℤ) - 2 := by omega
  have hsumdiff : (∑ x, f x) = -2 := by
    rw [show (∑ x, f x) = (∑ x, (T.degree x : ℤ)) - ∑ _x : α, (2 : ℤ) by
      simp [f, Finset.sum_sub_distrib]]
    rw [hsumdegZ]
    simp [nsmul_eq_mul]
    ring
  have hsplit : (∑ x, f x) = (∑ x ∈ L, f x) + ∑ x ∈ I, f x := by
    rw [huniv, Finset.sum_union hdisj]
  have hsumL : (∑ x ∈ L, f x) = -(L.card : ℤ) := by
    calc
      (∑ x ∈ L, f x) = ∑ _x ∈ L, (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx1 : T.degree x = 1 := (Finset.mem_filter.mp hx).2
        simp [f, hx1]
      _ = -(L.card : ℤ) := by simp
  have hnonneg : ∀ x ∈ I, 0 ≤ f x := by
    intro x hx
    have hpos : 0 < T.degree x :=
      hT.isConnected.preconnected.degree_pos_of_nontrivial x
    have hne : T.degree x ≠ 1 := (Finset.mem_filter.mp hx).2
    have htwo : 2 ≤ T.degree x := by omega
    dsimp [f]
    exact sub_nonneg.mpr (by exact_mod_cast htwo)
  have hleaf : (L.card : ℤ) = 2 + ∑ x ∈ I, f x := by
    linarith [hsumdiff, hsplit, hsumL]
  have hLnonneg : 0 ≤ (L.card : ℤ) := by positivity
  by_cases huI : u ∈ I
  · by_cases hvI : v ∈ I
    · have hpair : f u + f v ≤ ∑ x ∈ I, f x := by
        exact I.add_le_sum hnonneg huI hvI huv.ne
      change (T.degree u : ℤ) + T.degree v ≤ (L.card : ℤ) + 2
      dsimp [f] at hpair
      omega
    · have hv1 : T.degree v = 1 := by simpa [I] using hvI
      have huBound : f u ≤ ∑ x ∈ I, f x := I.single_le_sum hnonneg huI
      change (T.degree u : ℤ) + T.degree v ≤ (L.card : ℤ) + 2
      dsimp [f] at huBound
      omega
  · have hu1 : T.degree u = 1 := by simpa [I] using huI
    by_cases hvI : v ∈ I
    · have hvBound : f v ≤ ∑ x ∈ I, f x := I.single_le_sum hnonneg hvI
      change (T.degree u : ℤ) + T.degree v ≤ (L.card : ℤ) + 2
      dsimp [f] at hvBound
      omega
    · have hv1 : T.degree v = 1 := by simpa [I] using hvI
      change (T.degree u : ℤ) + T.degree v ≤ (L.card : ℤ) + 2
      omega

lemma tree_pair_degree_sub_two_le_leafCount
    (T : SimpleGraph α) (hT : T.IsTree) {u v : α} (huv : T.Adj u v) :
    (T.degree u : ℝ) + T.degree v - 2 ≤
      ((Finset.univ.filter (fun x => T.degree x = 1)).card : ℝ) := by
  have h := tree_pair_degree_le_leafCount_add_two T hT huv
  exact_mod_cast h

end WrittenOnTheWallII.GraphConjecture2.Alternative
