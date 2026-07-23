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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture2AlternativeReplacement
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Averaged local-independence step for the alternative proof of WOWII Conjecture 2

A maximum independent set in each induced neighbourhood is transported back
to the original vertex type and bounded by the corresponding degree in the
maximum-edge triangle-free spanning subgraph. Summing and applying the degree
sum formula gives the global local-independence bound.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma indepNeighborsCard_le_degree_maxEdgeTriangleFreeSubgraph
    (G : SimpleGraph α) (v : α) :
    G.indepNeighborsCard v ≤ (maxEdgeTriangleFreeSubgraph G).degree v := by
  classical
  obtain ⟨s, hs⟩ :=
    (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  let e : {x // x ∈ G.neighborSet v} ↪ α :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let A : Finset α := s.map e
  have hAcard : A.card = G.indepNeighborsCard v := by
    unfold SimpleGraph.indepNeighborsCard
    calc
      A.card = s.card := by simp [A]
      _ = (G.induce (G.neighborSet v)).indepNum := hs.card_eq
  have hA : ∀ a ∈ A, G.Adj v a := by
    intro a ha
    rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
    exact a'.property
  have hAind : G.IsIndepSet (A : Set α) := by
    intro x hx y hy hxy
    have hxA : x ∈ A := Finset.mem_coe.mp hx
    have hyA : y ∈ A := Finset.mem_coe.mp hy
    rcases Finset.mem_map.mp hxA with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hyA with ⟨y', hy', rfl⟩
    intro hAdj
    exact (hs.isIndepSet
      (Finset.mem_coe.mpr hx')
      (Finset.mem_coe.mpr hy')
      (Subtype.coe_ne_coe.mp hxy)) hAdj
  calc
    G.indepNeighborsCard v = A.card := hAcard.symm
    _ ≤ (maxEdgeTriangleFreeSubgraph G).degree v :=
      indepSet_card_le_degree_maxEdgeTriangleFreeSubgraph G hA hAind

lemma sum_indepNeighborsCard_le_twice_edges
    (G : SimpleGraph α) :
    (∑ v, G.indepNeighborsCard v) ≤
      2 * (maxEdgeTriangleFreeSubgraph G).edgeFinset.card := by
  classical
  calc
    (∑ v, G.indepNeighborsCard v) ≤
        ∑ v, (maxEdgeTriangleFreeSubgraph G).degree v := by
      exact Finset.sum_le_sum fun v _ =>
        indepNeighborsCard_le_degree_maxEdgeTriangleFreeSubgraph G v
    _ = 2 * (maxEdgeTriangleFreeSubgraph G).edgeFinset.card :=
      (maxEdgeTriangleFreeSubgraph G).sum_degrees_eq_twice_card_edges

lemma sum_indepNeighbors_le_twice_edges
    (G : SimpleGraph α) :
    (∑ v, G.indepNeighbors v) ≤
      (2 * (maxEdgeTriangleFreeSubgraph G).edgeFinset.card : ℕ) := by
  classical
  simpa [SimpleGraph.indepNeighbors, ← Nat.cast_sum] using
    sum_indepNeighborsCard_le_twice_edges G

end WrittenOnTheWallII.GraphConjecture2.Alternative
