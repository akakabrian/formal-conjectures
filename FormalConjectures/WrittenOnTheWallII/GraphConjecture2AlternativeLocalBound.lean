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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture2Alternative

/-!
# Local-degree step for the alternative proof of WOWII Conjecture 2

This file formalizes finite stars and the edge-counting infrastructure needed
to replace all edges incident to a vertex by edges to an independent subset of
its neighbourhood.
-/

namespace WrittenOnTheWallII.GraphConjecture2.Alternative

open Classical Finset SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The finite star with centre `v` and the vertices of `A` as its possible
leaves. Loops are discarded by `SimpleGraph.fromEdgeSet`. -/
def finsetStar (v : α) (A : Finset α) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet
    (↑(A.image (fun a => s(v, a))) : Set (Sym2 α))

lemma finsetStar_adj {v x y : α} {A : Finset α} (hv : v ∉ A) :
    (finsetStar v A).Adj x y ↔
      (x = v ∧ y ∈ A) ∨ (y = v ∧ x ∈ A) := by
  constructor
  · intro hxy
    rw [finsetStar, SimpleGraph.fromEdgeSet_adj] at hxy
    rcases hxy with ⟨hmem, _⟩
    change s(x, y) ∈ A.image (fun a => s(v, a)) at hmem
    rcases Finset.mem_image.mp hmem with ⟨a, ha, hae⟩
    rcases Sym2.eq_iff.mp hae with h | h
    · exact Or.inl ⟨h.1.symm, h.2 ▸ ha⟩
    · exact Or.inr ⟨h.1.symm, h.2 ▸ ha⟩
  · intro hxy
    rw [finsetStar, SimpleGraph.fromEdgeSet_adj]
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨hx, hy⟩
      subst x
      refine ⟨?_, ?_⟩
      · change s(v, y) ∈ A.image (fun a => s(v, a))
        exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      · intro h
        subst y
        exact hv hy
    · rcases hxy with ⟨hy, hx⟩
      subst y
      refine ⟨?_, ?_⟩
      · change s(x, v) ∈ A.image (fun a => s(v, a))
        exact Finset.mem_image.mpr ⟨x, hx, Sym2.eq_swap⟩
      · intro h
        subst x
        exact hv hx

lemma finsetStar_cliqueFree {v : α} {A : Finset α} (hv : v ∉ A) :
    (finsetStar v A).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  rw [finsetStar_adj hv] at hxy hxz hyz
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    subst x
    have hz : z ∈ A := by
      rcases hxz with hxz | hxz
      · exact hxz.2
      · exact False.elim (hv hxz.2)
    rcases hyz with hyz | hyz
    · exact hv (hyz.1 ▸ hy)
    · exact hv (hyz.1 ▸ hz)
  · rcases hxy with ⟨hy, hx⟩
    subst y
    have hz : z ∈ A := by
      rcases hyz with hyz | hyz
      · exact hyz.2
      · exact False.elim (hv hyz.2)
    rcases hxz with hxz | hxz
    · exact hv (hxz.1 ▸ hx)
    · exact hv (hxz.1 ▸ hz)

lemma finsetStar_le (G : SimpleGraph α) {v : α} {A : Finset α}
    (hA : ∀ a ∈ A, G.Adj v a) :
    finsetStar v A ≤ G := by
  have hv : v ∉ A := by
    intro hvA
    exact G.loopless v (hA v hvA)
  intro x y hxy
  rw [finsetStar_adj hv] at hxy
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    subst x
    exact hA y hy
  · rcases hxy with ⟨hy, hx⟩
    subst y
    exact (hA x hx).symm

lemma edgeFinset_finsetStar {v : α} {A : Finset α} (hv : v ∉ A) :
    (finsetStar v A).edgeFinset = A.image (fun a => s(v, a)) := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  rw [finsetStar, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro he
    exact he.1
  · intro he
    refine ⟨he, ?_⟩
    change e ∈ A.image (fun a => s(v, a)) at he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    rw [Sym2.mem_diagSet_iff_eq]
    intro hva
    exact hv (hva ▸ ha)

lemma card_edgeFinset_finsetStar {v : α} {A : Finset α} (hv : v ∉ A) :
    (finsetStar v A).edgeFinset.card = A.card := by
  rw [edgeFinset_finsetStar hv]
  apply Finset.card_image_of_injOn
  intro a ha b _ hab
  rcases Sym2.eq_iff.mp hab with h | h
  · exact h.2
  · exact False.elim (hv (h.2 ▸ ha))

end WrittenOnTheWallII.GraphConjecture2.Alternative
