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
module

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ElementaryFamilies
public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Scaling

@[expose] public section

/-!
# Reduction to the residue class `1 mod 24`

The elementary distinct-denominator families, together with scaling the
solution for `3`, cover every residue class modulo `24` except `1`.
-/

namespace ErdosStraus

/-- Every `n > 2` outside the residue class `1 mod 24` has a strict decomposition. -/
theorem hasDistinctDecomposition_of_mod_twenty_four_ne_one
    (n : ℕ) (hn : 2 < n) (hmod : n % 24 ≠ 1) :
    HasDistinctDecomposition n := by
  have hclasses :
      n % 2 = 0 ∨ n % 3 = 0 ∨ n % 3 = 2 ∨ n % 4 = 3 ∨ n % 8 = 5 := by
    omega
  rcases hclasses with h2 | h3 | h32 | h43 | h85
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = 2 * m := by omega
    subst n
    exact even_family m (by omega)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m * 3 := by omega
    subst n
    exact (mod_four_three_family 0).scale (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 3 * k + 2 := by omega
    subst n
    exact mod_three_two_family k (by omega)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 3 := by omega
    subst n
    exact mod_four_three_family k
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 8 * k + 5 := by omega
    subst n
    exact mod_eight_five_family k

/-- A counterexample above `2`, if one exists, is congruent to `1 mod 24`. -/
theorem counterexample_mod_twenty_four_eq_one
    (n : ℕ) (hn : 2 < n) (hnot : ¬ HasDistinctDecomposition n) :
    n % 24 = 1 := by
  by_contra hmod
  exact hnot (hasDistinctDecomposition_of_mod_twenty_four_ne_one n hn hmod)

end ErdosStraus
