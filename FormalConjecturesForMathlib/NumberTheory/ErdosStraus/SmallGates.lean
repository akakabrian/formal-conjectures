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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.DivisorResidues

@[expose] public section

/-!
# Small Type-II gates

The first Type-II offset is `d = 3`. A divisor congruent to `2 mod 3` pairs
with `1`, giving opposite divisor residues.
-/

namespace ErdosStraus

/-- A divisor `q ≡ 2 mod 3` supplies the normalized opposite pair `(1,q)`. -/
theorem oppositeCoprimeDivisors_three_of_divisor_mod_three_two
    (x q : ℕ) (hq : q ∣ x) (hqmod : q % 3 = 2) :
    HasOppositeCoprimeDivisors x 3 := by
  have hqdiv := Nat.mod_add_div q 3
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 3 * k + 2 := by
    exact ⟨q / 3, by omega⟩
  refine ⟨1, q, by omega, by omega, by simp, by simp, hq, ?_⟩
  refine ⟨k + 1, ?_⟩
  omega

/-- The `d = 3` divisor gate gives a strict Erdős–Straus decomposition. -/
theorem dThree_gate_hasDistinctDecomposition
    (p x q : ℕ) (hp : 3 < p) (hx : 0 < x)
    (hpd : p + 3 = 4 * x) (hq : q ∣ x) (hqmod : q % 3 = 2) :
    HasDistinctDecomposition p := by
  apply oppositeCoprimeDivisors_hasDistinctDecomposition p 3 x (by omega) hx hp hpd
  exact oppositeCoprimeDivisors_three_of_divisor_mod_three_two x q hq hqmod

end ErdosStraus
