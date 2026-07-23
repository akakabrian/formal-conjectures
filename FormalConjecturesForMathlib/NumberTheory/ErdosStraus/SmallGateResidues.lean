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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.SmallGates

@[expose] public section

/-!
# Prime-factor residue triggers for the `d = 7` gate

When `2 ∣ x`, a prime divisor of `x` in any quadratic-nonresidue class
`3,5,6 mod 7` gives an explicit pair of opposite coprime divisors.
-/

namespace ErdosStraus

/-- A divisor `q ≡ 6 mod 7` supplies the pair `(1,q)`. -/
theorem oppositeCoprimeDivisors_seven_of_divisor_mod_seven_six
    (x q : ℕ) (hqx : q ∣ x) (hqmod : q % 7 = 6) :
    HasOppositeCoprimeDivisors x 7 := by
  have hqdiv := Nat.mod_add_div q 7
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 7 * k + 6 := by
    exact ⟨q / 7, by omega⟩
  refine ⟨1, q, by omega, by omega, by simp, by simp, hqx, ?_⟩
  refine ⟨k + 1, ?_⟩
  omega

/-- Coprime divisors `2` and `q ≡ 5 mod 7` are opposite modulo `7`. -/
theorem oppositeCoprimeDivisors_seven_of_two_and_divisor_mod_seven_five
    (x q : ℕ) (h2x : 2 ∣ x) (hqx : q ∣ x)
    (hcop : Nat.Coprime 2 q) (hqmod : q % 7 = 5) :
    HasOppositeCoprimeDivisors x 7 := by
  have hqdiv := Nat.mod_add_div q 7
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 7 * k + 5 := by
    exact ⟨q / 7, by omega⟩
  refine ⟨2, q, by omega, by omega, hcop, h2x, hqx, ?_⟩
  refine ⟨k + 1, ?_⟩
  omega

/-- If `2q ∣ x` and `q ≡ 3 mod 7`, the pair `(1,2q)` is opposite modulo `7`. -/
theorem oppositeCoprimeDivisors_seven_of_twice_divisor_mod_seven_three
    (x q : ℕ) (h2qx : 2 * q ∣ x) (hqmod : q % 7 = 3) :
    HasOppositeCoprimeDivisors x 7 := by
  have hqdiv := Nat.mod_add_div q 7
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 7 * k + 3 := by
    exact ⟨q / 7, by omega⟩
  refine ⟨1, 2 * q, by omega, by omega, by simp, by simp, h2qx, ?_⟩
  refine ⟨2 * k + 1, ?_⟩
  omega

/--
For even `x`, a prime divisor in any of the classes `3,5,6 mod 7` triggers
the `d = 7` opposite-divisor certificate.
-/
theorem oppositeCoprimeDivisors_seven_of_prime_divisor_nonresidue
    (x q : ℕ) (h2x : 2 ∣ x) (hqprime : q.Prime) (hqx : q ∣ x)
    (hqmod : q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) :
    HasOppositeCoprimeDivisors x 7 := by
  rcases hqmod with hq3 | hq5 | hq6
  · have hqne2 : q ≠ 2 := by
      intro hq2
      subst q
      norm_num at hq3
    have hcop : Nat.Coprime 2 q :=
      Nat.coprime_two_left.mpr (hqprime.odd_of_ne_two hqne2)
    have h2qx : 2 * q ∣ x := hcop.mul_dvd_of_dvd_of_dvd h2x hqx
    exact oppositeCoprimeDivisors_seven_of_twice_divisor_mod_seven_three x q h2qx hq3
  · have hqne2 : q ≠ 2 := by
      intro hq2
      subst q
      norm_num at hq5
    have hcop : Nat.Coprime 2 q :=
      Nat.coprime_two_left.mpr (hqprime.odd_of_ne_two hqne2)
    exact oppositeCoprimeDivisors_seven_of_two_and_divisor_mod_seven_five
      x q h2x hqx hcop hq5
  · exact oppositeCoprimeDivisors_seven_of_divisor_mod_seven_six x q hqx hq6

/-- The prime-factor nonresidue test gives a strict `d = 7` decomposition. -/
theorem dSeven_gate_hasDistinctDecomposition
    (p x q : ℕ) (hp : 7 < p) (hx : 0 < x)
    (hpd : p + 7 = 4 * x) (h2x : 2 ∣ x)
    (hqprime : q.Prime) (hqx : q ∣ x)
    (hqmod : q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) :
    HasDistinctDecomposition p := by
  apply oppositeCoprimeDivisors_hasDistinctDecomposition p 7 x (by omega) hx hp hpd
  exact oppositeCoprimeDivisors_seven_of_prime_divisor_nonresidue
    x q h2x hqprime hqx hqmod

end ErdosStraus
