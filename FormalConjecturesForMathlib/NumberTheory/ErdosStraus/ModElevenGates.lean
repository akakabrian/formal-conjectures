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
# Prime-factor triggers for the `d=11` gate

For a residual prime `p ≡ 1 mod 24`, the offset variable
`x=(p+11)/4` is divisible by `3`. This fixed divisor turns prime-factor
residues `7`, `8`, and `10 mod 11` into explicit opposite-divisor pairs.
-/

namespace ErdosStraus

/-- A divisor `q ≡ 10 mod 11` supplies the pair `(1,q)`. -/
theorem oppositeCoprimeDivisors_eleven_of_divisor_mod_ten
    (x q : ℕ) (hqx : q ∣ x) (hqmod : q % 11 = 10) :
    HasOppositeCoprimeDivisors x 11 := by
  have hqdiv := Nat.mod_add_div q 11
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 11 * k + 10 := by
    exact ⟨q / 11, by omega⟩
  refine ⟨1, q, by omega, by omega, by simp, by simp, hqx, ?_⟩
  refine ⟨k + 1, ?_⟩
  omega

/-- Divisors `3` and `q ≡ 8 mod 11` are opposite modulo `11`. -/
theorem oppositeCoprimeDivisors_eleven_of_three_and_divisor_mod_eight
    (x q : ℕ) (h3x : 3 ∣ x) (hqx : q ∣ x)
    (hcop : Nat.Coprime 3 q) (hqmod : q % 11 = 8) :
    HasOppositeCoprimeDivisors x 11 := by
  have hqdiv := Nat.mod_add_div q 11
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 11 * k + 8 := by
    exact ⟨q / 11, by omega⟩
  refine ⟨3, q, by omega, ?_, hcop, h3x, hqx, ?_⟩
  · omega
  · refine ⟨k + 1, ?_⟩
    omega

/-- If `3q ∣ x` and `q ≡ 7 mod 11`, the pair `(1,3q)` is opposite modulo `11`. -/
theorem oppositeCoprimeDivisors_eleven_of_three_times_divisor_mod_seven
    (x q : ℕ) (h3qx : 3 * q ∣ x) (hqmod : q % 11 = 7) :
    HasOppositeCoprimeDivisors x 11 := by
  have hqdiv := Nat.mod_add_div q 11
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 11 * k + 7 := by
    exact ⟨q / 11, by omega⟩
  refine ⟨1, 3 * q, by omega, by omega, by simp, by simp, h3qx, ?_⟩
  refine ⟨3 * k + 2, ?_⟩
  omega

/-- A prime other than `3` is coprime to `3`. -/
theorem coprime_three_of_prime_ne_three
    (q : ℕ) (hqprime : q.Prime) (hqne3 : q ≠ 3) :
    Nat.Coprime 3 q := by
  have hnot : ¬ 3 ∣ q := by
    intro h3q
    rcases hqprime.eq_one_or_self_of_dvd 3 h3q with h31 | h3qeq
    · norm_num at h31
    · exact hqne3 h3qeq.symm
  exact (by
    have h3prime : Nat.Prime 3 := by norm_num
    exact h3prime.coprime_iff_not_dvd.mpr hnot)

/--
When `3 ∣ x`, a prime divisor in any of the classes `7,8,10 mod 11`
triggers the `d=11` opposite-divisor certificate.
-/
theorem oppositeCoprimeDivisors_eleven_of_prime_divisor_trigger
    (x q : ℕ) (h3x : 3 ∣ x) (hqprime : q.Prime) (hqx : q ∣ x)
    (hqmod : q % 11 = 7 ∨ q % 11 = 8 ∨ q % 11 = 10) :
    HasOppositeCoprimeDivisors x 11 := by
  rcases hqmod with hq7 | hq8 | hq10
  · have hqne3 : q ≠ 3 := by
      intro hq3
      subst q
      norm_num at hq7
    have hcop : Nat.Coprime 3 q := coprime_three_of_prime_ne_three q hqprime hqne3
    have h3qx : 3 * q ∣ x := hcop.mul_dvd_of_dvd_of_dvd h3x hqx
    exact oppositeCoprimeDivisors_eleven_of_three_times_divisor_mod_seven x q h3qx hq7
  · have hqne3 : q ≠ 3 := by
      intro hq3
      subst q
      norm_num at hq8
    have hcop : Nat.Coprime 3 q := coprime_three_of_prime_ne_three q hqprime hqne3
    exact oppositeCoprimeDivisors_eleven_of_three_and_divisor_mod_eight
      x q h3x hqx hcop hq8
  · exact oppositeCoprimeDivisors_eleven_of_divisor_mod_ten x q hqx hq10

/-- If `p ≡ 1 mod 24` and `p+11=4x`, then `3 ∣ x`. -/
theorem three_dvd_offset_eleven_of_mod_twenty_four_one
    (p x : ℕ) (hpmod : p % 24 = 1) (hpx : p + 11 = 4 * x) :
    3 ∣ x := by
  have hpdiv := Nat.mod_add_div p 24
  refine ⟨2 * (p / 24) + 1, ?_⟩
  omega

/-- The prime-factor trigger gives a strict `d=11` decomposition. -/
theorem dEleven_gate_hasDistinctDecomposition
    (p x q : ℕ) (hp : 11 < p) (hx : 0 < x)
    (hpx : p + 11 = 4 * x) (h3x : 3 ∣ x)
    (hqprime : q.Prime) (hqx : q ∣ x)
    (hqmod : q % 11 = 7 ∨ q % 11 = 8 ∨ q % 11 = 10) :
    HasDistinctDecomposition p := by
  apply oppositeCoprimeDivisors_hasDistinctDecomposition p 11 x (by omega) hx hp hpx
  exact oppositeCoprimeDivisors_eleven_of_prime_divisor_trigger
    x q h3x hqprime hqx hqmod

end ErdosStraus
