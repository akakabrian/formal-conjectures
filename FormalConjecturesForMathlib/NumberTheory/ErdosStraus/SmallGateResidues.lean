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
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

/-!
# Prime-factor residue structure of the first Type-II gates

The `d=3` and `d=7` gates admit exact descriptions in terms of prime-factor
residue classes. For `d=7`, the relevant subgroup is the quadratic residues
`{1,2,4}` modulo `7`.
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

/-- If every prime divisor of a positive integer is `1 mod 3`, so is the integer. -/
theorem mod_three_eq_one_of_prime_divisors_mod_three_one
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ n → q % 3 = 1) :
    n % 3 = 1 := by
  revert hn hprime
  induction n using induction_on_primes with
  | zero => intro hn; omega
  | one => intro _ _; norm_num
  | prime_mul p a hp ih =>
      intro hpa hprime
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        simp at hpa
      have ha : 0 < a := Nat.pos_of_ne_zero ha0
      have hpmod : p % 3 = 1 := hprime p hp (dvd_mul_right p a)
      have hamod : a % 3 = 1 := by
        apply ih ha
        intro q hq hqa
        exact hprime q hq (hqa.trans (dvd_mul_left a p))
      simpa [Nat.mul_mod, hpmod, hamod]

/-- If all prime divisors of `x` are `1 mod 3`, the `d=3` gate fails. -/
theorem not_hasOppositeCoprimeDivisors_three_of_prime_divisors_mod_three_one
    (x : ℕ) (hx : 0 < x)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ x → q % 3 = 1) :
    ¬ HasOppositeCoprimeDivisors x 3 := by
  rintro ⟨a, b, ha, hab, _, hax, hbx, hdab⟩
  have hb : 0 < b := lt_trans ha hab
  have hamod : a % 3 = 1 :=
    mod_three_eq_one_of_prime_divisors_mod_three_one a ha fun q hq hqa =>
      hprime q hq (hqa.trans hax)
  have hbmod : b % 3 = 1 :=
    mod_three_eq_one_of_prime_divisors_mod_three_one b hb fun q hq hqb =>
      hprime q hq (hqb.trans hbx)
  have hsum : (a + b) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdab
  have hadd := Nat.add_mod a b 3
  omega

/-- Exact prime-factor characterization of the `d=3` gate. -/
theorem hasOppositeCoprimeDivisors_three_iff_exists_prime_divisor_mod_three_two
    (x : ℕ) (hx : 0 < x) (hxmod : x % 3 = 1) :
    HasOppositeCoprimeDivisors x 3 ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧ q % 3 = 2 := by
  constructor
  · intro hgate
    by_contra hex
    have hall : ∀ q : ℕ, q.Prime → q ∣ x → q % 3 = 1 := by
      intro q hq hqx
      have hlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
      have hne2 : q % 3 ≠ 2 := by
        intro hq2
        exact hex ⟨q, hq, hqx, hq2⟩
      have hne0 : q % 3 ≠ 0 := by
        intro hq0
        have h3q : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hq0
        rcases hq.eq_one_or_self_of_dvd 3 h3q with h31 | h3q
        · norm_num at h31
        · have h3x : 3 ∣ x := by
            rw [h3q]
            exact hqx
          have hx0 : x % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3x
          omega
      omega
    exact (not_hasOppositeCoprimeDivisors_three_of_prime_divisors_mod_three_one
      x hx hall) hgate
  · rintro ⟨q, _, hqx, hqmod⟩
    exact oppositeCoprimeDivisors_three_of_divisor_mod_three_two x q hqx hqmod

/-- The unit quadratic residues modulo `7`. -/
def IsSevenSquareResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 2 ∨ r = 4

/-- The residues `{1,2,4}` are closed under multiplication modulo `7`. -/
theorem isSevenSquareResidue_mul_mod
    (a b : ℕ) (ha : IsSevenSquareResidue (a % 7))
    (hb : IsSevenSquareResidue (b % 7)) :
    IsSevenSquareResidue ((a * b) % 7) := by
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [IsSevenSquareResidue, Nat.mul_mod, ha, hb]

/-- If every prime divisor lies in `{1,2,4} mod 7`, so does the positive integer. -/
theorem isSevenSquareResidue_mod_of_prime_divisors
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ n → IsSevenSquareResidue (q % 7)) :
    IsSevenSquareResidue (n % 7) := by
  revert hn hprime
  induction n using induction_on_primes with
  | zero => intro hn; omega
  | one => intro _ _; simp [IsSevenSquareResidue]
  | prime_mul p a hp ih =>
      intro hpa hprime
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        simp at hpa
      have ha : 0 < a := Nat.pos_of_ne_zero ha0
      have hpmod : IsSevenSquareResidue (p % 7) :=
        hprime p hp (dvd_mul_right p a)
      have hamod : IsSevenSquareResidue (a % 7) := by
        apply ih ha
        intro q hq hqa
        exact hprime q hq (hqa.trans (dvd_mul_left a p))
      exact isSevenSquareResidue_mul_mod p a hpmod hamod

/-- If all prime divisors are square residues modulo `7`, the `d=7` gate fails. -/
theorem not_hasOppositeCoprimeDivisors_seven_of_prime_divisors_square_residue
    (x : ℕ) (hx : 0 < x)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ x → IsSevenSquareResidue (q % 7)) :
    ¬ HasOppositeCoprimeDivisors x 7 := by
  rintro ⟨a, b, ha, hab, _, hax, hbx, hdab⟩
  have hb : 0 < b := lt_trans ha hab
  have hamod := isSevenSquareResidue_mod_of_prime_divisors a ha fun q hq hqa =>
    hprime q hq (hqa.trans hax)
  have hbmod := isSevenSquareResidue_mod_of_prime_divisors b hb fun q hq hqb =>
    hprime q hq (hqb.trans hbx)
  have hsum : (a + b) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdab
  have hadd := Nat.add_mod a b 7
  rcases hamod with ha1 | ha2 | ha4 <;>
    rcases hbmod with hb1 | hb2 | hb4 <;> omega

/-- Exact prime-factor characterization of the `d=7` gate for even `x` coprime to `7`. -/
theorem hasOppositeCoprimeDivisors_seven_iff_exists_prime_divisor_nonresidue
    (x : ℕ) (hx : 0 < x) (h2x : 2 ∣ x) (h7x : Nat.Coprime 7 x) :
    HasOppositeCoprimeDivisors x 7 ↔
      ∃ q : ℕ, q.Prime ∧ q ∣ x ∧
        (q % 7 = 3 ∨ q % 7 = 5 ∨ q % 7 = 6) := by
  constructor
  · intro hgate
    by_contra hex
    have hall : ∀ q : ℕ, q.Prime → q ∣ x → IsSevenSquareResidue (q % 7) := by
      intro q hq hqx
      have hlt : q % 7 < 7 := Nat.mod_lt q (by norm_num)
      have hne3 : q % 7 ≠ 3 := by
        intro hq3
        exact hex ⟨q, hq, hqx, Or.inl hq3⟩
      have hne5 : q % 7 ≠ 5 := by
        intro hq5
        exact hex ⟨q, hq, hqx, Or.inr (Or.inl hq5)⟩
      have hne6 : q % 7 ≠ 6 := by
        intro hq6
        exact hex ⟨q, hq, hqx, Or.inr (Or.inr hq6)⟩
      have hne0 : q % 7 ≠ 0 := by
        intro hq0
        have h7q : 7 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hq0
        rcases hq.eq_one_or_self_of_dvd 7 h7q with h71 | h7q
        · norm_num at h71
        · have h7divx : 7 ∣ x := by
            rw [h7q]
            exact hqx
          exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) (by simp) h7divx) h7x
      dsimp [IsSevenSquareResidue]
      omega
    exact (not_hasOppositeCoprimeDivisors_seven_of_prime_divisors_square_residue
      x hx hall) hgate
  · rintro ⟨q, hqprime, hqx, hqmod⟩
    exact oppositeCoprimeDivisors_seven_of_prime_divisor_nonresidue
      x q h2x hqprime hqx hqmod

end ErdosStraus
