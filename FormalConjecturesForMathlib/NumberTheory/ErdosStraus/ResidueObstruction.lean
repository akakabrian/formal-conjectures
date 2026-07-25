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
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

/-!
# Multiplicative residue obstructions to fixed Type-II gates

This file abstracts the prime-factor arguments used at offsets `d=3` and
`d=7`. If a residue property contains `1`, is closed under multiplication,
and contains no additive-opposite pair, then an integer whose prime factors
all have that property cannot have opposite coprime divisors modulo `d`.
-/

namespace ErdosStraus

/--
A multiplicatively closed residue property inherited by every prime divisor is
inherited by the positive integer itself.
-/
theorem residueProperty_mod_of_prime_divisors
    (d n : ℕ) (P : ℕ → Prop) (hn : 0 < n)
    (hone : P (1 % d))
    (hmul : ∀ a b : ℕ, P (a % d) → P (b % d) → P ((a * b) % d))
    (hprime : ∀ q : ℕ, q.Prime → q ∣ n → P (q % d)) :
    P (n % d) := by
  revert hn hprime
  induction n using induction_on_primes with
  | zero => intro hn; omega
  | one => intro _ _; simpa using hone
  | prime_mul p a hp ih =>
      intro hpa hprime
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        simp at hpa
      have ha : 0 < a := Nat.pos_of_ne_zero ha0
      have hpmod : P (p % d) := hprime p hp (dvd_mul_right p a)
      have hamod : P (a % d) := by
        apply ih ha
        intro q hq hqa
        exact hprime q hq (hqa.trans (dvd_mul_left a p))
      exact hmul p a hpmod hamod

/--
A multiplicatively closed residue property with no additive opposites is an
obstruction to `HasOppositeCoprimeDivisors`.
-/
theorem not_hasOppositeCoprimeDivisors_of_residueProperty
    (x d : ℕ) (P : ℕ → Prop) (hx : 0 < x)
    (hone : P (1 % d))
    (hmul : ∀ a b : ℕ, P (a % d) → P (b % d) → P ((a * b) % d))
    (hopp : ∀ r s : ℕ, P r → P s → (r + s) % d ≠ 0)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ x → P (q % d)) :
    ¬ HasOppositeCoprimeDivisors x d := by
  rintro ⟨a, b, ha, hab, _, hax, hbx, hdab⟩
  have hb : 0 < b := lt_trans ha hab
  have hamod : P (a % d) :=
    residueProperty_mod_of_prime_divisors d a P ha hone hmul fun q hq hqa =>
      hprime q hq (hqa.trans hax)
  have hbmod : P (b % d) :=
    residueProperty_mod_of_prime_divisors d b P hb hone hmul fun q hq hqb =>
      hprime q hq (hqb.trans hbx)
  have hsum : (a + b) % d = 0 := Nat.dvd_iff_mod_eq_zero.mp hdab
  have hres : (a % d + b % d) % d = 0 := by
    rw [← Nat.add_mod]
    exact hsum
  exact (hopp (a % d) (b % d) hamod hbmod) hres

end ErdosStraus
