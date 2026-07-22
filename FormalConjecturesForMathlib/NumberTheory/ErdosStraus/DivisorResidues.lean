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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.TypeIIFactorPair

@[expose] public section

/-!
# Opposite divisor residues

A coprime pair of divisors `a,b ∣ x` with `a + b ≡ 0 (mod d)` is a normalized
Type-II certificate when `p + d = 4x`.
-/

namespace ErdosStraus

/-- A normalized pair of opposite divisor residues modulo `d`. -/
def HasOppositeCoprimeDivisors (x d : ℕ) : Prop :=
  ∃ a b : ℕ,
    0 < a ∧ a < b ∧ Nat.Coprime a b ∧ a ∣ x ∧ b ∣ x ∧ d ∣ a + b

/--
A normalized opposite-divisor pair gives a strictly ordered Type-II
Erdős–Straus certificate whenever `3 ≤ d < p` and `p+d=4x`.
-/
theorem oppositeCoprimeDivisors_hasDistinctDecomposition
    (p d x : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hd : 3 ≤ d) (hdp : d < p)
    (hpd : p + d = 4 * x)
    (h : HasOppositeCoprimeDivisors x d) :
    HasDistinctDecomposition p := by
  rcases h with ⟨a, b, ha, hab, hcop, hax, hbx, hdab⟩
  have habx : a * b ∣ x := hcop.mul_dvd_of_dvd_of_dvd hax hbx
  rcases habx with ⟨c, hxc⟩
  have hc : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    simp at hxc
    omega
  rcases hdab with ⟨s, habs⟩
  have hs : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
    subst s
    simp at habs
    omega
  have hps : d * s < p * s := (Nat.mul_lt_mul_right hs).2 hdp
  have hbds : b < d * s := by omega
  have hb_lt_ps : b < p * s := lt_trans hbds hps
  apply typeII_factor_pair_hasDistinctDecomposition p a b c s d hp ha
    (lt_trans ha hab) hc hs hab hb_lt_ps
  · exact habs
  · calc
      p + d = 4 * x := hpd
      _ = 4 * (a * b * c) := by rw [hxc]

end ErdosStraus
