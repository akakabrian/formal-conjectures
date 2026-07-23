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
# Normalizing a divisor of a square

This file connects the divisor certificate `q ∣ x²`, used in Type-II
parametrizations of the Erdős–Straus equation, to the coprime factor-pair
certificate in `DivisorResidues.lean`.
-/

namespace ErdosStraus

/--
A strict divisor-square residue certificate normalizes to a pair of coprime
opposite divisors. The coprimality hypothesis on `d` and `x` is the exact
cancellation condition needed to pass from `d ∣ q+x` to the normalized pair.
-/
theorem divisorSquare_hasOppositeCoprimeDivisors
    (x d q : ℕ)
    (hx : 0 < x) (hq : 0 < q) (hqx : q < x)
    (hqsq : q ∣ x ^ 2) (hdqx : d ∣ q + x)
    (hdx : Nat.Coprime d x) :
    HasOppositeCoprimeDivisors x d := by
  let g := Nat.gcd x q
  let a := q / g
  let b := x / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left q hx
  have hgx : g ∣ x := by
    dsimp [g]
    exact Nat.gcd_dvd_left x q
  have hgq : g ∣ q := by
    dsimp [g]
    exact Nat.gcd_dvd_right x q
  have hxgb : g * b = x := by
    dsimp [b]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hgx
  have hqga : g * a = q := by
    dsimp [a]
    simpa [Nat.mul_comm] using Nat.div_mul_cancel hgq
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.div_pos (Nat.gcd_le_right x hq) hgpos
  have hb : 0 < b := by
    dsimp [b]
    exact Nat.div_pos (Nat.gcd_le_left q hx) hgpos
  have hab : a < b := by
    apply (Nat.mul_lt_mul_left hgpos).mp
    simpa [hqga, hxgb] using hqx
  have hcop : Nat.Coprime a b := by
    dsimp [a, b, g]
    exact (Nat.coprime_div_gcd_div_gcd (m := x) (n := q)
      (Nat.gcd_pos_of_pos_left q hx)).symm
  have ha_dvd_gb_sq : a ∣ g * b ^ 2 := by
    apply (mul_dvd_mul_iff_left (Nat.ne_of_gt hgpos)).mp
    rw [hqga]
    convert hqsq using 1
    rw [← hxgb]
    ring
  have hag : a ∣ g :=
    (hcop.pow_right 2).dvd_of_dvd_mul_right ha_dvd_gb_sq
  rcases hag with ⟨c, hgc⟩
  have hax : a ∣ x := by
    refine ⟨c * b, ?_⟩
    rw [← hxgb, hgc]
    ring
  have hbx : b ∣ x := by
    refine ⟨g, ?_⟩
    simpa [Nat.mul_comm] using hxgb.symm
  have hd_gab : d ∣ g * (a + b) := by
    simpa [hqga, hxgb, Nat.mul_add] using hdqx
  have hdg : Nat.Coprime d g := hdx.coprime_dvd_right hgx
  have hdab : d ∣ a + b := hdg.dvd_of_dvd_mul_left hd_gab
  exact ⟨a, b, ha, hab, hcop, hax, hbx, hdab⟩

/--
A strict divisor-square residue certificate gives a strictly ordered
Erdős–Straus decomposition once the offset equation and size condition hold.
-/
theorem divisorSquare_hasDistinctDecomposition
    (p d x q : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hq : 0 < q) (hqx : q < x)
    (hdp : d < p) (hpd : p + d = 4 * x)
    (hqsq : q ∣ x ^ 2) (hdqx : d ∣ q + x)
    (hdx : Nat.Coprime d x) :
    HasDistinctDecomposition p :=
  oppositeCoprimeDivisors_hasDistinctDecomposition p d x hp hx hdp hpd
    (divisorSquare_hasOppositeCoprimeDivisors x d q hx hq hqx hqsq hdqx hdx)

/--
For a prime target, the offset `d = 4*x-p` is automatically coprime to `x`
whenever `0 < x < p`.
-/
theorem coprime_offset_of_prime
    (p d x : ℕ) (hp : p.Prime) (hx : 0 < x) (hxp : x < p)
    (hpd : p + d = 4 * x) :
    Nat.Coprime d x := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := Nat.gcd d x
  change g = 1
  have hgd : g ∣ d := by
    dsimp [g]
    exact Nat.gcd_dvd_left d x
  have hgx : g ∣ x := by
    dsimp [g]
    exact Nat.gcd_dvd_right d x
  have hg4x : g ∣ 4 * x := dvd_mul_of_dvd_right hgx 4
  have hgpd : g ∣ p + d := by simpa [hpd] using hg4x
  have hgdp : g ∣ d + p := by simpa [Nat.add_comm] using hgpd
  have hgp : g ∣ p := (Nat.dvd_add_iff_right hgd).2 hgdp
  rcases hp.eq_one_or_self_of_dvd g hgp with hg1 | hgeq
  · exact hg1
  · have hpx : p ∣ x := by simpa [hgeq] using hgx
    have hple : p ≤ x := Nat.le_of_dvd hx hpx
    omega

/--
Bradford's strict Type-II divisor-square certificate, specialized to a prime,
produces the exact distinct-denominator Erdős–Straus conclusion.
-/
theorem prime_divisorSquare_hasDistinctDecomposition
    (p d x q : ℕ)
    (hp : p.Prime) (hx : 0 < x) (hxp : x < p)
    (hq : 0 < q) (hqx : q < x)
    (hdp : d < p) (hpd : p + d = 4 * x)
    (hqsq : q ∣ x ^ 2) (hdqx : d ∣ q + x) :
    HasDistinctDecomposition p :=
  divisorSquare_hasDistinctDecomposition p d x q hp.pos hx hq hqx hdp hpd hqsq hdqx
    (coprime_offset_of_prime p d x hp hx hxp hpd)

end ErdosStraus
