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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Basic

@[expose] public section

/-!
# Type-II factor-pair certificates

If positive integers satisfy

`p + d = 4 * a * b * c` and `a + b = d * s`,

then `a*b*c`, `p*a*c*s`, and `p*b*c*s` give an Erdős–Straus decomposition
for `p`.
-/

namespace ErdosStraus

/-- The polynomial identity underlying the Type-II factor-pair certificate. -/
theorem typeII_factor_pair_identity
    (p a b c s d : ℕ)
    (hab : a + b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    4 * (a * b * c) * (p * a * c * s) * (p * b * c * s) =
      p * ((a * b * c) * (p * a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (p * a * c * s) * (p * b * c * s)) := by
  calc
    4 * (a * b * c) * (p * a * c * s) * (p * b * c * s)
        = 4 * p ^ 2 * a ^ 2 * b ^ 2 * c ^ 3 * s ^ 2 := by ring
    _ = p ^ 2 * a * b * c ^ 2 * s * ((p + d) * s) := by
      rw [hpd]
      ring
    _ = p ^ 2 * a * b * c ^ 2 * s * (p * s + (a + b)) := by
      rw [hab]
      ring
    _ = p * ((a * b * c) * (p * a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (p * a * c * s) * (p * b * c * s)) := by ring

/-- A positive factor-pair certificate produces a positive decomposition. -/
theorem typeII_factor_pair_hasDecomposition
    (p a b c s d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (hab : a + b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    HasDecomposition p := by
  refine ⟨a * b * c, p * a * c * s, p * b * c * s, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · exact typeII_factor_pair_identity p a b c s d hab hpd

/--
A positive factor-pair certificate with `a < b < p*s` produces the exact
strictly ordered formulation.
-/
theorem typeII_factor_pair_hasDistinctDecomposition
    (p a b c s d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (ha_lt_b : a < b) (hb_lt_ps : b < p * s)
    (hab : a + b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    HasDistinctDecomposition p := by
  have habc : 0 < a * b * c := by positivity
  have hac : 0 < a * c := by positivity
  have hpcs : 0 < p * c * s := by positivity
  refine ⟨a * b * c, p * a * c * s, p * b * c * s, ?_, ?_, ?_, ?_⟩
  · omega
  · calc
      a * b * c = (a * c) * b := by ring
      _ < (a * c) * (p * s) := Nat.mul_lt_mul_of_pos_left hb_lt_ps hac
      _ = p * a * c * s := by ring
  · calc
      p * a * c * s = (p * c * s) * a := by ring
      _ < (p * c * s) * b := Nat.mul_lt_mul_of_pos_left ha_lt_b hpcs
      _ = p * b * c * s := by ring
  · exact typeII_factor_pair_identity p a b c s d hab hpd

end ErdosStraus
