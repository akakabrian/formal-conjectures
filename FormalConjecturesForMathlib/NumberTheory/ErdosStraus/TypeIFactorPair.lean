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
# Type-I factor-pair certificates

If positive integers satisfy

`p + d = 4 * a * b * c` and `a + p * b = d * s`,

then `a*b*c`, `a*c*s`, and `p*b*c*s` give an Erdős–Straus decomposition
for `p`. This complements the Type-II factor-pair identity.
-/

namespace ErdosStraus

/-- The polynomial identity underlying the Type-I factor-pair certificate. -/
theorem typeI_factor_pair_identity
    (p a b c s d : ℕ)
    (hab : a + p * b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    4 * (a * b * c) * (a * c * s) * (p * b * c * s) =
      p * ((a * b * c) * (a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (a * c * s) * (p * b * c * s)) := by
  calc
    4 * (a * b * c) * (a * c * s) * (p * b * c * s)
        = p * a * b * c ^ 2 * s * ((p + d) * s) := by
          rw [hpd]
          ring
    _ = p * a * b * c ^ 2 * s * (p * s + (a + p * b)) := by
      rw [hab]
      ring
    _ = p * ((a * b * c) * (a * c * s) +
        (a * b * c) * (p * b * c * s) +
        (a * c * s) * (p * b * c * s)) := by ring

/--
A positive Type-I factor-pair certificate with `b < s` and `a < p*b`
produces the exact strictly ordered formulation.
-/
theorem typeI_factor_pair_hasDistinctDecomposition
    (p a b c s d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (hb_lt_s : b < s) (ha_lt_pb : a < p * b)
    (hab : a + p * b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    HasDistinctDecomposition p := by
  have hac : 0 < a * c := by positivity
  have hcs : 0 < c * s := by positivity
  refine ⟨a * b * c, a * c * s, p * b * c * s, ?_, ?_, ?_, ?_⟩
  · positivity
  · calc
      a * b * c = (a * c) * b := by ring
      _ < (a * c) * s := Nat.mul_lt_mul_of_pos_left hb_lt_s hac
      _ = a * c * s := by ring
  · calc
      a * c * s = (c * s) * a := by ring
      _ < (c * s) * (p * b) := Nat.mul_lt_mul_of_pos_left ha_lt_pb hcs
      _ = p * b * c * s := by ring
  · exact typeI_factor_pair_identity p a b c s d hab hpd

/--
The offset inequality `d < p` forces `b < s` in a positive Type-I
certificate. Thus the only additional strictness condition is `a < p*b`.
-/
theorem typeI_factor_pair_hasDistinctDecomposition_of_offset_lt
    (p a b c s d : ℕ)
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : 0 < s) (hd : 0 < d) (hdp : d < p)
    (ha_lt_pb : a < p * b)
    (hab : a + p * b = d * s)
    (hpd : p + d = 4 * (a * b * c)) :
    HasDistinctDecomposition p := by
  have hdb_lt_pb : d * b < p * b :=
    Nat.mul_lt_mul_of_pos_right hdp hb
  have hpb_lt_ds : p * b < d * s := by omega
  have hdb_lt_ds : d * b < d * s := lt_trans hdb_lt_pb hpb_lt_ds
  have hb_lt_s : b < s := (Nat.mul_lt_mul_left hd).mp hdb_lt_ds
  exact typeI_factor_pair_hasDistinctDecomposition p a b c s d hp ha hb hc hs
    hb_lt_s ha_lt_pb hab hpd

/--
The unit Type-I gate. If `p + 1 = d*s` and `p+d=4*x`, then the denominators
`x`, `x*s`, and `p*x*s` give a strict decomposition whenever `d < p`.
-/
theorem unit_typeI_gate_hasDistinctDecomposition
    (p d x s : ℕ)
    (hp : 1 < p) (hd : 0 < d) (hx : 0 < x) (hs : 0 < s)
    (hdp : d < p)
    (hps : p + 1 = d * s)
    (hpd : p + d = 4 * x) :
    HasDistinctDecomposition p := by
  apply typeI_factor_pair_hasDistinctDecomposition_of_offset_lt
      p 1 1 x s d (by omega) (by norm_num) (by norm_num) hx hs hd hdp
  · simpa using hp
  · simpa [Nat.add_comm] using hps
  · simpa using hpd

end ErdosStraus
