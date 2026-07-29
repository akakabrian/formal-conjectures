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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.TypeIFactorPair

@[expose] public section

/-!
# Consecutive Erdős–Straus offsets

For a residual prime written as `p + 3 = 4*m`, the complete offset sequence is

`x_k = m+k` and `d_k = 4*k+3`.

The identity `p+d_k=4*x_k` holds for every `k`. A divisor `d_k ∣ p+1`
therefore activates the unit Type-I gate at that offset.
-/

namespace ErdosStraus

/-- The consecutive candidate denominator at offset `k`. -/
def offsetX (m k : ℕ) : ℕ := m + k

/-- The corresponding offset `4*k+3`. -/
def offsetD (k : ℕ) : ℕ := 4 * k + 3

@[simp] theorem offsetX_zero (m : ℕ) : offsetX m 0 = m := by
  simp [offsetX]

@[simp] theorem offsetX_succ (m k : ℕ) : offsetX m (k + 1) = offsetX m k + 1 := by
  simp [offsetX, Nat.add_assoc]

@[simp] theorem offsetD_succ (k : ℕ) : offsetD (k + 1) = offsetD k + 4 := by
  simp [offsetD]
  omega

/-- The invariant tying every consecutive candidate to the same target `p`. -/
theorem offset_identity
    (p m k : ℕ) (hpm : p + 3 = 4 * m) :
    p + offsetD k = 4 * offsetX m k := by
  dsimp [offsetD, offsetX]
  omega

/--
If one offset `d_k` divides `p+1`, the unit Type-I construction gives the
exact strict-denominator Erdős–Straus decomposition at `x_k`.
-/
theorem unit_typeI_gate_of_offset_dvd
    (p m k : ℕ)
    (hp : 1 < p) (hm : 0 < m)
    (hpm : p + 3 = 4 * m)
    (hdp : offsetD k < p)
    (hdvd : offsetD k ∣ p + 1) :
    HasDistinctDecomposition p := by
  rcases hdvd with ⟨s, hps⟩
  have hs : 0 < s := by
    apply Nat.pos_of_ne_zero
    intro hs0
    subst s
    simp at hps
  apply unit_typeI_gate_hasDistinctDecomposition
      p (offsetD k) (offsetX m k) s hp
  · dsimp [offsetD]
    omega
  · dsimp [offsetX]
    omega
  · exact hs
  · exact hdp
  · exact hps
  · exact offset_identity p m k hpm

end ErdosStraus
