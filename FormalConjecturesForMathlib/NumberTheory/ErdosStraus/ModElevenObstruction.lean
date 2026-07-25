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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ResidueObstruction

@[expose] public section

/-!
# A quadratic-residue obstruction modulo 11

The quadratic residues `{1,3,4,5,9}` modulo `11` form a multiplicatively
closed set containing no additive-opposite pair. Hence an integer whose prime
factors all lie in this set cannot pass the `d=11` opposite-divisor gate.
-/

namespace ErdosStraus

/-- The nonzero quadratic residues modulo `11`. -/
def IsElevenSquareResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 9

/-- Quadratic residues modulo `11` are closed under multiplication. -/
theorem isElevenSquareResidue_mul_mod
    (a b : ℕ) (ha : IsElevenSquareResidue (a % 11))
    (hb : IsElevenSquareResidue (b % 11)) :
    IsElevenSquareResidue ((a * b) % 11) := by
  rcases ha with ha | ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb | hb <;>
    simp [IsElevenSquareResidue, Nat.mul_mod, ha, hb]

/-- No two nonzero quadratic residues modulo `11` are additive opposites. -/
theorem elevenSquareResidues_not_opposite
    (r s : ℕ) (hr : IsElevenSquareResidue r)
    (hs : IsElevenSquareResidue s) :
    (r + s) % 11 ≠ 0 := by
  rcases hr with hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs <;> omega

/--
If every prime divisor of `x` is a quadratic residue modulo `11`, then the
`d=11` opposite-divisor gate fails.
-/
theorem not_hasOppositeCoprimeDivisors_eleven_of_prime_divisors_square_residue
    (x : ℕ) (hx : 0 < x)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ x → IsElevenSquareResidue (q % 11)) :
    ¬ HasOppositeCoprimeDivisors x 11 := by
  apply not_hasOppositeCoprimeDivisors_of_residueProperty
      x 11 IsElevenSquareResidue hx
  · simp [IsElevenSquareResidue]
  · exact isElevenSquareResidue_mul_mod
  · exact elevenSquareResidues_not_opposite
  · exact hprime

end ErdosStraus
