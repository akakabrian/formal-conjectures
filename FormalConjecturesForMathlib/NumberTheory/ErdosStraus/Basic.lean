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

public import Mathlib

@[expose] public section

/-!
# Erdős–Straus foundations

We use the polynomial identity

`4 * x * y * z = n * (x * y + x * z + y * z)`

as a certificate format over natural numbers. This avoids division-by-zero
side conditions and is equivalent to the usual unit-fraction equation for
positive denominators.
-/

namespace ErdosStraus

/-- A positive three-denominator Erdős–Straus decomposition. -/
def HasDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ 0 < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

/-- The strict-order form used in Erdős Problem 242. -/
def HasDistinctDecomposition (n : ℕ) : Prop :=
  ∃ x y z : ℕ,
    1 ≤ x ∧ x < y ∧ y < z ∧
      4 * x * y * z = n * (x * y + x * z + y * z)

/-- A strictly ordered decomposition is in particular a positive one. -/
theorem HasDistinctDecomposition.hasDecomposition
    {n : ℕ} (h : HasDistinctDecomposition n) :
    HasDecomposition n := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  exact ⟨x, y, z, by omega, by omega, by omega, hEq⟩

/-- A strict polynomial certificate implies the usual rational unit-fraction identity. -/
theorem HasDistinctDecomposition.toRational
    {n : ℕ} (hn : 0 < n) (h : HasDistinctDecomposition n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  refine ⟨x, y, z, hx, hxy, hyz, ?_⟩
  have hnx : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxx : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < x))
  have hyx : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < y))
  have hzx : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < z))
  have hEqQ :
      (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
    exact_mod_cast hEq
  field_simp [hnx, hxx, hyx, hzx]
  ring_nf at hEqQ ⊢
  exact hEqQ

end ErdosStraus
