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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ModElevenReduction

@[expose] public section

/-!
# Final Erdős–Straus proof architecture

All elementary, scaling, prime-reduction, and modular-sieve obligations are
isolated below from the remaining universal mathematical problem. A proof of
`ResidualPrimeCoverage` would complete the exact strict-denominator theorem
for `n > 2` and the ordinary Erdős–Straus conjecture for every `n ≥ 2`.
-/

namespace ErdosStraus

/--
The remaining universal obligation after the corrected modulo-9240 sieve:
every prime in a residual class has a strict polynomial decomposition.
-/
def ResidualPrimeCoverage : Prop :=
  ∀ p : ℕ, p.Prime → IsModNineTwoFourZeroResidue (p % 9240) →
    HasDistinctDecomposition p

/-- Residual prime coverage implies the strict polynomial theorem for every `n > 2`. -/
theorem hasDistinctDecomposition_of_residualPrimeCoverage
    (hcoverage : ResidualPrimeCoverage) (n : ℕ) (hn : 2 < n) :
    HasDistinctDecomposition n := by
  by_contra hnot
  have hcounter : IsCounterexample n := ⟨hn, hnot⟩
  obtain ⟨p, hp, hres, hpnot⟩ :=
    exists_prime_counterexample_mod_nine_two_four_zero ⟨n, hcounter⟩
  exact hpnot (hcoverage p hp hres)

/--
Residual prime coverage implies the exact rational formulation used by
Erdős Problem 242, including `1 ≤ x < y < z`, for every `n > 2`.
-/
theorem rational_erdos_straus_of_residualPrimeCoverage
    (hcoverage : ResidualPrimeCoverage) (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  exact (hasDistinctDecomposition_of_residualPrimeCoverage hcoverage n hn).toRational
    (by omega)

/--
Residual prime coverage also implies the ordinary Erdős–Straus conjecture for
all `n ≥ 2`. The exceptional endpoint `n=2` is handled by `(x,y,z)=(1,2,2)`;
strictly distinct denominators are impossible at that endpoint and are not
part of the ordinary conjecture.
-/
theorem ordinary_erdos_straus_of_residualPrimeCoverage
    (hcoverage : ResidualPrimeCoverage) (n : ℕ) (hn : 2 ≤ n) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  by_cases hne : n = 2
  · subst n
    exact ⟨1, 2, 2, by norm_num⟩
  · have hnstrict : 2 < n := by omega
    obtain ⟨x, y, z, hx, hxy, hyz, hidentity⟩ :=
      rational_erdos_straus_of_residualPrimeCoverage hcoverage n hnstrict
    exact ⟨x, y, z, by omega, by omega, by omega, hidentity⟩

end ErdosStraus
