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

import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.FinalReduction
import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ResidueObstruction
import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ModElevenGates

/-!
# Erdős–Straus foundation axiom audit

This standalone Lean script emits the axiom dependencies of the principal
strict-denominator reductions, the corrected modulo-9240 sieve, the generic
residue obstruction, the `d=11` prime-factor triggers, and the final
conditional proof architecture. It is run with `lake env lean` rather than
built as a project module because Lean does not permit `#print axioms` inside
a `module` file.
-/

#print axioms ErdosStraus.HasDistinctDecomposition.toRational
#print axioms ErdosStraus.even_family
#print axioms ErdosStraus.mod_three_two_family
#print axioms ErdosStraus.mod_four_three_family
#print axioms ErdosStraus.mod_eight_five_family
#print axioms ErdosStraus.HasDistinctDecomposition.scale
#print axioms ErdosStraus.counterexample_mod_twenty_four_eq_one
#print axioms ErdosStraus.exists_prime_counterexample_one_mod_twenty_four
#print axioms ErdosStraus.typeII_factor_pair_hasDistinctDecomposition
#print axioms ErdosStraus.hasOppositeCoprimeDivisors_of_product_dvd
#print axioms ErdosStraus.oppositeCoprimeDivisors_hasDistinctDecomposition
#print axioms ErdosStraus.residueProperty_mod_of_prime_divisors
#print axioms ErdosStraus.not_hasOppositeCoprimeDivisors_of_residueProperty
#print axioms ErdosStraus.dThree_gate_hasDistinctDecomposition
#print axioms ErdosStraus.divisorSquare_hasOppositeCoprimeDivisors
#print axioms ErdosStraus.divisorSquare_hasDistinctDecomposition
#print axioms ErdosStraus.coprime_offset_of_prime
#print axioms ErdosStraus.prime_divisorSquare_hasDistinctDecomposition
#print axioms ErdosStraus.coprime_three_of_prime_ne_three
#print axioms ErdosStraus.oppositeCoprimeDivisors_eleven_of_prime_divisor_trigger
#print axioms ErdosStraus.three_dvd_offset_eleven_of_mod_twenty_four_one
#print axioms ErdosStraus.dEleven_gate_hasDistinctDecomposition
#print axioms ErdosStraus.mod_one_twenty_seventy_three_family
#print axioms ErdosStraus.mod_one_twenty_ninety_seven_family
#print axioms ErdosStraus.mod_one_sixty_eight_seventy_three_family
#print axioms ErdosStraus.mod_one_sixty_eight_ninety_seven_family
#print axioms ErdosStraus.mod_one_sixty_eight_one_forty_five_family
#print axioms ErdosStraus.prime_counterexample_mod_eight_forty
#print axioms ErdosStraus.mod_one_three_two_zero_two_forty_one_family
#print axioms ErdosStraus.mod_one_three_two_zero_four_eighty_one_family
#print axioms ErdosStraus.mod_one_three_two_zero_six_zero_one_family
#print axioms ErdosStraus.mod_one_three_two_zero_four_zero_nine_family
#print axioms ErdosStraus.mod_one_three_two_zero_seven_sixty_nine_family
#print axioms ErdosStraus.mod_one_three_two_zero_one_zero_zero_nine_family
#print axioms ErdosStraus.mod_one_three_two_zero_one_one_two_nine_family
#print axioms ErdosStraus.mod_one_three_two_zero_one_two_four_nine_family
#print axioms ErdosStraus.mod_nine_two_four_zero_one_two_zero_one_family
#print axioms ErdosStraus.mod_nine_two_four_zero_six_zero_zero_one_family
#print axioms ErdosStraus.prime_counterexample_mod_one_three_two_zero
#print axioms ErdosStraus.prime_counterexample_mod_nine_two_four_zero
#print axioms ErdosStraus.exists_prime_counterexample_mod_nine_two_four_zero
#print axioms ErdosStraus.hasDistinctDecomposition_of_residualPrimeCoverage
#print axioms ErdosStraus.rational_erdos_straus_of_residualPrimeCoverage
#print axioms ErdosStraus.ordinary_erdos_straus_of_residualPrimeCoverage
