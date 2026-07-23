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

import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MinimalCounterexample
import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.SmallGates
import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.DivisorSquareNormalization
import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MordellReduction

/-!
# Erdős–Straus foundation axiom audit

This standalone Lean script emits the axiom dependencies of the principal
helper theorems used in the strict-denominator foundation, divisor-square
normalization, and Mordell residue reduction. It is run with `lake env lean`
rather than built as a project module because Lean does not permit
`#print axioms` inside a `module` file.
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
#print axioms ErdosStraus.oppositeCoprimeDivisors_hasDistinctDecomposition
#print axioms ErdosStraus.dThree_gate_hasDistinctDecomposition
#print axioms ErdosStraus.divisorSquare_hasOppositeCoprimeDivisors
#print axioms ErdosStraus.divisorSquare_hasDistinctDecomposition
#print axioms ErdosStraus.coprime_offset_of_prime
#print axioms ErdosStraus.prime_divisorSquare_hasDistinctDecomposition
#print axioms ErdosStraus.mod_one_twenty_seventy_three_family
#print axioms ErdosStraus.mod_one_twenty_ninety_seven_family
#print axioms ErdosStraus.mod_one_sixty_eight_seventy_three_family
#print axioms ErdosStraus.mod_one_sixty_eight_ninety_seven_family
#print axioms ErdosStraus.mod_one_sixty_eight_one_forty_five_family
#print axioms ErdosStraus.prime_counterexample_mod_one_twenty
#print axioms ErdosStraus.prime_counterexample_mod_one_sixty_eight
#print axioms ErdosStraus.prime_counterexample_mod_eight_forty
#print axioms ErdosStraus.exists_prime_counterexample_mordell
