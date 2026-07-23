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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MinimalCounterexample
public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.SmallGates

/-!
# Erdős–Straus Phase 1 axiom audit

This module emits the axiom dependencies of the principal helper theorems used
in the strict-denominator Phase 1 foundation.
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
