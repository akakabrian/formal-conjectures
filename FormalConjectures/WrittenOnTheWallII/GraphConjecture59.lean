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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 59

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false. On vertices `0, …, 9`, begin with the complete bipartite graph
$K_{5,5}$ with parts $\{0,\ldots,4\}$ and $\{5,\ldots,9\}$, and delete the four
edges $(0,5)$, $(0,6)$, $(0,7)$, and $(1,5)$. Add seven isolated vertices
`10, …, 16`, and then add a universal vertex `17`.

For the resulting connected graph $G$:

* its descending degree sequence is
  $[17,6,6,6,6,6,5,5,5,4,3,1,1,1,1,1,1,1]$, whose Havel--Hakimi residue is $10$;
* deleting the universal vertex leaves an induced bipartite subgraph on $17$ vertices,
  so $b(G) \ge 17$;
* every induced forest has at most $13$ vertices. Without the universal vertex, the
  ten-vertex core contributes at most six vertices and the seven added vertices
  contribute at most seven. With the universal vertex, the selected core vertices
  must be independent to avoid a triangle, so at most five core vertices can be used,
  together with the universal vertex and seven leaves.

Hence $\operatorname{residue}(G)b(G) \ge 170 > 13^2$, so
$\lceil\sqrt{\operatorname{residue}(G)b(G)}\rceil \ge 14 > 13$.

The counterexample and Lean formalization were developed by Brian Akaka with assistance
from OpenAI ChatGPT/Codex and Anthropic Claude. The linked proof was checked by Lean 4.27.0.
-/

namespace WrittenOnTheWallII.GraphConjecture59

open Classical SimpleGraph

/--
WOWII [Conjecture 59](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest
satisfies $f(G) \ge \lceil \sqrt{\mathrm{residue}(G) \cdot b(G)} \rceil$, where
$\mathrm{residue}(G)$ is the Havel-Hakimi residue and $b(G)$ is the size of a
largest induced bipartite subgraph.

This conjecture is false, as witnessed by the 18-vertex graph described in the module
docstring.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/akakabrian/WOW-59/blob/1dc12403c7e9cce83e88c423ec7fadfc1ae0370e/WOW59/Counterexample.lean#L469-L506"]
theorem conjecture59 : answer(False) ↔
    ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- The residue of $K_2$ equals $1$: degree sequence is $[1, 1]$; one Havel-Hakimi
step gives $[0]$, leaving a single zero. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 1 := by
  unfold residue; decide +native

end WrittenOnTheWallII.GraphConjecture59
