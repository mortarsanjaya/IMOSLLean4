/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6MainResults.General
import IMOSLLean4.IMO2017.A6.A6MainResults.Field

/-!
# IMO 2017 A6 (P2)

Let $R$ be a ring.
Determine all functions $f : R → R$ such that, for any $x, y ∈ R$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

### Implementation details

The solution is still incomplete in the sense that only some subcases have been solved.
Here are the cases with implemented solution:
* Case 1: `2 ∈ Rˣ` and `3 ∈ R⁰`.
* Case 2: `R` is a division ring with `char(R) ≠ 2`.
* Case 3: `R` is a field.

Case 1 is implemented in `IMOSLLean4/IMO2017/A6/A6MainResults/General.lean`.
Case 2 and 3 are implemented in `IMOSLLean4/IMO2017/A6/A6MainResults/Field.lean`.
-/

namespace IMOSL
namespace IMO2017A6

/-- Final solution for Case 1 -/
alias final_solution_case1 := general_good_iff

/-- Final solution for Case 2 -/
alias final_solution_case2 := CharNeTwoDivRing_good_iff

/-- Final solution for Case 3 -/
alias final_solution_case3 := Field_good_iff
