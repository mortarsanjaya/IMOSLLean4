/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Archive.F2X.Defs
import Mathlib.Data.Finset.Sort

/-!
# List representation of `𝔽₂X`

We provide a list representation of `𝔽₂X` and related constructions.
In particular, `Repr` instance for `𝔽₂X` is given here.

### Implementation details

Our list representation is a descending list.
-/

namespace IMOSL
namespace IMO2012A5
namespace 𝔽₂X

open Extra

/-- List representation of `𝔽₂X` -/
protected def toList (P : 𝔽₂X) := P.toFinset.sort GE.ge

protected lemma toFinset_toList (P : 𝔽₂X) : P.toList.toFinset = P.toFinset :=
  P.toFinset.sort_toFinset _

protected lemma toList_inj {P Q : 𝔽₂X} : P.toList = Q.toList ↔ P = Q :=
  ⟨λ h ↦ 𝔽₂X.ext (by rw [← 𝔽₂X.toFinset_toList, h, 𝔽₂X.toFinset_toList]),
  congrArg 𝔽₂X.toList⟩





/-! ### Representation -/

protected def repr_term : ℕ → Lean.Format
  | 0 => "1"
  | 1 => "X"
  | n => "X^" ++ n.repr

protected def repr_aux : List ℕ → Lean.Format
  | [] => ""
  | n :: l => 𝔽₂X.repr_term n ++ l.foldr (λ k str ↦ " + " ++ 𝔽₂X.repr_term k ++ str) ""

protected def repr (P : 𝔽₂X) (_ : ℕ) : Lean.Format :=
  𝔽₂X.repr_aux P.toList

instance : Repr 𝔽₂X := ⟨𝔽₂X.repr⟩
