/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Defs
import Std.Data.Sum.Basic

/-!
# IMO 2017 A3 (Binary sums)

Let `X` and `Y` be self-maps.
We prove that if `X ⊕ Y` is good, then `X` and `Y` are good.
-/

namespace IMOSL
namespace IMO2017A3

theorem bad_pair_sum_SelfMap {X Y : SelfMap} {g₁ : X.α → X.α} {g₂ : Y.α → Y.α}
    (h : bad_pair X.f g₁) (h0 : bad_pair Y.f g₂) :
    bad_pair (X.sum Y).f (Sum.map g₁ g₂) :=
  funext λ x ↦ match x with
    | Sum.inl a => congr_arg Sum.inl (congr_fun h a)
    | Sum.inr b => congr_arg Sum.inr (congr_fun h0 b)

theorem good_sum_inl {X Y : SelfMap} (h : good (X.sum Y)) : good X :=
  λ g h0 ↦ funext λ a ↦ Sum.inl.inj <|
    congr_fun (h (Sum.map g Y.f) (bad_pair_sum_SelfMap h0 rfl)) (Sum.inl a)

theorem good_sum_inr {X Y : SelfMap} (h : good (X.sum Y)) : good Y :=
  λ g h0 ↦ funext λ b ↦ Sum.inr.inj <|
    congr_fun (h (Sum.map X.f g) (bad_pair_sum_SelfMap rfl h0)) (Sum.inr b)
