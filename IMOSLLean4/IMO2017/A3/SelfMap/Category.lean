/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Category of self-maps

This file defines the category of self-maps.
-/

namespace IMOSL
namespace IMO2017A3

open SelfMap CategoryTheory

structure SelfMapCat where
  α : Type*
  f : α → α

instance : Category SelfMapCat where
  Hom := λ e₁ e₂ ↦ Hom e₁.f e₂.f
  id := λ X ↦ Hom.id X.f
  comp := λ e₁ e₂ ↦ Hom.comp e₂ e₁
  /- The category axioms proven for speeding up instance inference -/
  id_comp := Hom.comp_id
  comp_id := Hom.id_comp
  assoc := λ e₁ e₂ e₃ ↦ Hom.comp_assoc e₃ e₂ e₁
