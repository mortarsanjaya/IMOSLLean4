/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Homomorphisms between self-maps

Let `X` and `Y` be self-maps.
A homomorphism from `X` to `Y` is a function `e : X.α → Y.α` that
  semiconjugates `X.f` to `Y.f`, i.e., satisfies `e ∘ X.f = Y.f ∘ e`.
We construct some basic homomorphisms in this file.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

/-- Homomorphisms between self-maps -/
structure Hom (X Y : SelfMap) where
  toFun : X.α → Y.α
  Semiconj : toFun.Semiconj X.f Y.f


namespace Hom

instance (X Y : SelfMap) : FunLike (Hom X Y) X.α Y.α :=
  ⟨toFun, λ e₁ e₂ h ↦ by cases e₁; cases e₂; congr⟩

instance (X Y : SelfMap) : CoeFun (Hom X Y) (λ _ ↦ X.α → Y.α) := ⟨toFun⟩

@[ext] theorem ext {e₁ e₂ : Hom X Y} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

theorem ext_iff {e₁ e₂ : Hom X Y} : (∀ x, e₁ x = e₂ x) ↔ e₁ = e₂ :=
  ⟨ext, λ h _ ↦ h ▸ rfl⟩

protected def copy (e : Hom X Y) (e') (h : e' = ⇑e) : Hom X Y :=
  ⟨e', h ▸ e.Semiconj⟩



def id (X : SelfMap) : Hom X X :=
  ⟨_root_.id, Function.Semiconj.id_left⟩

def comp (φ₁ : Hom Y Z) (φ₂ : Hom X Y) : Hom X Z :=
  ⟨φ₁ ∘ φ₂, φ₁.Semiconj.comp_left φ₂.Semiconj⟩

theorem id_comp (φ : Hom X Y) : (id Y).comp φ = φ := rfl

theorem comp_id (φ : Hom X Y) : φ.comp (id X) = φ := rfl

theorem comp_assoc (φ₁ : Hom Y Z) (φ₂ : Hom X Y) (φ₃ : Hom W X) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := rfl



lemma semiconj (φ : Hom X Y) : φ ∘ X.f = Y.f ∘ φ :=
  funext φ.Semiconj

lemma semiconj_apply (φ : Hom X Y) : ∀ a, φ (X.f a) = Y.f (φ a) :=
  φ.Semiconj

lemma semiconj_iterate (φ : Hom X Y) (k : ℕ) : φ ∘ X.f^[k] = Y.f^[k] ∘ φ :=
  funext (φ.Semiconj.iterate_right k)

lemma semiconj_iterate_apply (φ : Hom X Y) :
    ∀ k x, φ (X.f^[k] x) = Y.f^[k] (φ x) :=
  φ.Semiconj.iterate_right



/-! ##### Binary sum -/

def sum_inl (X Y : SelfMap) : Hom X (sum X Y) := ⟨Sum.inl, λ _ ↦ rfl⟩

def sum_inr (X Y : SelfMap) : Hom Y (sum X Y) := ⟨Sum.inr, λ _ ↦ rfl⟩

def sum_elim (e₁ : Hom X₁ Y) (e₂ : Hom X₂ Y) : Hom (sum X₁ X₂) Y :=
  ⟨Sum.elim e₁ e₂, Sum.rec e₁.Semiconj e₂.Semiconj⟩

def sum_map (e₁ : Hom X₁ Y₁) (e₂ : Hom X₂ Y₂) : Hom (sum X₁ X₂) (sum Y₁ Y₂) :=
  ⟨Sum.map e₁ e₂, λ a ↦ match a with
    | Sum.inl a => congr_arg Sum.inl (e₁.Semiconj a)
    | Sum.inr a => congr_arg Sum.inr (e₂.Semiconj a)⟩



/-! ##### Sigma -/

/-- Inclusion of `F(i)` to the direct sum `Σ F` -/
def sigma_incl (F : I → SelfMap) (i : I) : Hom (F i) (sigma F) :=
  ⟨λ a ↦ ⟨i, a⟩, λ _ ↦ rfl⟩

/-- Given a collection of self-map homomorphisms `F(i) → X`,
  construct the self-map homomorphism `Σ F → X`. -/
def sigma_elim (e : (i : I) → Hom (F i) X) : Hom (sigma F) X :=
  ⟨λ ⟨i, x⟩ ↦ e i x, λ ⟨i, x⟩ ↦ (e i).Semiconj x⟩

/-- Given `s : I → J`, `F : I → SelfMap`, `G : J → SelfMap`, and
  homomorphisms `F(i) → G(s(i))`, construct a homomorphism `Σ F → Σ G`. -/
def sigma_map (s : I → J) (E : (i : I) → Hom (F i) (G (s i))) :
    Hom (sigma F) (sigma G) where
  toFun := λ ⟨i, x⟩ ↦ ⟨s i, E i x⟩
  Semiconj := λ ⟨i, x⟩ ↦ Sigma.ext rfl <| heq_of_eq ((E i).Semiconj x)

/-- Given a collection of self-map homomorphisms `F(i) → G(i)`,
  construct the self-map homomorphism `Σ F → Σ G`. -/
def sigma_map_id (E : (i : I) → Hom (F i) (G i)) : Hom (sigma F) (sigma G) :=
  sigma_map _root_.id E



/-! ##### Concrete self-maps -/

def fromEmpty (X : SelfMap) : Hom EmptySelfMap X :=
  ⟨Empty.elim, λ x ↦ Empty.elim x⟩

def toUnit (X : SelfMap) : Hom X UnitSelfMap :=
  ⟨λ _ ↦ (), λ _ ↦ rfl⟩

def fromUnit_ofFixedPt (X : SelfMap) {x} (h : X.f x = x) : Hom UnitSelfMap X :=
  ⟨λ _ ↦ x, λ _ ↦ h.symm⟩

lemma fixedPt_ofUnit (e : Hom UnitSelfMap X) : X.f (e ()) = e () :=
  (e.Semiconj ()).symm

def fromNatSucc (X : SelfMap) (x : X.α) : Hom NatSuccMap X :=
  ⟨λ k ↦ X.f^[k] x, λ k ↦ X.f.iterate_succ_apply' k x⟩

def fromFinSucc (X : SelfMap) {x : X.α} (h : X.f^[n.succ] x = x) :
    Hom (FinSuccMap n) X :=
  ⟨λ k ↦ X.f^[k.1] x, λ k ↦ by
    change X.f^[(k.1 + 1 % n.succ) % _] x = X.f (X.f^[k.1] x)
    rw [Nat.add_mod_mod, ← X.f.iterate_succ_apply', ← Nat.succ_eq_add_one]
    have h0 : X.f^[n.succ * _ + _] x = X.f^[_] x :=
      congr_arg (λ m ↦ X.f^[m] x) (Nat.div_add_mod k.1.succ n.succ)
    rwa [Nat.add_comm, X.f.iterate_add_apply,
      X.f.iterate_mul, Function.iterate_fixed h] at h0⟩
