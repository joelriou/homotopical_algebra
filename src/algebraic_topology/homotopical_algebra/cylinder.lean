/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category

open category_theory
open category_theory.limits
open algebraic_topology

variables {C : Type*} [category C] [has_finite_limits C] [has_finite_colimits C] (M : model_category C)

namespace algebraic_topology

namespace model_category

structure precylinder (A : C) :=
(I : C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A)
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)
(Wσ : σ ∈ M.weak_equivalences I A)

structure cylinder (A : C) extends precylinder M A :=
(cof : M.cofibrations _ _ (coprod.desc d₀ d₁))

variable {M}

structure left_homotopic {A B : C} (P : M.precylinder A) (f g : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f) (h₁ : P.d₁ ≫ h = g)

namespace precylinder

def symm {A : C} (P : M.precylinder A) : M.precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀,
  Wσ := P.Wσ,}

end precylinder

namespace left_homotopic

def symm {A B : C} {P : M.precylinder A} {f g : A ⟶ B} (H : left_homotopic P f g) :
  left_homotopic P.symm g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

end left_homotopic

end model_category

end algebraic_topology