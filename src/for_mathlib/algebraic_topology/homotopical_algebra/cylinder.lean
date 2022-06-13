/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fibrant

noncomputable theory

open category_theory category_theory.limits

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

structure precylinder (A : C) :=
(I : C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A) [weq_σ : weak_eq σ]
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)

namespace precylinder

variables {A : C} (P : precylinder A)

@[simp]
def ι (P : precylinder A) := coprod.desc P.d₀ P.d₁

end precylinder

structure cylinder (A : C) extends precylinder A :=
[cof_ι : cofibration to_precylinder.ι]

namespace cylinder

end cylinder

end model_category

end algebraic_topology