/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cofibrant

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open algebraic_topology

variables {M : model_category}

namespace algebraic_topology

namespace model_category

structure precylinder (A : M.C) :=
(I : M.C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A)
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)
(Wσ : arrow.mk σ ∈ M.W)

structure cylinder (A : M.C) extends precylinder A :=
(cof : arrow.mk (coprod.desc d₀ d₁) ∈ M.cofibrations)

variable {M}

namespace precylinder

structure left_homotopic {A B : M.C} (P : precylinder A) (f g : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f) (h₁ : P.d₁ ≫ h = g)

def symm {A : M.C} (P : precylinder A) : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀,
  Wσ := P.Wσ, }

end precylinder

namespace cylinder

def trans {A : M.C} (P : cylinder A) (P' : cylinder A) (hA : cofibrant A) : cylinder A :=
{ I := pushout P.d₁ P'.d₀,
  d₀ := P.d₀ ≫ pushout.inl,
  d₁ := P'.d₁ ≫ pushout.inr,
  σ := pushout.desc P.σ P'.σ (by rw [P.σd₁, P'.σd₀]),
  σd₀ := by { rw [category.assoc, pushout.inl_desc], exact P.σd₀, },
  σd₁ := by { rw [category.assoc, pushout.inr_desc], exact P'.σd₁, },
  cof := begin
    dsimp,
    sorry,
  end,
  Wσ := begin
    sorry,
  end, }

end cylinder

namespace left_homotopic

def refl {A B : M.C} {P : precylinder A} (f : A ⟶ B) : P.left_homotopic f f :=
{ h := P.σ ≫ f,
  h₀ := by rw [← assoc, P.σd₀, id_comp],
  h₁ := by rw [← assoc, P.σd₁, id_comp], }

def symm {A B : M.C} {P : precylinder A} {f g : A ⟶ B} (H : P.left_homotopic f g) :
  P.symm.left_homotopic g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

def trans {A B : M.C} (hA : cofibrant A) {P P' : cylinder A} {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : P.to_precylinder.left_homotopic f₁ f₂) (H₂ : P'.to_precylinder.left_homotopic f₂ f₃) :
    (P.trans P' hA).to_precylinder.left_homotopic f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by rw [H₁.h₁, H₂.h₀]),
  h₀ := by erw [category.assoc, pushout.inl_desc, H₁.h₀],
  h₁ := by erw [category.assoc, pushout.inr_desc, H₂.h₁], }

end left_homotopic

end model_category

end algebraic_topology