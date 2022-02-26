/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cofibrant

open category_theory
open category_theory.limits
open algebraic_topology

variables {M : model_category}

namespace algebraic_topology

namespace model_category

structure precylinder (A : M.C) :=
(I : M.C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A)
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)
(Wσ : M.weak_equivalences.contains σ)

structure cylinder (A : M.C) extends precylinder A :=
(cof : M.cofibrations.contains (coprod.desc d₀ d₁))

variable {M}

structure left_homotopic {A B : M.C} (P : precylinder A) (f g : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f) (h₁ : P.d₁ ≫ h = g)

namespace precylinder

def symm {A : M.C} (P : precylinder A) : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀,
  Wσ := P.Wσ,}

noncomputable def trans {A : M.C} [cofA : M.cofibrant A] (P : M.cylinder A) (P' : M.cylinder A) : M.cylinder A :=
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
  end,
}

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