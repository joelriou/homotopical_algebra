/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cylinder

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [model_category C]

namespace precylinder

structure left_homotopy {A B : C} (P : precylinder A) (f₀ f₁ : A ⟶ B) :=
(h : P.I ⟶ B) (h₀' : P.d₀ ≫ h = f₀ . obviously) (h₁' : P.d₁ ≫ h = f₁ . obviously)

namespace left_homotopy

restate_axiom h₀'
restate_axiom h₁'
attribute [simp, reassoc] h₀ h₁

def refl {A B : C} (P : precylinder A) (f : A ⟶ B) : P.left_homotopy f f :=
{ h := P.σ ≫ f, }

instance {A B : C} (P : precylinder A) (f : A ⟶ B) : inhabited (P.left_homotopy f f) := ⟨refl P f⟩

def symm {A B : C} {P : precylinder A} {f g : A ⟶ B} (H : P.left_homotopy f g) :
  P.symm.left_homotopy g f :=
{ h := H.h, }

def trans {A B : C} [is_cofibrant A] {P P' : cylinder A} {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : P.pre.left_homotopy f₁ f₂) (H₂ : P'.pre.left_homotopy f₂ f₃) :
    (P.trans P').pre.left_homotopy f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by simp only [h₁, h₀]), }

def comp_right {A B E : C} {P : precylinder A} {f f' : A ⟶ B}
  (H : P.left_homotopy f f') (g : B ⟶ E) : P.left_homotopy (f ≫ g) (f' ≫ g) :=
{ h := H.h ≫ g, }

end left_homotopy

end precylinder

end model_category

end algebraic_topology
