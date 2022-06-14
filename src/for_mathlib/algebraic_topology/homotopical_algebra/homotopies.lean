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

variables {C : Type*} [category C] [model_category C] {A A' B B' : C}

structure left_homotopy (P : precylinder A) (f₀ f₁ : A ⟶ B) :=
(h : P.I ⟶ B) (h₀' : P.d₀ ≫ h = f₀ . obviously) (h₁' : P.d₁ ≫ h = f₁ . obviously)

namespace left_homotopy

restate_axiom h₀'
restate_axiom h₁'
attribute [simp, reassoc] h₀ h₁

def refl (P : precylinder A) (f : A ⟶ B) : left_homotopy P f f :=
{ h := P.σ ≫ f, }

instance (P : precylinder A) (f : A ⟶ B) : inhabited (left_homotopy P f f) := ⟨refl P f⟩

def symm {P : precylinder A} {f g : A ⟶ B} (H : left_homotopy P f g) :
  left_homotopy P.symm g f :=
{ h := H.h, }

def trans [is_cofibrant A] {P P' : cylinder A} {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : left_homotopy P.pre f₁ f₂) (H₂ : left_homotopy P'.pre f₂ f₃) :
    left_homotopy (P.trans P').pre f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by simp only [h₁, h₀]), }

def comp_right {P : precylinder A} {f f' : A ⟶ B}
  (H : left_homotopy P f f') (g : B ⟶ B') : left_homotopy P (f ≫ g) (f' ≫ g) :=
{ h := H.h ≫ g, }

end left_homotopy

structure right_homotopy (P : pre_path_object B) (f₀ f₁ : A ⟶ B) :=
(h : A ⟶ P.I) (h₀' : h ≫ P.d₀ = f₀ . obviously) (h₁' : h ≫ P.d₁ = f₁ . obviously)

namespace right_homotopy

restate_axiom h₀'
restate_axiom h₁'
attribute [simp, reassoc] h₀ h₁

@[simps]
def op {P : pre_path_object B} {f g : A ⟶ B} (H : right_homotopy P f g) : left_homotopy P.op f.op g.op :=
{ h := H.h.op,
  h₀' := by { dsimp [pre_path_object.op], rw [← op_comp, H.h₀], },
  h₁' := by { dsimp [pre_path_object.op], rw [← op_comp, H.h₁], }, }

@[simps]
def unop {A B : Cᵒᵖ} {P : pre_path_object B} {f g : A ⟶ B} (H : right_homotopy P f g) : left_homotopy P.unop f.unop g.unop :=
{ h := H.h.unop,
  h₀' := by { dsimp [pre_path_object.unop], rw [← unop_comp, H.h₀], },
  h₁' := by { dsimp [pre_path_object.unop], rw [← unop_comp, H.h₁], }, }

end right_homotopy

namespace left_homotopy

@[simps]
def op {P : precylinder A} {f g : A ⟶ B} (H : left_homotopy P f g) : right_homotopy P.op f.op g.op :=
{ h := H.h.op,
  h₀' := by { dsimp [precylinder.op], rw [← op_comp, H.h₀], },
  h₁' := by { dsimp [precylinder.op], rw [← op_comp, H.h₁], }, }

@[simps]
def unop {A B : Cᵒᵖ} {P : precylinder A} {f g : A ⟶ B} (H : left_homotopy P f g) : right_homotopy P.unop f.unop g.unop :=
{ h := H.h.unop,
  h₀' := by { dsimp [precylinder.unop], rw [← unop_comp, H.h₀], },
  h₁' := by { dsimp [precylinder.unop], rw [← unop_comp, H.h₁], }, }

end left_homotopy

namespace right_homotopy

def refl (P : pre_path_object B) (f : A ⟶ B) : right_homotopy P f f :=
{ h := f ≫ P.σ, }

instance (P : pre_path_object B) (f : A ⟶ B) : inhabited (right_homotopy P f f) := ⟨refl P f⟩

def symm {P : pre_path_object B} {f g : A ⟶ B} (H : right_homotopy P f g) :
  right_homotopy P.symm g f :=
{ h := H.h, }

def trans {A B : C} [is_fibrant B] {P P' : path_object B} {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : right_homotopy P.pre f₁ f₂) (H₂ : right_homotopy P'.pre f₂ f₃) :
    right_homotopy (P.trans P').pre f₁ f₃ :=
begin
  haveI : is_cofibrant (opposite.op B) := is_fibrant.op infer_instance,
  let H₁' : left_homotopy P.op.pre f₁.op f₂.op := H₁.op,
  let H₂' : left_homotopy P'.op.pre f₂.op f₃.op := H₂.op,
  exact (left_homotopy.trans H₁' H₂').unop,
end

def comp_left {P : pre_path_object B} {f f' : A ⟶ B}
  (H : right_homotopy P f f') (g : A' ⟶ A) : right_homotopy P (g ≫ f) (g ≫ f') :=
{ h := g ≫ H.h, }

end right_homotopy

end model_category

end algebraic_topology
