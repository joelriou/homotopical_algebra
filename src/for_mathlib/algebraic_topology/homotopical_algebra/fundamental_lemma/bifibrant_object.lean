/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma.cofibrant_object

noncomputable theory

open algebraic_topology category_theory category_theory.limits category_theory.category

namespace algebraic_topology

namespace model_category

variables (C : Type*) [category C] [M : model_category C]
include M

@[nolint has_nonempty_instance]
structure bifibrant_object :=
(obj : C)
[cof : is_cofibrant obj]
[fib : is_fibrant obj]

namespace bifibrant_object

instance (X : bifibrant_object C) : is_cofibrant X.obj := X.cof
instance (X : bifibrant_object C) : is_fibrant X.obj := X.fib

instance : category (bifibrant_object C) :=
induced_category.category (λ X, cofibrant_object.mk X.obj)

@[simps]
def forget_fib : bifibrant_object C ⥤ cofibrant_object C := induced_functor _

variable {C}

def right_homotopy : hom_rel (bifibrant_object C) :=
λ A X f₁ f₂, cofibrant_object.right_homotopy f₁ f₂

lemma right_homotopy.is_equiv (A X : bifibrant_object C) :
  is_equiv (A ⟶ X) (λ f₁ f₂, right_homotopy f₁ f₂) :=
{ refl := λ f, cofibrant_object.right_homotopy.mk (path_object.some X.1)
      (right_homotopy.refl _ f),
  symm := λ f₁ f₂ H, H.symm,
  trans := λ f₁ f₂ f₃ H₁₂ H₂₃, begin
    let Cyl := cylinder.some A.obj,
    let H₁₂' := H₁₂.some_spec.some.to_left_homotopy Cyl,
    let H₂₃' := H₂₃.some_spec.some.to_left_homotopy Cyl,
    let H₁₃' := H₁₂'.trans H₂₃',
    let H₁₃ := H₁₃'.to_right_homotopy (path_object.some X.obj),
    exact cofibrant_object.right_homotopy.mk (path_object.some X.obj) H₁₃,
  end}

instance : congruence (bifibrant_object.right_homotopy : hom_rel (bifibrant_object C)) :=
{ is_equiv := right_homotopy.is_equiv,
  comp_left := λ A B X f g₁ g₂ H, H.comp_left f,
  comp_right := λ A X Y f₁ f₂ g H, H.comp_right g, }

variable (C)

def homotopy_category := quotient (right_homotopy : hom_rel (bifibrant_object C))

instance : category (homotopy_category C) := quotient.category _

variable {C}

namespace homotopy_category

def Q : bifibrant_object C ⥤ homotopy_category C := quotient.functor _

@[simp]
lemma Q_map {X Y : bifibrant_object C} (f : X ⟶ Y) :
  homotopy_category.Q.map f = (quotient.functor _).map f := rfl

lemma Q_map_surjective (X Y : bifibrant_object C) :
  function.surjective (λ (f : X ⟶ Y), Q.map f) :=
by apply quotient.functor_map_surjective

lemma Q_map_eq_iff' {X Y : bifibrant_object C}
  (P : path_object Y.obj) (f₁ f₂ : X ⟶ Y) :
  (homotopy_category.Q.map f₁ = homotopy_category.Q.map f₂) ↔
    nonempty (model_category.right_homotopy P.pre f₁ f₂) :=
begin
  split,
  { intro h,
    simp only [homotopy_category.Q_map, quotient.functor_map_eq_iff] at h,
    exact nonempty.intro (h.some_spec.some.change_path_object P), },
  { intro h,
    apply category_theory.quotient.sound,
    exact cofibrant_object.right_homotopy.mk P h.some, },
end

lemma Q_map_eq_iff {X Y : bifibrant_object C}
  (Cyl : cylinder X.obj) (f₁ f₂ : X ⟶ Y) :
  (homotopy_category.Q.map f₁ = homotopy_category.Q.map f₂) ↔
    nonempty (left_homotopy Cyl.pre f₁ f₂) :=
begin
  rw homotopy_category.Q_map_eq_iff' (path_object.some Y.obj),
  split,
  { exact λ h, nonempty.intro (h.some.to_left_homotopy _), },
  { exact λ h, nonempty.intro (h.some.to_right_homotopy _), },
end

@[simps]
def forget_fib : homotopy_category C ⥤ cofibrant_object.homotopy_category C :=
category_theory.quotient.lift _
  (bifibrant_object.forget_fib C ⋙ cofibrant_object.homotopy_category.Q)
  (λ X Y f₁ f₂ H, begin
    dsimp only [functor.comp_map],
    haveI : is_fibrant ((forget_fib C).obj Y).obj := by { dsimp, apply_instance, },
    rw cofibrant_object.homotopy_category.Q_map_eq_iff' H.some,
    exact nonempty.intro H.some_spec.some,
  end)

end homotopy_category

end bifibrant_object

end model_category

end algebraic_topology
