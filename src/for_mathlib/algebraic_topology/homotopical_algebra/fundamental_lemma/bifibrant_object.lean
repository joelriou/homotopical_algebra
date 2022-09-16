/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma.cofibrant_object
import for_mathlib.category_theory.localization.predicate

noncomputable theory

open algebraic_topology category_theory category_theory.limits category_theory.category

namespace category_theory.functor

lemma congr_map_conjugate {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (h : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
  F₁.map f = eq_to_hom (by rw h) ≫ F₂.map f ≫ eq_to_hom (by rw h) :=
begin
  subst h,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

end category_theory.functor

namespace category_theory.quotient

def lift.is_lift' {C D : Type*} [category C] [category D]
  (r : hom_rel C) (F : C ⥤ D)   (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) :
  (functor r) ⋙ lift r F H = F :=
category_theory.functor.ext (λ X, rfl) (by tidy)

end category_theory.quotient

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

@[simps]
def forget : bifibrant_object C ⥤ C := forget_fib C ⋙ cofibrant_object.forget C

variable {C}

@[simp]
def weq : morphism_property (bifibrant_object C) := λ X Y f, M.weq f

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

def lift {D : Type*} [category D] (F : bifibrant_object C ⥤ D) (hF : weq.is_inverted_by F) :
  bifibrant_object.homotopy_category C ⥤ D :=
category_theory.quotient.lift _ F (λ X Y f₁ f₂ h, begin
  rcases h with ⟨P, h'⟩,
  let Cyl := cylinder.some X.obj,
  let H := h'.some.to_left_homotopy Cyl,
  let I := bifibrant_object.mk (Cyl.I),
  let s : I ⟶ X := Cyl.σ,
  let η : I ⟶ Y := H.h,
  let d₀ : X ⟶ I := Cyl.d₀,
  let d₁ : X ⟶ I := Cyl.d₁,
  have eq₁ : f₁ = d₀ ≫ η := H.h₀.symm,
  have eq₂ : f₂ = d₁ ≫ η := H.h₁.symm,
  simp only [eq₁, eq₂, F.map_comp],
  congr' 1,
  haveI : is_iso (F.map s) := hF s weak_eq.property,
  simp only [← cancel_mono (F.map s), ← F.map_comp],
  congr' 1,
  exact Cyl.σd₀.trans Cyl.σd₁.symm,
end)

lemma fac {D : Type*} [category D] (F : bifibrant_object C ⥤ D) (hF : weq.is_inverted_by F) :
  Q ⋙ lift F hF = F :=
by apply category_theory.quotient.lift.is_lift'

lemma uniq {D : Type*} [category D] (G₁ G₂ : bifibrant_object.homotopy_category C ⥤ D)
  (h₁₂ : Q ⋙ G₁ = Q ⋙ G₂) : G₁ = G₂ :=
begin
  refine category_theory.functor.ext _ _,
  { rintro ⟨X⟩,
    convert functor.congr_obj h₁₂ X, },
  { rintros ⟨X⟩ ⟨Y⟩ f,
    rcases Q_map_surjective _ _ f with ⟨g, hg⟩,
    dsimp only at hg,
    subst hg,
    convert category_theory.functor.congr_map_conjugate h₁₂ g, },
end

variable (C)

def strict_universal_property_fixed_target (D : Type*) [category D] :
  localization.strict_universal_property_fixed_target (Q : bifibrant_object C ⥤ _) weq D :=
{ inverts_W := sorry,
  lift := lift,
  fac := fac,
  uniq := uniq, }

instance Q_is_localization : (Q : bifibrant_object C ⥤ _).is_localization weq :=
functor.is_localization.mk' _ _ (strict_universal_property_fixed_target C _)
  (strict_universal_property_fixed_target C _)

end homotopy_category

end bifibrant_object

end model_category

end algebraic_topology
