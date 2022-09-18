/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.homotopies
import for_mathlib.algebraic_topology.homotopical_algebra.fibrant
import category_theory.full_subcategory
import for_mathlib.category_theory.quotient_misc
import for_mathlib.category_theory.localization.predicate

noncomputable theory

open algebraic_topology
open category_theory
open category_theory.limits
open category_theory.category

namespace algebraic_topology

namespace model_category

variables (C : Type*) [category C] [M : model_category C]
include M

@[nolint has_nonempty_instance]
structure cofibrant_object :=
(obj : C)
[cof : is_cofibrant obj]

namespace cofibrant_object

instance (X : cofibrant_object C) : is_cofibrant X.obj := X.cof

instance : category (cofibrant_object C) := induced_category.category (λ X, X.obj)

@[simps, derive full, derive faithful]
def forget : cofibrant_object C ⥤ C := induced_functor _

variable {C}

@[simp]
def weq : morphism_property (cofibrant_object C) := λ X Y f, M.weq ((forget C).map f)

def right_homotopy : hom_rel (cofibrant_object C) := λ A X f₁ f₂,
∃ (P : path_object X.obj), nonempty (right_homotopy P.pre f₁ f₂)

namespace right_homotopy

lemma mk {A X : cofibrant_object C} {f₁ f₂ : A ⟶ X} (P : path_object X.obj)
  (H : model_category.right_homotopy P.pre f₁ f₂) : right_homotopy f₁ f₂ :=
⟨P, nonempty.intro H⟩

lemma symm {A X : cofibrant_object C} {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) :
  right_homotopy f₂ f₁ :=
right_homotopy.mk H.some.symm H.some_spec.some.symm

lemma comp_left {A B X : cofibrant_object C} {g₁ g₂ : B ⟶ X} (H : right_homotopy g₁ g₂)
  (f : A ⟶ B) : right_homotopy (f ≫ g₁) (f ≫ g₂) :=
right_homotopy.mk H.some (H.some_spec.some.comp_left f)

lemma comp_right {A X Y : cofibrant_object C} {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂)
  (g : X ⟶ Y) : right_homotopy (f₁ ≫ g) (f₂ ≫ g) :=
begin
  cases H with P hP,
  rcases hP.some.with_cof_σ_of_right_homotopy with ⟨P', H', hP'⟩,
  haveI : cofibration P'.σ := hP',
  let Q := path_object.some Y.1,
  suffices H'' : model_category.right_homotopy Q.pre (P'.d₀ ≫ g) (P'.d₁ ≫ g),
  { exact mk Q { h := H'.h ≫ H''.h, }, },
  apply right_homotopy.extension P'.σ,
  simp only [pre_path_object.d₀σ_assoc, pre_path_object.d₁σ_assoc],
  apply right_homotopy.refl,
end

inductive trans_closure ⦃A X : cofibrant_object C⦄ : (A ⟶ X) → (A ⟶ X) → Prop
| mk {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) : trans_closure f₁ f₂
| trans {f₁ f₂ f₃ : A ⟶ X} (H₁₂ : trans_closure f₁ f₂) (H₂₃ : trans_closure f₂ f₃) :
  trans_closure f₁ f₃

namespace trans_closure

lemma is_equiv (A X : cofibrant_object C) :
  is_equiv (A ⟶ X) (λ f₁ f₂, trans_closure f₁ f₂) :=
{ refl := λ f, trans_closure.mk (right_homotopy.mk
    (path_object.some X.1) (right_homotopy.refl _ f)),
  trans := λ f₁ f₂ f₃ H₁₂ H₂₃, trans_closure.trans H₁₂ H₂₃,
  symm := λ f₁ f₂ H, begin
    induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₂₁ H₃₂,
    { exact trans_closure.mk H₁₂.symm, },
    { exact trans_closure.trans H₃₂ H₂₁, },
  end, }

lemma comp_left {A B X : cofibrant_object C} {g₁ g₂ : B ⟶ X} (H : trans_closure g₁ g₂)
  (f : A ⟶ B) : trans_closure (f ≫ g₁) (f ≫ g₂) :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact mk (H₁₂.comp_left f), },
  { exact trans H₁₂' H₂₃', }
end

lemma comp_right {A X Y : cofibrant_object C} {f₁ f₂ : A ⟶ X} (H : trans_closure f₁ f₂)
  (g : X ⟶ Y) : trans_closure (f₁ ≫ g) (f₂ ≫ g) :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact mk (H₁₂.comp_right g), },
  { exact trans H₁₂' H₂₃', },
end

end trans_closure

end right_homotopy

variable (C)

@[simp]
def homotopy_relation : hom_rel (cofibrant_object C) := right_homotopy.trans_closure

instance : congruence (homotopy_relation C) :=
{ is_equiv := right_homotopy.trans_closure.is_equiv,
  comp_left := λ A B X f g₁ g₂ H, H.comp_left f,
  comp_right := λ A X Y f₁ f₂ g H, H.comp_right g, }

@[nolint has_nonempty_instance]
def homotopy_category := quotient (right_homotopy.trans_closure : hom_rel (cofibrant_object C))

instance : congruence (right_homotopy.trans_closure : hom_rel (cofibrant_object C)) :=
{ is_equiv := right_homotopy.trans_closure.is_equiv,
  comp_left := λ A B X f g₁ g₂ H, H.comp_left f,
  comp_right := λ A X Y f₁ f₂ g H, H.comp_right g, }

instance : category (homotopy_category C) := quotient.category _

variable {C}

def homotopy_category.Q : cofibrant_object C ⥤ homotopy_category C := quotient.functor _

namespace homotopy_category

@[simp]
lemma Q_map {X Y : cofibrant_object C} (f : X ⟶ Y) :
  Q.map f = (quotient.functor _).map f := rfl

lemma Q_map_surjective (X Y : cofibrant_object C) :
  function.surjective (@category_theory.functor.map _ _ _ _ Q X Y) :=
by apply quotient.functor_map_surjective

lemma Q_map_eq_iff {X Y : cofibrant_object C} [hY : is_fibrant Y.obj]
  (Cyl : cylinder X.obj) (f₁ f₂ : X ⟶ Y) :
  (Q.map f₁ = Q.map f₂) ↔ nonempty (left_homotopy Cyl.pre f₁ f₂) :=
begin
  split,
  { intro h,
    simp only [Q_map, quotient.functor_map_eq_iff] at h,
    induction h with f₁ f₂ H f₁ f₂ f₃ H₁₂ H₂₃ H H',
    { exact nonempty.intro (H.some_spec.some.to_left_homotopy Cyl), },
    { exact nonempty.intro ((H.some.trans H'.some).change_cylinder Cyl), }, },
  { intro h,
    apply category_theory.quotient.sound,
    refine right_homotopy.trans_closure.mk
      (right_homotopy.mk (path_object.some Y.obj) (h.some.to_right_homotopy _)), },
end

lemma Q_map_eq_iff' {X Y : cofibrant_object C} [is_fibrant Y.obj]
  (P : path_object Y.obj) (f₁ f₂ : X ⟶ Y) :
  (Q.map f₁ = Q.map f₂) ↔ nonempty (model_category.right_homotopy P.pre f₁ f₂) :=
begin
  rw Q_map_eq_iff (cylinder.some X.obj) f₁ f₂,
  split,
  { exact λ h, nonempty.intro (h.some.to_right_homotopy _), },
  { exact λ h, nonempty.intro (h.some.to_left_homotopy _), },
end

def weq : morphism_property (cofibrant_object.homotopy_category C) :=
λ X Y f, ∃ (g : X.as.obj ⟶ Y.as.obj) (hg : model_category.weq g), f = Q.map g

lemma weq_Q_map_iff {X Y : cofibrant_object C} (f : X ⟶ Y) :
  weq (Q.map f) ↔ cofibrant_object.weq f :=
begin
  refine ⟨λ hf, _, λ hf, ⟨f, hf, rfl⟩⟩,
  rcases hf with ⟨g : X ⟶ Y, hg, H⟩,
  dsimp only [Q] at H,
  rw quotient.functor_map_eq_iff at H,
  induction H with f₁ f₂ H f₁ f₂ f₃ H₁₂ H₂₃ h₁ h₂,
  { rcases H with ⟨P, H⟩,
    let f'₁ : X.obj ⟶ Y.obj := f₁,
    let f'₂ : X.obj ⟶ Y.obj := f₂,
    change model_category.weq f'₁,
    change model_category.weq f'₂ at hg,
    let h : model_category.right_homotopy P.pre f'₁ f'₂ := H.some,
    rw ← h.h₀,
    rw ← h.h₁ at hg,
    exact CM2.of_comp _ _ (CM2.of_comp_right _ _ weak_eq.property hg) weak_eq.property, },
  { exact h₁ (h₂ hg), },
end

end homotopy_category

end cofibrant_object

variable (C)

@[derive category]
def Hocof' := (cofibrant_object.weq : morphism_property (cofibrant_object C)).localization

variable {C}

def Lcof' : cofibrant_object C ⥤ Hocof' C :=
(cofibrant_object.weq : morphism_property (cofibrant_object C)).Q

instance Lcof'_is_localization :
(Lcof' : cofibrant_object C ⥤ Hocof' C).is_localization cofibrant_object.weq :=
by { dsimp [Lcof'], apply_instance, }

end model_category

end algebraic_topology
