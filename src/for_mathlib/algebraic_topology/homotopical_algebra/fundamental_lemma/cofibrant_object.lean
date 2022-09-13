/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.homotopies
import for_mathlib.algebraic_topology.homotopical_algebra.fibrant
import category_theory.full_subcategory
import category_theory.quotient

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

@[simps]
def inclusion : cofibrant_object C ⥤ C := induced_functor _

variable {C}

def right_homotopy : hom_rel (cofibrant_object C) := λ A X f₁ f₂,
∃ (P : path_object X.obj), nonempty (right_homotopy P.pre f₁ f₂)

namespace right_homotopy

def symm {A X : cofibrant_object C} {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) :
  right_homotopy f₂ f₁ :=
⟨H.some.symm, nonempty.intro H.some_spec.some.symm⟩

lemma comp_left {A B X : cofibrant_object C} {g₁ g₂ : B ⟶ X} (H : right_homotopy g₁ g₂)
  (f : A ⟶ B) : right_homotopy (f ≫ g₁) (f ≫ g₂) :=
⟨H.some, nonempty.intro (H.some_spec.some.comp_left f)⟩

lemma comp_right {A X Y : cofibrant_object C} {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂)
  (g : X ⟶ Y) : right_homotopy (f₁ ≫ g) (f₂ ≫ g) :=
begin
  cases H with P hP,
  rcases hP.some.with_cof_σ_of_right_homotopy with ⟨P', H', hP'⟩,
  haveI : cofibration P'.σ := hP',
  let Q := path_object.some Y.1,
  suffices H'' : model_category.right_homotopy Q.pre (P'.d₀ ≫ g) (P'.d₁ ≫ g),
  { exact ⟨Q, nonempty.intro { h := H'.h ≫ H''.h, }⟩, },
  apply right_homotopy.extension P'.σ,
  simp only [pre_path_object.d₀σ_assoc, pre_path_object.d₁σ_assoc],
  apply right_homotopy.refl,
end

end right_homotopy

inductive trans_closure {A X : cofibrant_object C} : (A ⟶ X) → (A ⟶ X) → Prop
| right_homotopy {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) : trans_closure f₁ f₂
| trans {f₁ f₂ f₃ : A ⟶ X} (H₁₂ : trans_closure f₁ f₂) (H₂₃ : trans_closure f₂ f₃) :
  trans_closure f₁ f₃

lemma trans_closure.is_equiv (A X : cofibrant_object C) :
  is_equiv (A ⟶ X) trans_closure :=
{ refl := λ f, trans_closure.right_homotopy
    ⟨path_object.some X.1, nonempty.intro (right_homotopy.refl _ f)⟩,
  trans := λ f₁ f₂ f₃, trans_closure.trans,
  symm := λ f₁ f₂ H, begin
    induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₂₁ H₃₂,
    { exact trans_closure.right_homotopy H₁₂.symm, },
    { exact trans_closure.trans H₃₂ H₂₁, },
  end, }

end cofibrant_object

end model_category

end algebraic_topology
