/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.pullbacks
import category_theory.comma_op

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

def cone_of_square {f g : arrow C} (sq : f ⟶ g) : pullback_cone g.hom sq.right :=
pullback_cone.mk sq.left f.hom sq.w'

def cocone_of_square {f g : arrow C} (sq : f ⟶ g) : pushout_cocone sq.left f.hom :=
pushout_cocone.mk g.hom sq.right sq.w'

def is_cartesian {f g : arrow C} (sq : f ⟶ g) := is_limit (cone_of_square sq)

def is_cocartesian {f g : arrow C} (sq : f ⟶ g) := is_colimit (cocone_of_square sq)

def pushout_square {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  arrow.mk f₂ ⟶ arrow.mk (pushout.inl : A₁ ⟶ pushout f₁ f₂) :=
{ left := f₁,
  right := pushout.inr,
  w' := pushout.condition, }

def pushout_square' {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  arrow.mk f₁ ⟶ arrow.mk (pushout.inr : A₂ ⟶ pushout f₁ f₂) :=
{ left := f₂,
  right := pushout.inl,
  w' := pushout.condition.symm, }


lemma pushout_square_is_cocartesian {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  is_cocartesian (pushout_square f₁ f₂) :=
begin
  dsimp [is_cocartesian],
  convert limits.colimit.is_colimit (span f₁ f₂),
  sorry,
end

lemma pushout_square'_is_cocartesian {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  is_cocartesian (pushout_square' f₁ f₂) := sorry

/- opposites... -/

end category_theory

