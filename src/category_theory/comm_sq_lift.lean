/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.comm_sq
import category_theory.lifting_properties

noncomputable theory

namespace category_theory

open category

variables {C : Type*} [category C]

variables {A B B' X Y Y' : C} {f : A ⟶ X} {i : A ⟶ B} (i' : B ⟶ B') {p : X ⟶ Y} (p' : Y ⟶ Y') {g : B ⟶ Y}
variables {W Z : C} {q : W ⟶ Z} {f' : X ⟶ W} {g' : Y ⟶ Z}

namespace comm_sq

@[nolint has_inhabited_instance]
structure lifts (sq : comm_sq f i p g) :=
(l : B ⟶ X) (fac_left : i ≫ l = f) (fac_right : l ≫ p = g)

/-lemma comp (sq₁ : comm_sq f i p g) (sq₂ : comm_sq f' p q g') :
  comm_sq (f ≫ f') i q (g ≫ g') :=
⟨by simp only [assoc, sq₂.w, sq₁.w_assoc]⟩

namespace lifts

def comp {sq₁ : comm_sq f i p g} {sq₂ : comm_sq f' p q g'}
  (l₁ : lifts sq₁) (l₂ : lifts sq₂) : lifts (sq₁.comp sq₂) :=
{ l := l₁.l ≫ p ≫ l₂.l,
  fac_left := by rw [l₂.fac_left, ← assoc, l₁.fac_left],
  fac_right := begin
    simp only [assoc, l₂.fac_right],
    simp only [← assoc, l₁.fac_right],
  end }

end lifts-/

variable (sq : comm_sq f i p g)

class has_lift : Prop := (exists_lift : nonempty sq.lifts)

def lift [hsq : has_lift sq] : B ⟶ X :=
hsq.exists_lift.some.l

@[simp, reassoc]
lemma fac_left [hsq : has_lift sq] : i ≫ sq.lift = f :=
hsq.exists_lift.some.fac_left

@[simp, reassoc]
lemma fac_right [hsq : has_lift sq] : sq.lift ≫ p = g :=
hsq.exists_lift.some.fac_right

end comm_sq

variables (i p)

class has_lifting_property_new : Prop :=
(sq_has_lift : ∀ (f : A ⟶ X) (g : B ⟶ Y) (sq : comm_sq f i p g), sq.has_lift)

@[priority 100]
instance sq_has_lift_of_has_lifting_property (sq : comm_sq f i p g)
  [hip : has_lifting_property_new i p] : sq.has_lift := by apply hip.sq_has_lift

namespace has_lifting_property_new

@[priority 100]
instance of_left_iso [is_iso i] : has_lifting_property_new i p :=
⟨λ f g sq, ⟨nonempty.intro 
  { l := inv i ≫ f,
    fac_left := by simp only [is_iso.hom_inv_id_assoc],
    fac_right := by simp only [sq.w, assoc, is_iso.inv_hom_id_assoc], }⟩⟩

@[priority 100]
instance of_right_iso [is_iso p] : has_lifting_property_new i p :=
⟨λ f g sq, ⟨nonempty.intro
  { l := g ≫ inv p,
    fac_left := by simp only [← sq.w_assoc, is_iso.hom_inv_id, comp_id],
    fac_right := by simp only [assoc, is_iso.inv_hom_id, comp_id], }⟩⟩

instance of_comp_left [has_lifting_property_new i p] [has_lifting_property_new i' p] :
  has_lifting_property_new (i ≫ i') p :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw assoc at fac,
  exact ⟨nonempty.intro
  { l := (comm_sq.mk (comm_sq.mk fac).fac_right).lift,
    fac_left := by simp only [assoc, comm_sq.fac_left],
    fac_right := by simp only [comm_sq.fac_right], }⟩,
end⟩

instance of_comp_right [has_lifting_property_new i p] [has_lifting_property_new i p'] :
  has_lifting_property_new i (p ≫ p') :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw ← assoc at fac,
  let sq₂ := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
  exact ⟨nonempty.intro 
  { l := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
    fac_left := by simp only [comm_sq.fac_left],
    fac_right := by simp only [comm_sq.fac_right_assoc, comm_sq.fac_right], }⟩,
end⟩

end has_lifting_property_new

lemma test {φ : B' ⟶ Y} (sq : comm_sq f (i ≫ i') p φ) [is_iso i] [is_iso i'] :
  sq.has_lift :=
begin
  apply_instance,
end

end category_theory