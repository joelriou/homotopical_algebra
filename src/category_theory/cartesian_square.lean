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

variables (C : Type*) [category C]

@[derive category]
def square := arrow (arrow C)

variable {C}

namespace arrow

@[ext]
lemma ext (f₁ f₂ : arrow C) (h₁ : f₁.left = f₂.left) (h₂ : f₁.right = f₂.right)
  (h₃ : f₁.hom = eq_to_hom h₁ ≫ f₂.hom ≫ eq_to_hom h₂.symm) : f₁ = f₂ :=
begin
  cases f₁,
  cases f₂,
  dsimp at h₁ h₂ h₃,
  substs h₁ h₂ h₃,
  erw [comp_id, id_comp],
end

end arrow

namespace square

@[ext]
lemma ext (Sq₁ Sq₂ : square C) (h₁ : Sq₁.left = Sq₂.left) (h₂ : Sq₁.right = Sq₂.right)
  (h₃ : Sq₁.hom = eq_to_hom h₁ ≫ Sq₂.hom ≫ eq_to_hom h₂.symm) : Sq₁ = Sq₂ :=
begin
  cases Sq₁,
  cases Sq₂,
  dsimp at h₁ h₂ h₃,
  substs h₁ h₂,
  congr,
  erw [h₃, id_comp, comp_id],
end

@[simps]
def mk {f g : arrow C} (sq : f ⟶ g) : square C := arrow.mk sq

@[simps]
def mk' (f g : arrow C) (sq : f ⟶ g) : square C := square.mk sq

@[simps]
def mk'' {X₁ X₂ Y₁ Y₂ : C} (l : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (t : X₁ ⟶ X₂) (r : X₂ ⟶ Y₂)
  (fac : t ≫ r = l ≫ b) : square C := mk' (arrow.mk l) (arrow.mk r) (arrow.hom_mk fac)

@[simps]
def top (Sq : square C) : arrow C := arrow.mk Sq.hom.left

@[simps]
def bottom (Sq : square C) : arrow C := arrow.mk Sq.hom.right

@[simps]
def hom_vert (Sq : square C) : Sq.top ⟶ Sq.bottom :=
{ left := Sq.left.hom,
  right := Sq.right.hom,
  w' := Sq.hom.w'.symm }

@[simps]
def flip (Sq : square C) : square C :=
{ left := Sq.top,
  right := Sq.bottom,
  hom := Sq.hom_vert }

lemma flip_flip (Sq : square C) : Sq.flip.flip = Sq := by tidy

@[simps]
def horizontal_comp (Sq₁ Sq₂ : square C) (e : Sq₁.right ≅ Sq₂.left) : square C :=
square.mk' Sq₁.left Sq₂.right (Sq₁.hom ≫ e.hom ≫ Sq₂.hom)

@[simps]
def vertical_comp (Sq₁ Sq₂ : square C) (e : Sq₁.bottom ≅ Sq₂.top) : square C :=
(square.mk' Sq₁.top Sq₂.bottom (Sq₁.hom_vert ≫ e.hom ≫ Sq₂.hom_vert)).flip

lemma vertical_comp_eq (Sq₁ Sq₂ : square C) (e : Sq₁.bottom ≅ Sq₂.top) :
vertical_comp Sq₁ Sq₂ e = (horizontal_comp Sq₁.flip Sq₂.flip e).flip := by refl

@[simps]
def cone (Sq : square C) : pullback_cone Sq.right.hom Sq.bottom.hom :=
pullback_cone.mk Sq.top.hom Sq.left.hom Sq.hom.w'

@[simps]
def cocone (Sq : square C) : pushout_cocone Sq.top.hom Sq.left.hom :=
pushout_cocone.mk Sq.right.hom Sq.bottom.hom Sq.hom.w'

@[simp]
def is_cartesian (Sq : square C) := is_limit (Sq.cone)

@[simp]
def is_cocartesian (Sq : square C) := is_colimit (Sq.cocone)

def is_cocartesian_of_eq (Sq₁ Sq₂ : square C) (h₀ : Sq₁ = Sq₂) (h₁ : Sq₁.is_cocartesian) :
  Sq₂.is_cocartesian :=
by { subst h₀, exact h₁, }

end square

@[simps]
def pushout_square {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] : square C :=
square.mk' (arrow.mk f₂) (arrow.mk (pushout.inl : A₁ ⟶ pushout f₁ f₂))
{ left := f₁,
  right := pushout.inr,
  w' := pushout.condition, }

@[simps]
def pushout_square' {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] : square C :=
square.mk' (arrow.mk f₁) (arrow.mk (pushout.inr : A₂ ⟶ pushout f₁ f₂))
{ left := f₂,
  right := pushout.inl,
  w' := pushout.condition.symm, }

lemma flip_pushout_square {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  pushout_square' f₁ f₂ = (pushout_square f₁ f₂).flip := by refl

@[ext]
lemma cocone.ext {J C : Type*} [category J] [category C] {F : J ⥤ C} (c₁ c₂ : cocone F)
  (hX : c₁.X = c₂.X) (hι : c₁.ι = c₂.ι ≫ eq_to_hom (by rw hX)) : c₁ = c₂ :=
begin
  cases c₁,
  cases c₂,
  dsimp at hX,
  subst hX,
  congr,
  { convert hι,
    erw comp_id, },
end

def pushout_square_is_cocartesian {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  (pushout_square f₁ f₂).is_cocartesian :=
begin
  dsimp [square.is_cocartesian],
  convert limits.colimit.is_colimit (span f₁ f₂),
  ext x,
  { cases x,
    { have h := (colimit.cocone (span f₁ f₂)).ι.naturality walking_span.hom.fst,
      exact h, },
    { cases x; { erw comp_id, refl, }, }, },
  { refl, }
end
namespace square
namespace is_cocartesian

@[protected]
def flip {Sq : square C} (hSq : Sq.is_cocartesian) : Sq.flip.is_cocartesian :=
pushout_cocone.flip_is_colimit hSq

@[protected]
def unflip {Sq : square C} (hSq : Sq.flip.is_cocartesian) : Sq.is_cocartesian :=
by { rw ← Sq.flip_flip,
exact is_cocartesian.flip hSq, }

def has_pushout {Sq : square C} (hSq : Sq.is_cocartesian) : has_pushout Sq.top.hom Sq.left.hom :=
⟨nonempty.intro
  { cocone := Sq.cocone,
  is_colimit := hSq, }⟩

end is_cocartesian

namespace is_cartesian

def has_pullback {Sq : square C} (hSq : Sq.is_cartesian) : has_pullback Sq.right.hom Sq.bottom.hom :=
⟨nonempty.intro
  { cone := Sq.cone,
    is_limit := hSq, }⟩

end is_cartesian

end square

def pushout_square'_is_cocartesian {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  (pushout_square' f₁ f₂).is_cocartesian :=
begin
  rw flip_pushout_square,
  apply square.is_cocartesian.flip,
  apply pushout_square_is_cocartesian,
end

def horizontal_comp_is_cocartesian (i₁ i₂ i₃ : arrow C) (sq₁₂ : i₁ ⟶ i₂) (sq₂₃ : i₂ ⟶ i₃)
  (h₁₂ : (square.mk sq₁₂).is_cocartesian) (h₂₃ : (square.mk sq₂₃).is_cocartesian) :
  (square.mk (sq₁₂ ≫ sq₂₃)).is_cocartesian :=
begin
  rcases i₁ with ⟨X₁, Y₁, i₁⟩,
  rcases i₂ with ⟨X₂, Y₂, i₂⟩,
  rcases i₃ with ⟨X₃, Y₃, i₃⟩,
  rcases sq₁₂ with ⟨f₁, g₁, w₁₂⟩,
  rcases sq₂₃ with ⟨f₂, g₂, w₂₃⟩,
  have h := big_square_is_pushout f₁ f₂ g₁ g₂ i₁ i₂ i₃ w₁₂.symm w₂₃.symm h₂₃.flip h₁₂.flip,
  apply square.is_cocartesian.unflip,
  exact h,
end

namespace square

def is_cocartesian_of_horizontal_is_iso (Sq : square C) (hSq : is_iso Sq.hom) : Sq.is_cocartesian :=
begin
  letI := hSq,
  let e := as_iso Sq.hom,
  let e₁ := (comma.fst _ _).map_iso e,
  let e₂ := (comma.snd _ _).map_iso e,
  dsimp at *,
  refine pushout_cocone.is_colimit_aux _ (λ s, e₂.inv ≫ s.ι.app walking_span.right) _ _ _,
  { intro s,
    dsimp [cocone],
    have h₁ := s.ι.naturality walking_span.hom.fst,
    have h₂ := s.ι.naturality walking_span.hom.snd,
    erw comp_id at h₁ h₂,
    have he := e.inv.w',
    dsimp at he h₁ h₂,
    erw [← assoc, ← he, assoc, h₂, ← h₁],
    simp only [arrow.inv_left, is_iso.inv_hom_id_assoc], },
  { intro s,
    dsimp [cocone],
    simp only [arrow.inv_right, is_iso.hom_inv_id_assoc], },
  { intros s m hm,
    rw ← hm walking_span.right,
    dsimp [cocone],
    simp only [arrow.inv_right, is_iso.inv_hom_id_assoc], },
end

def is_cocartesian_of_vertical_is_iso (Sq : square C) (h : is_iso Sq.flip.hom) : Sq.is_cocartesian :=
(is_cocartesian_of_horizontal_is_iso Sq.flip h).unflip

def is_cocartesian_of_horizontal_comp (Sq₁ Sq₂ : square C) (e : Sq₁.right ≅ Sq₂.left)
  (h₁ : Sq₁.is_cocartesian) (h₂ : Sq₂.is_cocartesian) : 
  (Sq₁.horizontal_comp Sq₂ e).is_cocartesian :=
begin
  apply horizontal_comp_is_cocartesian _ _ _ Sq₁.hom _ h₁,
  refine horizontal_comp_is_cocartesian _ _ _ e.hom Sq₂.hom _ h₂,
  exact is_cocartesian_of_horizontal_is_iso _ (is_iso.of_iso e),
end

def is_cocartesian_of_vertical_comp (Sq₁ Sq₂ : square C) (e : Sq₁.bottom ≅ Sq₂.top)
  (h₁ : Sq₁.is_cocartesian) (h₂ : Sq₂.is_cocartesian) : 
  (Sq₁.vertical_comp Sq₂ e).is_cocartesian :=
begin
  rw square.vertical_comp_eq,
  apply square.is_cocartesian.flip,
  exact is_cocartesian_of_horizontal_comp Sq₁.flip Sq₂.flip e h₁.flip h₂.flip,
end

def is_cocartesian_of_iso (Sq₁ Sq₂ : square C) (e : Sq₁ ≅ Sq₂) (h : Sq₁.is_cocartesian) :
  Sq₂.is_cocartesian :=
begin
  let e₁ := (comma.fst _ _).map_iso e.symm,
  let e₂ := (comma.snd _ _).map_iso e,
  have h₁₃ := is_cocartesian_of_horizontal_comp _ Sq₁ (by refl)
    (is_cocartesian_of_horizontal_is_iso (square.mk e₁.hom) (is_iso.of_iso e₁)) h,
  have h₁₄ := is_cocartesian_of_horizontal_comp _ (square.mk e₂.hom) (by refl)
    h₁₃ (is_cocartesian_of_horizontal_is_iso _ (is_iso.of_iso e₂)),
  refine is_cocartesian_of_eq _ _ _ h₁₄,
  ext1; try { refl, },
  { have h₁ := e.hom.w,
    have h₂ := e₁.hom_inv_id,
    dsimp [horizontal_comp] at h₁ h₂ ⊢,
    erw [id_comp, id_comp, assoc, comp_id, id_comp, ← h₁, ← assoc, h₂, id_comp], },
end

end square

end category_theory

