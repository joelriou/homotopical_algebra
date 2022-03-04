/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.finite_products
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

lemma congr_hom {f₁ f₂ : arrow C} (h : f₁ = f₂) :
  f₁.hom = eq_to_hom (by rw h) ≫ f₂.hom ≫ eq_to_hom (by rw h) :=
by { subst h, erw [id_comp, comp_id], }

lemma congr_left {f₁ f₂ : arrow C} (h : f₁ = f₂) : f₁.left = f₂.left := by rw h
lemma congr_right {f₁ f₂ : arrow C} (h : f₁ = f₂) : f₁.right = f₂.right := by rw h

def mk_iso {f g : arrow C} (e₁ : f.left ≅ g.left) (e₂ : f.right ≅ g.right)
  (fac : e₁.hom ≫ g.hom = f.hom ≫ e₂.hom) :
  f ≅ g :=
{ hom :=
  { left := e₁.hom,
    right := e₂.hom,
    w' := fac, },
  inv :=
  { left := e₁.inv,
    right := e₂.inv,
    w' := begin
      dsimp,
      erw [← comp_id f.hom, ← e₂.hom_inv_id],
      slice_lhs 2 3 { rw ← fac, },
      slice_lhs 1 2 { rw e₁.inv_hom_id, },
      rw id_comp,
    end, },
  hom_inv_id' := begin
    ext,
    exacts [e₁.hom_inv_id, e₂.hom_inv_id],
  end,
  inv_hom_id' := begin
    ext,
    exacts [e₁.inv_hom_id, e₂.inv_hom_id],
  end, }

namespace hom

lemma congr_left {f₁ f₂ : arrow C} {φ₁ φ₂ : f₁ ⟶ f₂} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by rw h
lemma congr_right {f₁ f₂ : arrow C} {φ₁ φ₂ : f₁ ⟶ f₂} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by rw h

end hom

@[simps]
def coproduct_cofan {J : Type*} (f : J → arrow C) [has_coproduct (λ j, (f j).left)]
  [has_coproduct (λ j, (f j).right)] : cofan f :=
{ X :=
  { left := ∐ (λ j, (f j).left),
    right := ∐ (λ j, (f j).right),
    hom := limits.sigma.map (λ j, (f j).hom) },
  ι :=
  { app := λ j,
    { left := limits.sigma.ι ((λ j, (f j).left)) j,
      right := limits.sigma.ι ((λ j, (f j).right)) j, } } }

@[simps]
def binary_coproduct_cofan (f₁ f₂ : arrow C) [has_binary_coproduct f₁.left f₂.left]
  [has_binary_coproduct f₁.right f₂.right] : binary_cofan f₁ f₂ :=
{ X :=
  { left := coprod f₁.left f₂.left,
    right := coprod f₁.right f₂.right,
    hom := coprod.map f₁.hom f₂.hom },
  ι :=
  { app := λ j, begin
    cases j,
    { exact { left := coprod.inl, right := coprod.inl, }, },
    { exact { left := coprod.inr, right := coprod.inr, }, },
  end, } }

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

lemma mk_eq (Sq : square C) : square.mk Sq.hom = Sq :=
by { cases Sq, dsimp [arrow.mk], refl, }

@[simps]
def mk' (f g : arrow C) (sq : f ⟶ g) : square C := square.mk sq

@[simps]
def mk'' {X₁ X₂ Y₁ Y₂ : C} (l : X₁ ⟶ Y₁) (r : X₂ ⟶ Y₂) (t : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂)
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

@[simps]
def coprod_square (A₁ A₂ : C) [has_initial C] [has_binary_coproduct A₁ A₂] : square C :=
square.mk' (arrow.mk (initial.to A₂)) (arrow.mk (coprod.inl : A₁ ⟶ coprod A₁ A₂ ))
{ left := initial.to A₁,
  right := coprod.inr,
  w' := by { dsimp, apply subsingleton.elim, }, }

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

def coprod_square_is_cocartesian (A₁ A₂ : C) [has_initial C] [has_binary_coproduct A₁ A₂] :
  (coprod_square A₁ A₂).is_cocartesian :=
begin
  dsimp [square.is_cocartesian],
  refine pushout_cocone.is_colimit_aux _
    (λ s, coprod.desc (s.ι.app walking_span.left) (s.ι.app walking_span.right)) _ _ _,
  { intro s, erw [coprod.inl_desc], },
  { intro s, erw [coprod.inr_desc], },
  { intros s m hm,
    dsimp [square.cocone],
    ext,
    { erw [coprod.inl_desc, ← hm, square.cocone_ι_app, coprod_square_right_hom], },
    { erw [coprod.inr_desc, ← hm, square.cocone_ι_app, coprod_square_hom_right], }, },
end

def coprod_inl_with_identity_is_cocartesian (f : arrow C) (A : C) [hl : has_binary_coproduct f.left A]
  [hr : has_binary_coproduct f.right A] :
  (square.mk (@arrow.binary_coproduct_cofan _ _ f (arrow.mk (𝟙 A)) hl hr).inl).is_cocartesian :=
begin
  dsimp [square.is_cocartesian],
  refine limits.pushout_cocone.is_colimit_aux _
    (λ s, coprod.desc (s.ι.app walking_span.right) (coprod.inr ≫ s.ι.app walking_span.left)) _ _ _,
  { intro s,
    dsimp [square.mk, square.cocone],
    ext,
    { simp only [coprod.map_desc, coprod.inl_desc],
      erw [s.ι.naturality walking_span.hom.snd],
      erw ← s.ι.naturality walking_span.hom.fst,
      refl, },
    { simp only [coprod.map_desc, id_comp, coprod.inr_desc], }, },
  { intro s,
    dsimp [square.mk, square.cocone, arrow.binary_coproduct_cofan],
    simp, },
  { intros s m hm,
    ext,
    { simpa only [← hm walking_span.right, coprod.inl_desc], },
    { erw [coprod.inr_desc, ← hm walking_span.left, coprod.inr_map_assoc, id_comp], }, },
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

@[protected]
def has_pushout {Sq : square C} (hSq : Sq.is_cocartesian) : has_pushout Sq.top.hom Sq.left.hom :=
⟨nonempty.intro
  { cocone := Sq.cocone,
  is_colimit := hSq, }⟩

@[simps]
def couniversal_lift {Sq : square C} (hSq : Sq.is_cocartesian) (Sq' : square C)
  (h₁ : Sq.top = Sq'.top) (h₂ : Sq.left = Sq'.left) : Sq ⟶ Sq' :=
begin
  let φ₁ : Sq.left ⟶ Sq'.left :=
  { left := eq_to_hom (arrow.congr_left h₂),
    right := eq_to_hom (arrow.congr_right h₂),
    w' := by simp only [arrow.congr_hom h₂, eq_to_hom_map, assoc,
      eq_to_hom_trans, eq_to_hom_refl, comp_id], },
  have eq : Sq.top.hom ≫ eq_to_hom (by exact arrow.congr_right h₁) ≫ Sq'.right.hom =
    Sq.left.hom ≫ eq_to_hom (by exact arrow.congr_right h₂) ≫ Sq'.bottom.hom,
  { erw [arrow.congr_hom h₁, arrow.congr_hom h₂],
    simpa only [top_hom, assoc, eq_to_hom_trans_assoc, eq_to_hom_refl,
      id_comp, arrow.w, bottom_hom], },
  let φ₂ : Sq.right ⟶ Sq'.right :=
  { left := eq_to_hom (arrow.congr_right h₁),
    right := hSq.desc (pushout_cocone.mk _ _ eq),
    w' := (hSq.fac (pushout_cocone.mk _ _ eq) (walking_span.left)).symm, },
  exact
  { left := φ₁,
    right := φ₂,
    w' := begin
      ext,
      { have h := arrow.congr_hom h₁,
        dsimp at ⊢ h,
        simp only [h, assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id], },
      { exact (hSq.fac (pushout_cocone.mk _ _ eq) (walking_span.right)).symm, },
    end },
end

lemma couniversal_uniq {Sq : square C} (hSq : Sq.is_cocartesian) (Sq' : square C)
  (h₁ : Sq.top = Sq'.top) (h₂ : Sq.left = Sq'.left) (φ : Sq ⟶ Sq')
  (h₃ : φ.left.left = eq_to_hom (arrow.congr_left h₂))
  (h₄ : φ.left.right = eq_to_hom (arrow.congr_right h₂))
  (h₅ : φ.right.left = eq_to_hom (arrow.congr_right h₁)) :
  φ = hSq.couniversal_lift Sq' h₁ h₂ :=
begin
  ext,
  { simp only [h₃, couniversal_lift_left_left], },
  { simp only [h₄, couniversal_lift_left_right], },
  { simp only [h₅, couniversal_lift_right_left], },
  { apply hSq.uniq (pushout_cocone.mk _ _ _) φ.right.right,
    rintro (_|_|_),
    { simp only [cocone_ι_app, assoc, pushout_cocone.mk_ι_app_zero, top_hom],
      have h := arrow.hom.congr_right φ.w,
      dsimp at h,
      erw [← h, h₄],
      have h' := arrow.congr_hom h₁,
      have h'' := arrow.congr_hom h₂,
      dsimp at h' h'',
      simp only [h', h'', assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp, arrow.w], },
    { simp only [cocone_ι_app, pushout_cocone.mk_ι_app_left],
      erw [← φ.right.w, h₅],
      refl, },
    { simp only [cocone_ι_app, pushout_cocone.mk_ι_app_right, bottom_hom],
      have h := arrow.hom.congr_right φ.w,
      dsimp at h,
      erw [← h, h₄],
      refl, } },
end

lemma endo_is_id {Sq : square C} (hSq : Sq.is_cocartesian) (φ : Sq ⟶ Sq)
  (h₁ : φ.left.left = 𝟙 _)
  (h₄ : φ.left.right = 𝟙 _)
  (h₅ : φ.right.left = 𝟙 _) :
  φ = 𝟙 _ :=
begin
  rw [hSq.couniversal_uniq Sq rfl rfl φ, hSq.couniversal_uniq Sq rfl rfl (𝟙 _)],
  all_goals { rw eq_to_hom_refl, try { refl, }, try { assumption }, },
end

def iso_pushout_square {Sq : square C} (hSq : Sq.is_cocartesian) :
  Sq ≅ @pushout_square _ _ _ _ _ Sq.top.hom Sq.left.hom (hSq.has_pushout) :=
begin
  haveI := hSq.has_pushout,
  let Sq' := pushout_square Sq.top.hom Sq.left.hom,
  let hSq' : Sq'.is_cocartesian := pushout_square_is_cocartesian _ _,
  exact
  { hom := hSq.couniversal_lift Sq' (by tidy) (by tidy),
    inv := hSq'.couniversal_lift Sq (by tidy) (by tidy),
    hom_inv_id' := begin
      apply hSq.endo_is_id,
      all_goals { dsimp, simpa only [comp_id], },
    end,
    inv_hom_id' := begin
      apply hSq'.endo_is_id,
      all_goals { dsimp, simp only [comp_id], },
    end, }
end

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
  apply square.is_cocartesian.unflip,
  exact big_square_is_pushout f₁ f₂ g₁ g₂ i₁ i₂ i₃ w₁₂.symm w₂₃.symm h₂₃.flip h₁₂.flip,
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

def right_square_is_cocartesian' (i₁ i₂ i₃ : arrow C) (sq₁₂ : i₁ ⟶ i₂) (sq₂₃ : i₂ ⟶ i₃)
  (h₁₂ : (square.mk sq₁₂).is_cocartesian) (h₁₃ : (square.mk (sq₁₂ ≫ sq₂₃)).is_cocartesian) :
  (square.mk sq₂₃).is_cocartesian :=
begin
  rcases i₁ with ⟨X₁, Y₁, i₁⟩,
  rcases i₂ with ⟨X₂, Y₂, i₂⟩,
  rcases i₃ with ⟨X₃, Y₃, i₃⟩,
  rcases sq₁₂ with ⟨f₁, g₁, w₁₂⟩,
  rcases sq₂₃ with ⟨f₂, g₂, w₂₃⟩,
  apply square.is_cocartesian.unflip,
  exact right_square_is_pushout f₁ f₂ g₁ g₂ i₁ i₂ i₃ w₁₂.symm w₂₃.symm h₁₂.flip h₁₃.flip,
end

def right_square_is_cocartesian (Sq₂ Sq₁ : square C) (e : Sq₁.right ≅ Sq₂.left)
  (h₁ : Sq₁.is_cocartesian) (h₁₂ : (Sq₁.horizontal_comp Sq₂ e).is_cocartesian) :
  Sq₂.is_cocartesian :=
begin
  convert right_square_is_cocartesian' _ _ _ (Sq₁.hom ≫ e.hom) Sq₂.hom _ _,
  { rw Sq₂.mk_eq, },
  { refine horizontal_comp_is_cocartesian _ _ _ Sq₁.hom e.hom _ _,
    { rw Sq₁.mk_eq,
      exact h₁, },
    { apply is_cocartesian_of_horizontal_is_iso,
      exact is_iso.of_iso e, }, },
  { have eq : mk ((Sq₁.hom ≫ e.hom) ≫ Sq₂.hom) = Sq₁.horizontal_comp Sq₂ e := by tidy,
    convert h₁₂, },
end

def is_cocartesian_of_top_comp (Sq₂ Sq₁ : square C) (e : Sq₁.bottom ≅ Sq₂.top)
  (h₁ : Sq₁.is_cocartesian) (h₁₂ : (Sq₁.vertical_comp Sq₂ e).is_cocartesian) :
  Sq₂.is_cocartesian :=
(right_square_is_cocartesian Sq₂.flip Sq₁.flip e h₁.flip h₁₂.flip).unflip

end square

end category_theory

