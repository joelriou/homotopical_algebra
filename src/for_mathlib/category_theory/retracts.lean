/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.opposites
import for_mathlib.category_theory.arrow
import for_mathlib.category_theory.comma_op
import category_theory.preadditive.projective
import for_mathlib.category_theory.morphism_property_misc

open category_theory
open category_theory.category
open opposite

variables {C D : Type*} [category C] [category D] (G : C ⥤ D)

namespace category_theory

def is_retract (X Y : C) : Prop := ∃ (s : X ⟶ Y) (r : Y ⟶ X), s ≫ r = 𝟙 X

namespace is_retract

def mk {X Y : C} (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X) : is_retract X Y := ⟨s, r, h⟩

lemma iff_op (X Y : C) : is_retract X Y ↔ is_retract (opposite.op X) (opposite.op Y) :=
begin
  split,
  { intro h,
    rcases h with ⟨s, r, fac⟩,
    use [r.op, s.op],
    exact congr_arg (λ (φ : _ ⟶ _), φ.op) fac, },
  { intro h,
    rcases h with ⟨s, r, fac⟩,
    use [r.unop, s.unop],
    exact congr_arg (λ (φ : _ ⟶ _), φ.unop) fac, },
end

lemma imp_of_isos {X Y X' Y' : C} (e₁ : X ≅ X') (e₂ : Y ≅ Y')
  (h : is_retract X Y) : is_retract X' Y' :=
begin
  rcases h with ⟨s, p, r⟩,
  use [e₁.inv ≫ s ≫ e₂.hom, e₂.inv ≫ p ≫ e₁.hom],
  slice_lhs 3 4 { rw iso.hom_inv_id, },
  erw id_comp,
  slice_lhs 2 3 { rw r, },
  erw [id_comp, iso.inv_hom_id],
end

lemma iff_of_isos {X Y X' Y' : C} (e₁ : X ≅ X') (e₂ : Y ≅ Y') :
  is_retract X Y ↔ is_retract X' Y' :=
begin
  split,
  { exact imp_of_isos e₁ e₂, },
  { exact imp_of_isos e₁.symm e₂.symm, },
end

lemma imp_of_functor (X Y : C) (h : is_retract X Y) : is_retract (G.obj X) (G.obj Y) :=
begin
  rcases h with ⟨s, p, r⟩,
  use [G.map s, G.map p],
  rw [← G.map_comp, r, G.map_id],
end

lemma iff_of_is_equivalence (X Y : C) [is_equivalence G] :
  is_retract X Y ↔ is_retract (G.obj X) (G.obj Y) :=
begin
  split,
  { apply imp_of_functor, },
  { intro h,
    have e : is_equivalence G := infer_instance,
    erw iff_of_isos (e.unit_iso.app X) (e.unit_iso.app Y),
    convert imp_of_functor e.inverse _ _ h, }
end

end is_retract

def is_retract_hom {X₁ X₂ Y₁ Y₂ : C} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) := is_retract (arrow.mk x) (arrow.mk y)

namespace is_retract_hom

lemma iff_op {X₁ X₂ Y₁ Y₂ : C} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) :
  is_retract_hom x y ↔ is_retract_hom x.op y.op :=
begin
  calc is_retract (arrow.mk x) (arrow.mk y) ↔ is_retract (op (arrow.mk x)) (op (arrow.mk y)) :
    is_retract.iff_op (arrow.mk x) (arrow.mk y)
  ... ↔ is_retract (arrow.mk x.op) (arrow.mk y.op) : _,
  rw is_retract.iff_of_is_equivalence (equivalence_arrow_op C).functor,
  congr',
end

lemma iff_unop {X₁ X₂ Y₁ Y₂ : Cᵒᵖ} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) :
  is_retract_hom x y ↔ is_retract_hom x.unop y.unop :=
(iff_op x.unop y.unop).symm

lemma op {X₁ X₂ Y₁ Y₂ : C} {x : X₁ ⟶ X₂} {y : Y₁ ⟶ Y₂}
  (hxy : is_retract_hom x y) : is_retract_hom x.op y.op :=
(iff_op x y).mp hxy

lemma unop {X₁ X₂ Y₁ Y₂ : Cᵒᵖ} {x : X₁ ⟶ X₂} {y : Y₁ ⟶ Y₂}
  (hxy : is_retract_hom x y) : is_retract_hom x.unop y.unop :=
(iff_op x.unop y.unop).mpr hxy

lemma imp_of_functor {X₁ X₂ Y₁ Y₂ : C} {x : X₁ ⟶ X₂} {y : Y₁ ⟶ Y₂} (h : is_retract_hom x y) :
  is_retract_hom (G.map x) (G.map y) :=
is_retract.imp_of_functor G.map_arrow _ _ h

end is_retract_hom

namespace morphism_property

variables (P : morphism_property C) {P' : morphism_property Cᵒᵖ}

def is_stable_by_retract : Prop :=
∀ ⦃X₁ X₂ Y₁ Y₂ : C⦄ (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂)
  (hxy : is_retract_hom x y) (hx : P y), P x

namespace is_stable_by_retract

variable {P}

lemma op (h : is_stable_by_retract P) :
  is_stable_by_retract P.op :=
λ X₁ X₂ Y₁ Y₂ x y hxy hy, h x.unop y.unop hxy.unop hy

lemma unop (h : is_stable_by_retract P') :
  is_stable_by_retract P'.unop :=
λ X₁ X₂ Y₁ Y₂ x y hxy hy, h x.op y.op hxy.op hy

variables (P P')

lemma iff_op : is_stable_by_retract P ↔ is_stable_by_retract P.op :=
begin
  split,
  { intro h,
    exact h.op, },
  { intro h,
    simpa only [P.unop_op] using h.unop, },
end

lemma iff_unop : is_stable_by_retract P' ↔ is_stable_by_retract P'.unop :=
(iff_op P'.unop).symm

lemma of_inter {P₁ P₂ : morphism_property C} (h₁ : P₁.is_stable_by_retract)
  (h₂ : P₂.is_stable_by_retract) : (P₁ ∩ P₂).is_stable_by_retract :=
λ X₁ X₂ Y₁ Y₂ x y hxy hy, ⟨h₁ x y hxy hy.1, h₂ x y hxy hy.2⟩

lemma for_isomorphisms : (isomorphisms C).is_stable_by_retract :=
λ X₁ X₂ Y₁ Y₂ x y hxy hy,
begin
  haveI : is_iso y := hy,
  rcases hxy with ⟨s, r, fac⟩,
  use s.right ≫ inv y ≫ r.left,
  have hs := s.w,
  have hr := r.w,
  have fac₁ := arrow.hom.congr_left fac,
  have fac₂ := arrow.hom.congr_right fac,
  dsimp at hs hr fac₁ fac₂ ⊢,
  split,
  { slice_lhs 1 2 { rw ← hs, },
    slice_lhs 2 3 { rw is_iso.hom_inv_id, },
    rw [id_comp, fac₁], },
  { slice_lhs 3 4 { rw hr, },
    slice_lhs 2 3 { rw is_iso.inv_hom_id, },
    rw [id_comp, fac₂], },
end

lemma for_monomorphisms : (monomorphisms C).is_stable_by_retract :=
λ X₁ X₂ Y₁ Y₂ x y hxy hy, ⟨λ Z g g' hgg', begin
  haveI : mono y := hy,
  rcases hxy with ⟨s, r, fac⟩,
  haveI : is_split_mono s.left := is_split_mono.mk' ⟨r.left, arrow.hom.congr_left fac⟩,
  have hs := s.w,
  dsimp at hs,
  rw [← cancel_mono s.left, ← cancel_mono y,
    assoc, assoc, hs, ← assoc, ← assoc, hgg'],
end⟩

lemma for_epimorphisms : (epimorphisms C).is_stable_by_retract :=
by simpa only [unop_monomorphisms] using (@for_monomorphisms Cᵒᵖ _).unop

lemma inverse_image {W : morphism_property D} (h : W.is_stable_by_retract) (F : C ⥤ D) :
  (W.inverse_image F).is_stable_by_retract := λ X₁ X₂ Y₁ Y₂ x y hxy hy,
h _ _ (is_retract_hom.imp_of_functor F hxy) hy

end is_stable_by_retract

end morphism_property

namespace projective

lemma of_retract {X Y : C} (hXY : is_retract X Y) (hY : projective Y) : projective X :=
⟨λ E Z f e, begin
  introI,
  rcases hXY with ⟨s, r, fac⟩,
  use s ≫ projective.factor_thru (r ≫ f) e,
  rw [assoc, factor_thru_comp, ← assoc, fac, id_comp],
end⟩

end projective

end category_theory
