/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.opposites
import category_theory.arrow
import for_mathlib.category_theory.comma_op

open category_theory
open category_theory.category
open opposite

variables {C D : Type*} [category C] [category D] (F : C ⥤ D)

namespace category_theory

def is_retract (X Y : C) : Prop := ∃ (s : X ⟶ Y) (r : Y ⟶ X), s ≫ r = 𝟙 X

namespace is_retract

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

lemma imp_of_functor (X Y : C) (h : is_retract X Y) : is_retract (F.obj X) (F.obj Y) :=
begin
  rcases h with ⟨s, p, r⟩,
  use [F.map s, F.map p],
  rw [← F.map_comp, r, F.map_id],
end

lemma iff_of_is_equivalence (X Y : C) [is_equivalence F] :
  is_retract X Y ↔ is_retract (F.obj X) (F.obj Y) :=
begin
  split,
  { apply imp_of_functor, },
  { intro h,
    have e : is_equivalence F := infer_instance,
    erw iff_of_isos (e.unit_iso.app X) (e.unit_iso.app Y),
    convert imp_of_functor e.inverse _ _ h, }
end

end is_retract

def is_retract_hom {X₁ X₂ Y₁ Y₂ : C} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) := is_retract (arrow.mk x) (arrow.mk y) 

namespace is_retract_hom

def iff_op {X₁ X₂ Y₁ Y₂ : C} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) :
  is_retract_hom x y ↔ is_retract_hom x.op y.op :=
begin
  calc is_retract (arrow.mk x) (arrow.mk y) ↔ is_retract (op (arrow.mk x)) (op (arrow.mk y)) :
    is_retract.iff_op (arrow.mk x) (arrow.mk y)
  ... ↔ is_retract (arrow.mk x.op) (arrow.mk y.op) : _,
  rw is_retract.iff_of_is_equivalence (equivalence_arrow_op C).functor,
  congr',
end

def iff_unop {X₁ X₂ Y₁ Y₂ : Cᵒᵖ} (x : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) :
  is_retract_hom x y ↔ is_retract_hom x.unop y.unop :=
(iff_op x.unop y.unop).symm

def op {X₁ X₂ Y₁ Y₂ : C} {x : X₁ ⟶ X₂} {y : Y₁ ⟶ Y₂}
  (hxy : is_retract_hom x y) : is_retract_hom x.op y.op :=
(iff_op x y).mp hxy

def unop {X₁ X₂ Y₁ Y₂ : Cᵒᵖ} {x : X₁ ⟶ X₂} {y : Y₁ ⟶ Y₂}
  (hxy : is_retract_hom x y) : is_retract_hom x.unop y.unop :=
(iff_op x.unop y.unop).mpr hxy

end is_retract_hom

end category_theory
