/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.opposites

open category_theory
open category_theory.category
open opposite

variables {C : Type*} [category C]

namespace category_theory

def is_retract (X Y : C) : Prop := ∃ (s : X ⟶ Y) (r : Y ⟶ X), s ≫ r = 𝟙 X

def is_retract_iff_op (X Y : C) : is_retract X Y ↔ is_retract (opposite.op X) (opposite.op Y) :=
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

def is_retract_imp_of_isos {X Y X' Y' : C} (e₁ : X ≅ X') (e₂ : Y ≅ Y')
  (h : is_retract X Y) : is_retract X' Y' :=
begin
  rcases h with ⟨s, p, r⟩,
  use [e₁.inv ≫ s ≫ e₂.hom, e₂.inv ≫ p ≫ e₁.hom],
  slice_lhs 3 4 { rw iso.hom_inv_id, },
  erw id_comp,
  slice_lhs 2 3 { rw r, },
  erw [id_comp, iso.inv_hom_id],
end

def is_retract_iff_of_isos {X Y X' Y' : C} (e₁ : X ≅ X') (e₂ : Y ≅ Y') :
  is_retract X Y ↔ is_retract X' Y' :=
begin
  split,
  { exact is_retract_imp_of_isos e₁ e₂, },
  { exact is_retract_imp_of_isos e₁.symm e₂.symm, },
end

variables {D : Type*} [category D] (F : C ⥤ D)

def is_retract_imp_of_functor (X Y : C) (h : is_retract X Y) : is_retract (F.obj X) (F.obj Y) :=
begin
  rcases h with ⟨s, p, r⟩,
  use [F.map s, F.map p],
  rw [← F.map_comp, r, F.map_id],
end

def is_retract_iff_of_is_equivalence (X Y : C) [is_equivalence F] :
  is_retract X Y ↔ is_retract (F.obj X) (F.obj Y) :=
begin
  split,
  { apply is_retract_imp_of_functor, },
  { intro h,
    have e : is_equivalence F := infer_instance,
    erw is_retract_iff_of_isos (e.unit_iso.app X) (e.unit_iso.app Y),
    convert is_retract_imp_of_functor e.inverse _ _ h, }
end

end category_theory
