/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.comma
import category_theory.arrow
import category_theory.opposites

open category_theory
open category_theory.category
open opposite

namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃
variables {A : Type u₁} [category.{v₁} A]
variables {B : Type u₂} [category.{v₂} B]
variables {T : Type u₃} [category.{v₃} T]

@[simps]
def functor_comma_op (L : A ⥤ T) (R : B ⥤ T) :
  comma L R ⥤ (comma R.op L.op)ᵒᵖ :=
{ obj := λ X, op
  { left := op X.right,
    right := op X.left,
    hom := X.hom.op, },
  map := λ X Y f, quiver.hom.op
  { left := f.right.op,
    right := f.left.op,
    w' := congr_arg (λ (φ : _ ⟶ _), φ.op) f.w'.symm, }, }

@[simps]
def functor_comma_unop (L : A ⥤ T) (R : B ⥤ T) :
  (comma R.op L.op)ᵒᵖ ⥤ comma L R :=
{ obj := λ X,
  { left := X.unop.right.unop,
    right := X.unop.left.unop,
    hom := X.unop.hom.unop, },
  map := λ X Y f,
  { left := f.unop.right.unop,
    right := f.unop.left.unop,
    w' := congr_arg (λ (φ : _ ⟶ _), φ.unop) f.unop.w'.symm, }, }

@[simps]
def equivalence_comma_op (L : A ⥤ T) (R : B ⥤ T) :
  comma L R ≌ (comma R.op L.op)ᵒᵖ :=
{ functor := functor_comma_op L R,
  inverse := functor_comma_unop L R,
  unit_iso := eq_to_iso begin
    apply functor.ext,
    { tidy, },
    { intro X, cases X, refl, }
  end,
  counit_iso := eq_to_iso begin
    suffices h : (functor_comma_unop L R ⋙ functor_comma_op L R).unop = 𝟭 _,
    { exact congr_arg functor.op h, },
    { apply functor.ext,
      { tidy, },
      { intro X, cases X, refl, }, },
  end,
  functor_unit_iso_comp' := begin
    intro X,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans],
  end }

variable (T)
@[simps]
def equivalence_arrow_op :
  arrow T ≌ (arrow Tᵒᵖ)ᵒᵖ := equivalence_comma_op (𝟭 T) (𝟭 T)

variable {T}

namespace arrow

lemma mk_eq (f : arrow T) : arrow.mk f.hom = f :=
by { cases f, dsimp [arrow.mk], refl, }

@[simp]
def op (f : arrow T) : arrow Tᵒᵖ := ((equivalence_arrow_op T).functor.obj f).unop
@[simp]
def unop (f : arrow Tᵒᵖ) : arrow T := (equivalence_arrow_op T).inverse.obj (opposite.op f)

lemma unop_op (f : arrow T) : f.op.unop = f := by { cases f, refl, }
lemma op_unop (f : arrow Tᵒᵖ) : f.unop.op = f := by { cases f, refl, }

def op_hom {f g : arrow T} (sq : f ⟶ g) : g.op ⟶ f.op :=
((equivalence_arrow_op T).functor.map sq).unop

def unop_hom' {f g : arrow Tᵒᵖ} (sq : f ⟶ g) : g.unop ⟶ f.unop :=
((equivalence_arrow_op T).inverse.map sq.op)

def unop_hom {f g : arrow T} (sq : f.op ⟶ g.op) : g ⟶ f :=
eq_to_hom g.unop_op.symm ≫ unop_hom' sq ≫ eq_to_hom f.unop_op

def op_unop_hom {f g : arrow T} (sq : f.op ⟶ g.op) : sq = op_hom (unop_hom sq) :=
begin
  cases f,
  cases g,
  cases sq,
  dsimp only [unop_hom],
  erw [id_comp, comp_id],
  congr,
end

end arrow

end category_theory