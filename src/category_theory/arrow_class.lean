/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.isomorphism
import category_theory.limits.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.pullbacks
import category_theory.arrow

open category_theory
open category_theory.limits
open opposite

variables (C : Type*) [category C]


namespace category_theory

abbreviation arrow_class := set (arrow C)

namespace arrow_class

variables {C}
variables (F : arrow_class C) (F' : arrow_class Cᵒᵖ)

def isomorphisms : arrow_class C := λ f, is_iso f.hom

#exit
def arrow_eq_op : arrow C ≌ (arrow Cᵒᵖ)ᵒᵖ :=
{ functor :=
  { obj := λ f, opposite.op (arrow.mk f.hom.op),
    map := λ f g φ, begin
      apply λ (ψ : _ ⟶ _), ψ.op,
      apply arrow.hom_mk',
      symmetry,
      convert congr_arg (λ (ψ : _ ⟶ _), ψ.op) φ.w',
      sorry,
    end,
  },
  inverse := sorry,
  unit_iso := sorry,
  counit_iso := sorry }

#exit
@[simp] def unop : arrow_class C := λ f, begin
  have foo := equivalence.op
  sorry
end

--@[simp] def op : hom_class Cᵒᵖ := λ f, F f.unop
#exit
lemma unop_op : F.op.unop = F := by refl
lemma op_unop : F'.unop.op = F' := by refl

def contains_isomorphisms := ∀ (X Y : C) (f : X ⟶ Y), is_iso f → F.contains f

lemma contains_isomorphismsm_iff_op : F.contains_isomorphisms ↔ F.op.contains_isomorphisms :=
begin
  split,
  { intros hF X Y f,
    introI,
    apply hF,
    apply_instance, },
  { intros hF X Y f,
    introI,
    apply hF _ _ f.op,
    apply_instance, }
end

def is_stable_by_composition :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    F.contains f → F.contains g → F.contains (f ≫ g)

lemma stability_by_composition [hF : F.is_stable_by_composition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.contains f → F.contains g → F.contains (f ≫ g) := hF _ _ _ _ _

lemma is_stable_by_composition_iff_op : F.is_stable_by_composition ↔ F.op.is_stable_by_composition :=
begin
  split,
  { intros hF X Y Z f g hf hg,
    exact hF _ _ _ g.unop f.unop hg hf, },
  { intros hF X Y Z f g hf hg,
    exact hF _ _ _ g.op f.op hg hf, }
end

def three_of_two1 :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    F.contains (f ≫ g) → F.contains g → F.contains f
    
def three_of_two2 :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    F.contains (f ≫ g) → F.contains f → F.contains g

lemma three_of_two1_iff_op : F.three_of_two1 ↔ F.op.three_of_two2 :=
begin
  split,
  { intros hF X Y Z f g hfg hf,
    exact hF _ _ _ g.unop f.unop hfg hf, },
  { intros hF X Y Z f g hfg hg,
    exact hF _ _ _ g.op f.op hfg hg, }
end

lemma three_of_two2_iff_op : F.three_of_two2 ↔ F.op.three_of_two1 :=
begin
  split,
  { intros hF X Y Z f g hfg hg,
    exact hF _ _ _ g.unop f.unop hfg hg, },
  { intros hF X Y Z f g hfg hf,
    exact hF _ _ _ g.op f.op hfg hf, }
end

def three_of_two := is_stable_by_composition F ∧ three_of_two1 F ∧ three_of_two2 F

lemma three_of_two_iff_op : F.three_of_two ↔ F.op.three_of_two :=
begin
  dsimp only [three_of_two],
  rw [← is_stable_by_composition_iff_op, ← three_of_two1_iff_op, ← three_of_two2_iff_op],
  finish,
end

def is_stable_by_base_change [has_pullbacks C] :=
  ∀ (X Y Y' : C) (f : X ⟶ Y) (g : Y' ⟶ Y), F.contains f → F.contains (pullback.snd : pullback f g ⟶ Y')

def is_stable_by_cobase_change [has_pushouts C] :=
  ∀ (X X' Y : C) (f : X ⟶ Y) (g : X ⟶ X'), F.contains f → F.contains (pushout.inr : X' ⟶ pushout f g)

end hom_class

end category_theory
