/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.isomorphism
import category_theory.limits.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits
open opposite

variables (C : Type*) [category C]

abbreviation hom_class := Π (X Y : C), set (X ⟶ Y)

namespace hom_class

variables {C}
variables (F : hom_class C) (F' : hom_class Cᵒᵖ)

def isomorphisms : hom_class C := λ X Y f, is_iso f

def unop : hom_class C := λ X Y f, F' (op Y) (op X) f.op
def op : hom_class Cᵒᵖ := λ X Y f, F Y.unop X.unop f.unop

lemma unop_op : F.op.unop = F := by refl
lemma op_unop : F'.unop.op = F' := by refl

def contains_isomorphisms := ∀ (X Y : C) (f : X ⟶ Y), is_iso f → f ∈ F X Y

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
    f ∈ F X Y → g ∈ F Y Z → (f ≫ g) ∈ F X Z

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
    (f ≫ g) ∈ F X Z → g ∈ F Y Z → f ∈ F X Y

def three_of_two2 :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    (f ≫ g) ∈ F X Z → f ∈ F X Y → g ∈ F Y Z

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
  ∀ (X Y Y' : C) (f : X ⟶ Y) (g : Y' ⟶ Y), f ∈ F X Y → pullback.snd ∈ F (pullback f g) Y'

def is_stable_by_cobase_change [has_pushouts C] :=
  ∀ (X X' Y : C) (f : X ⟶ Y) (g : X ⟶ X'), f ∈ F X Y → pushout.inr ∈ F X' (pushout f g)


end hom_class

