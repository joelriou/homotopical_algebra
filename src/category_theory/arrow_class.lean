/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.isomorphism
import category_theory.limits.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.pullbacks
import category_theory.comma_op

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

def mem_isomorphisms_iff {X Y : C} (f : X ⟶ Y) : arrow.mk f ∈ (isomorphisms : arrow_class C) ↔ is_iso f :=
by refl

def op : arrow_class Cᵒᵖ := λ f, f.unop ∈ F
def unop : arrow_class C := λ f, f.op ∈ F'

lemma unop_op : F.op.unop = F :=
by { ext f, conv_rhs { rw ← arrow.unop_op f, }, refl, }
lemma op_unop : F'.unop.op = F' :=
by { ext f, conv_rhs { rw ← arrow.op_unop f, }, refl, }

@[simp]
lemma mem_op_iff (f : arrow Cᵒᵖ) : f ∈ F.op ↔ f.unop ∈ F := by refl

@[simp]
lemma unop_mem_iff (f : arrow C) : f ∈ F'.unop ↔ f.op ∈ F' := by refl

lemma subset_iff_op (G : arrow_class C) : F ⊆ G ↔ F.op ⊆ G.op :=
begin
  split,
  { intros h f hf,
    exact h hf, },
  { intros h f hf,
    rw ← f.unop_op at hf ⊢,
    exact h hf, }
end

lemma op_isomorphisms_eq : (isomorphisms : arrow_class C).op = isomorphisms :=
by { ext f, exact is_iso_unop_iff f.hom, }

lemma isomorphisms_subset_iff_op : isomorphisms ⊆ F ↔ isomorphisms ⊆ F.op :=
begin
  rw subset_iff_op isomorphisms F,
  convert iff.rfl,
  rw op_isomorphisms_eq,
end

def is_stable_by_composition : Prop :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F

lemma is_stable_by_composition_iff_op : F.is_stable_by_composition ↔ F.op.is_stable_by_composition :=
begin
  split,
  { intros hF X Y Z f g hf hg,
    rw mem_op_iff at hf hg ⊢,
    exact hF _ _ _ g.unop f.unop hg hf, },
  { intros hF X Y Z f g hf hg,
    rw ← (arrow.mk _).unop_op at ⊢ hf hg,
    rw ← mem_op_iff at hf hg ⊢,
    exact hF _ _ _  g.op f.op hg hf, }
end

lemma iso_comp_stable: (isomorphisms : arrow_class C).is_stable_by_composition :=
begin
  intros X Y Z f g hf hg,
  rw mem_isomorphisms_iff at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply_instance,
end

#exit


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
