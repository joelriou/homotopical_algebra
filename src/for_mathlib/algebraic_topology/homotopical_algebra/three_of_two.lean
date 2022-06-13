/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.factorisation_axiom

open category_theory category_theory.limits

variables {C : Type*} [category C] (F : arrow_class C) {F' : arrow_class Cᵒᵖ}

namespace category_theory

namespace arrow_class

def three_of_two_of_comp_left : Prop :=
∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z), arrow.mk f ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk g ∈ F

def three_of_two_of_comp_right : Prop :=
∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z), arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk f ∈ F

namespace three_of_two_of_comp_left

variable {F}

lemma op (h : F.three_of_two_of_comp_left) : F.op.three_of_two_of_comp_right :=
λ X Y Z f g hg hgf, h g.unop f.unop hg hgf

lemma unop (h : F'.three_of_two_of_comp_left) : F'.unop.three_of_two_of_comp_right :=
λ X Y Z f g hg hgf, h g.op f.op hg hgf

variable (F)

end three_of_two_of_comp_left

namespace three_of_two_of_comp_right

variable {F}

lemma op (h : F.three_of_two_of_comp_right) : F.op.three_of_two_of_comp_left :=
λ X Y Z f g hg hgf, h g.unop f.unop hg hgf

lemma unop (h : F'.three_of_two_of_comp_right) : F'.unop.three_of_two_of_comp_left :=
λ X Y Z f g hg hgf, h g.op f.op hg hgf

variables (F F')

lemma iff_op : F.three_of_two_of_comp_right ↔ F.op.three_of_two_of_comp_left :=
⟨op, three_of_two_of_comp_left.unop⟩

lemma iff_unop : F'.three_of_two_of_comp_right ↔ F'.unop.three_of_two_of_comp_left :=
⟨unop, three_of_two_of_comp_left.op⟩

end three_of_two_of_comp_right

namespace three_of_two_of_comp_left

lemma iff_op : F.three_of_two_of_comp_left ↔ F.op.three_of_two_of_comp_right :=
⟨op, three_of_two_of_comp_right.unop⟩

lemma iff_unop : F'.three_of_two_of_comp_left ↔ F'.unop.three_of_two_of_comp_right :=
⟨unop, three_of_two_of_comp_right.op⟩

end three_of_two_of_comp_left


variable (F)

structure three_of_two (F : arrow_class C) : Prop :=
  (of_comp : F.is_stable_by_composition)
  (of_comp_left : F.three_of_two_of_comp_left)
  (of_comp_right : F.three_of_two_of_comp_right)

namespace three_of_two

variables {F F'}

lemma op (h : three_of_two F) : three_of_two F.op :=
{ of_comp := h.of_comp.op,
  of_comp_left := h.of_comp_right.op,
  of_comp_right := h.of_comp_left.op, }

lemma unop (h : three_of_two F') : three_of_two F'.unop :=
{ of_comp := h.of_comp.unop,
  of_comp_left := h.of_comp_right.unop,
  of_comp_right := h.of_comp_left.unop, }

variables (F F')

lemma iff_op : F.three_of_two ↔ F.op.three_of_two :=
⟨op, λ h, by simpa only [F.unop_op] using h.unop⟩

lemma iff_unop : F'.three_of_two ↔ F'.unop.three_of_two :=
⟨unop, λ h, by simpa only [F'.op_unop] using h.op⟩

end three_of_two

end arrow_class

end category_theory
