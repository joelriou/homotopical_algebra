/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.factorisation_axiom

open category_theory

variables {C : Type*} [category C] (F : morphism_property C) {F' : morphism_property Cᵒᵖ}

namespace category_theory

namespace morphism_property

def three_of_two_of_comp_left : Prop :=
∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (hf : F f) (hfg : F (f ≫ g)), F g

def three_of_two_of_comp_right : Prop :=
∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (hg : F g) (hfg : F (f ≫ g)), F f

namespace three_of_two_of_comp_left

variable {F}

lemma inverse_image {D : Type*} [category D] (h : F.three_of_two_of_comp_left) (G : D ⥤ C) :
  (F.inverse_image G).three_of_two_of_comp_left := λ X Y Z f g hf hfg,
begin
  dsimp [morphism_property.inverse_image] at hf hfg ⊢,
  rw G.map_comp at hfg,
  exact h _ _ hf hfg,
end

lemma op (h : F.three_of_two_of_comp_left) : F.op.three_of_two_of_comp_right :=
λ X Y Z f g hg hgf, h g.unop f.unop hg hgf

lemma unop (h : F'.three_of_two_of_comp_left) : F'.unop.three_of_two_of_comp_right :=
λ X Y Z f g hg hgf, h g.op f.op hg hgf

end three_of_two_of_comp_left

namespace three_of_two_of_comp_right

variable {F}

lemma inverse_image {D : Type*} [category D] (h : F.three_of_two_of_comp_right) (G : D ⥤ C) :
  (F.inverse_image G).three_of_two_of_comp_right := λ X Y Z f g hg hfg,
begin
  dsimp [morphism_property.inverse_image] at hg hfg ⊢,
  rw G.map_comp at hfg,
  exact h _ _ hg hfg,
end

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

structure three_of_two : Prop :=
(of_comp : F.stable_under_composition)
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

variable {F}

lemma for_inverse_image {D : Type*} [category D] (h : three_of_two F) (G : D ⥤ C) :
  (F.inverse_image G).three_of_two :=
{ of_comp := h.of_comp.inverse_image G,
  of_comp_left := h.of_comp_left.inverse_image G,
  of_comp_right := h.of_comp_right.inverse_image G, }

variable (C)

lemma for_isomorphisms : (isomorphisms C).three_of_two :=
{ of_comp := stable_under_composition.for_isomorphisms C,
  of_comp_left := λ X Y Z f g hf hfg, begin
    dsimp [isomorphisms] at hf hfg ⊢,
    haveI := hf,
    haveI := hfg,
    exact is_iso.of_is_iso_comp_left f g,
  end,
  of_comp_right :=λ X Y Z f g hg hfg, begin
    dsimp [isomorphisms] at hg hfg ⊢,
    haveI := hg,
    haveI := hfg,
    exact is_iso.of_is_iso_comp_right f g,
  end, }

end three_of_two

end morphism_property

end category_theory
