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
import category_theory.epi_mono
import category_theory.retracts
import category_theory.cartesian_square

open category_theory
open category_theory.limits
open opposite

namespace category_theory

variables (C : Type*) [category C]

abbreviation arrow_class := set (arrow C)

variables {C}

namespace arrow

def is_retract_iff_op (f : arrow C) (f' : arrow C) :
  is_retract f f' ↔ is_retract f.op f'.op :=
begin
  let e := equivalence_arrow_op C,
  haveI := is_equivalence.of_equivalence e,
  have eq₁ := is_retract_iff_op f.op f'.op,
  have eq₂ := is_retract_iff_of_is_equivalence e.functor f f',
  exact eq₂.trans eq₁.symm,
end

def is_retract_iff_unop (f : arrow Cᵒᵖ) (f' : arrow Cᵒᵖ) :
  is_retract f f' ↔ is_retract f.unop f'.unop :=
begin
  have eq₁ := is_retract_iff_of_isos (eq_to_iso f.op_unop.symm) (eq_to_iso f'.op_unop.symm),
  have eq₂ := is_retract_iff_op f.unop f'.unop,
  exact eq₁.trans eq₂.symm,    
end

lemma op_mk {T : Type*} [category T] {X Y : T} (f : X ⟶ Y) : (arrow.mk f).op = arrow.mk f.op := by refl

lemma unop_mk {T : Type*} [category T] {X Y : Tᵒᵖ} (f : X ⟶ Y) :
  (arrow.mk f).unop = arrow.mk f.unop := by refl

end arrow

namespace arrow_class

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

lemma op_inj {f g : arrow_class C} (h : f.op = g.op) : f = g :=
by rw [← unop_op f, ← unop_op g, h]

lemma unop_inj {f g : arrow_class Cᵒᵖ} (h : f.unop = g.unop) : f = g :=
by rw [← op_unop f, ← op_unop g, h]

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

def is_stable_by_retract (F : arrow_class C) : Prop := ∀ (f f' : arrow C),
  f' ∈ F → is_retract f f' → f ∈ F

lemma is_stable_by_retract_iff_op (F : arrow_class C) :
  is_stable_by_retract F ↔ is_stable_by_retract F.op :=
begin
  split,
  { intros h f f' hf' hff',
    rw mem_op_iff at ⊢ hf',
    apply h f.unop f'.unop hf',
    rw ← arrow.is_retract_iff_unop,
    exact hff', },
  { intros h f f' hf hff',
    rw [← arrow.unop_op f,← mem_op_iff],
    rw ← arrow.unop_op f' at hf,
    apply h f.op f'.op hf,
    rw ← arrow.is_retract_iff_op,
    exact hff', }
end

namespace is_stable_by_retract

def op {F : arrow_class C} := (is_stable_by_retract_iff_op F).mp
def unop {F : arrow_class C} := (is_stable_by_retract_iff_op F).mpr

def of_intersection (F G : arrow_class C)
  (hF : F.is_stable_by_retract) (hG : G.is_stable_by_retract) :
  (F ∩ G).is_stable_by_retract :=
begin
  rintros f f' ⟨h₁, h₂⟩ hff',
  split,
  { exact hF f f' h₁ hff', },
  { exact hG f f' h₂ hff', },
end

end is_stable_by_retract

def three_of_two_of_comp_left (F : arrow_class C) : Prop :=
∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk g ∈ F

def three_of_two_of_comp_right (F : arrow_class C) : Prop :=
∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk f ∈ F

structure three_of_two (F : arrow_class C) : Prop :=
  (of_comp : F.is_stable_by_composition)
  (of_comp_left : F.three_of_two_of_comp_left)
  (of_comp_right : F.three_of_two_of_comp_right)

lemma three_of_two_of_comp_left_iff_op : F.three_of_two_of_comp_left ↔ F.op.three_of_two_of_comp_right :=
begin
  split,
  { intros hF X Y Z f g hfg hf,
    exact hF g.unop f.unop hfg hf, },
  { intros hF X Y Z f g hfg hg,
    exact hF g.op f.op hfg hg, }
end

lemma three_of_two_of_comp_right_iff_op : F.three_of_two_of_comp_right ↔ F.op.three_of_two_of_comp_left :=
begin
  split,
  { intros hF X Y Z f g hfg hg,
    exact hF g.unop f.unop hfg hg, },
  { intros hF X Y Z f g hfg hf,
    exact hF g.op f.op hfg hf, }
end

lemma three_of_two_iff (F : arrow_class C) : F.three_of_two ↔
F.is_stable_by_composition ∧ F.three_of_two_of_comp_left ∧ F.three_of_two_of_comp_right :=
begin
  split,
  { intro h,
    cases h,
    finish, },
  { rintro ⟨h₁, h₂, h₃⟩,
    dsimp [three_of_two_of_comp_left] at h₂,
    exact {
      of_comp := h₁,
      of_comp_left := λ _ _ _ , h₂,
      of_comp_right := λ _ _ _ , h₃, } }
end

lemma three_of_two_iff_op : F.three_of_two ↔ F.op.three_of_two :=
begin
  simp only [three_of_two_iff],
  rw [← is_stable_by_composition_iff_op, ← three_of_two_of_comp_left_iff_op,
    ← three_of_two_of_comp_right_iff_op],
  finish,
end

def is_stable_by_base_change :=
  ∀ {f' f : arrow C} (sq : f' ⟶ f) (hsq : is_cartesian sq), f ∈ F → f' ∈ F

def is_stable_by_cobase_change :=
  ∀ {f f' : arrow C} (sq : f ⟶ f') (hsq : is_cocartesian sq), f ∈ F → f' ∈ F

namespace is_stable_by_cobase_change

lemma for_pushout_inl (hF : F.is_stable_by_cobase_change)
  {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) (hf₂ : arrow.mk f₂ ∈ F) [has_pushout f₁ f₂] :
  arrow.mk (pushout.inl : A₁ ⟶ pushout f₁ f₂) ∈ F :=
hF _ (pushout_square_is_cocartesian f₁ f₂) hf₂

lemma for_pushout_inr (hF : F.is_stable_by_cobase_change)
  {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (hf₁ : arrow.mk f₁ ∈ F) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  arrow.mk (pushout.inr : A₂ ⟶ pushout f₁ f₂) ∈ F :=
hF _ (pushout_square'_is_cocartesian f₁ f₂) hf₁

end is_stable_by_cobase_change


def factorisation_axiom (F G : arrow_class C) :=
∀ (f : arrow C), ∃ (Z : C) (i : f.left ⟶ Z) (p : Z ⟶ f.right) (fac : f.hom = i ≫ p),
arrow.mk i ∈ F ∧ arrow.mk p ∈ G

lemma factorisation_axiom_iff_op (F G : arrow_class C) :
  factorisation_axiom F G ↔ factorisation_axiom G.op F.op :=
begin
  split,
  { intros h f,
    rcases h f.unop with ⟨Z, i, p, fac, ⟨r₁, r₂⟩⟩,
    use [opposite.op Z, p.op, i.op],
    split,
    { exact quiver.hom.unop_inj fac, },
    { simp only [mem_op_iff, arrow.unop_mk],
      exact ⟨r₂, r₁⟩, }, },
  { intros h f,
    rcases h f.op with ⟨Z, i, p, fac, ⟨r₁, r₂⟩⟩,
    use [opposite.unop Z, p.unop, i.unop],
    split,
    { exact quiver.hom.op_inj fac, },
    { simp only [mem_op_iff, arrow.unop_mk] at r₁ r₂,
      exact ⟨r₂, r₁⟩, }, },
end

namespace factorisation_axiom

def op {F G : arrow_class C} := (factorisation_axiom_iff_op F G).mp
def unop {F G : arrow_class C} := (factorisation_axiom_iff_op F G).mpr

end factorisation_axiom

end arrow_class

end category_theory
