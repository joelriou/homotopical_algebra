/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow
import for_mathlib.category_theory.arrow
import for_mathlib.category_theory.comma_op
import for_mathlib.category_theory.comm_sq

/-!

# Classes of arrows in a category

If `C` is a category, an `arrow_class C` is a class of arrows in C. It is
implemented here as `set (arrow C)`.

If `W : arrow_class C`, and `f : X ⟶ Y` is a morphism in `C`, `W f` is the
condition that `arrow.mk f` belongs to `W`.

-/

open category_theory
open category_theory.limits category_theory.category

noncomputable theory

universe v

namespace category_theory

variables (C : Type*) [category.{v} C] {D : Type*} [category D]

/-- An `arrow_class C` is a class of arrows in a category `C`. -/
abbreviation arrow_class := set (arrow C)

variable {C}

namespace arrow_class

/-- If `W : arrow_class C` and `F : C ⥤ D` is a functor, then `W.is_inverted_by F`
means that all morphisms in `W` are sent to isomorphisms in `D`. -/
def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : W), f.val.is_inverted_by F

variables (F : arrow_class C) (F' : arrow_class Cᵒᵖ)

def op : arrow_class Cᵒᵖ := λ f, f.unop ∈ F
def unop : arrow_class C := λ f, f.op ∈ F'

lemma mem_op_iff (f : arrow Cᵒᵖ) : f ∈ F.op ↔ f.unop ∈ F := by refl
lemma mem_unop_iff (f : arrow C) : f ∈ F'.unop ↔ f.op ∈ F' := by refl

lemma unop_op : F.op.unop = F :=
begin
  ext f,
  split;
  { intro h,
    simpa only [mem_unop_iff, mem_op_iff, arrow.unop_op] using h, },
end

lemma op_unop : F'.unop.op = F' :=
begin
  ext f,
  split;
  { intro h,
    simpa only [mem_unop_iff, mem_op_iff, arrow.op_unop] using h, },
end

def is_stable_by_composition : Prop :=
∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F

namespace is_stable_by_composition

variables {F F'}

lemma op (h : is_stable_by_composition F) :
  is_stable_by_composition F.op :=
λ X Y Z f g hf hg, h g.unop f.unop hg hf

lemma unop (h : is_stable_by_composition F') :
  is_stable_by_composition F'.unop :=
λ X Y Z f g hf hg, h g.op f.op hg hf

variables (F F')

lemma iff_op :
  is_stable_by_composition F ↔ is_stable_by_composition F.op :=
begin
  split,
  { intro h,
    exact h.op, },
  { intro h,
    simpa only [F.unop_op] using h.unop, },
end

lemma iff_unop :
  is_stable_by_composition F' ↔ is_stable_by_composition F'.unop :=
by simpa only [F'.op_unop] using (iff_op F'.unop).symm

end is_stable_by_composition

def inverse_image (G : D ⥤ C) : arrow_class D :=
λ w, G.map_arrow.obj w ∈ F

def isomorphisms : arrow_class C := λ f, is_iso f.hom
def monomorphisms : arrow_class C := λ f, mono f.hom
def epimorphisms : arrow_class C := λ f, epi f.hom

lemma mem_isomorphisms_of_is_iso {X Y : C} (f : X ⟶ Y) [hf : is_iso f] :
  arrow.mk f ∈ (isomorphisms : arrow_class C) := hf
lemma mem_monomorphisms_of_mono {X Y : C} (f : X ⟶ Y) [hf : mono f] :
  arrow.mk f ∈ (monomorphisms : arrow_class C) := hf
lemma mem_epimorphisms_of_epi {X Y : C} (f : X ⟶ Y) [hf : epi f] :
  arrow.mk f ∈ (epimorphisms : arrow_class C) := hf

lemma epimorphisms_eq_op : (epimorphisms : arrow_class C) = (monomorphisms : arrow_class Cᵒᵖ).unop :=
begin
  ext f,
  rcases f with ⟨X, Y, f⟩,
  dsimp at X Y f,
  split,
  { intro hf,
    haveI : epi f := hf,
    exact category_theory.op_mono_of_epi f, },
  { intro hf,
    haveI : mono f.op := hf,
    exact category_theory.unop_epi_of_mono f.op, },
end

lemma monomorphisms_eq_op : (monomorphisms : arrow_class C) = (epimorphisms : arrow_class Cᵒᵖ).unop :=
begin
  ext f,
  rcases f with ⟨X, Y, f⟩,
  dsimp at X Y f,
  split,
  { intro hf,
    haveI : mono f := hf,
    exact category_theory.op_epi_of_mono f, },
  { intro hf,
    haveI : epi f.op := hf,
    exact category_theory.unop_mono_of_epi f.op, },
end

def is_stable_by_direct_image :=
∀ ⦃A B X Y : C⦄ ⦃f : A ⟶ X⦄ ⦃i : A ⟶ B⦄ ⦃p : X ⟶ Y⦄ ⦃g : B ⟶ Y⦄
(sq : is_pushout f i p g) (hi : arrow.mk i ∈ F), arrow.mk p ∈ F

namespace is_stable_by_direct_image

variable {F}

lemma for_coprod_inl (h : is_stable_by_direct_image F) (A B : C)
  [has_binary_coproduct A B] [has_initial C] (hB : arrow.mk (initial.to B) ∈ F) :
  arrow.mk (coprod.inl : A ⟶ A ⨿ B) ∈ F :=
h (is_pushout.of_has_binary_coproduct A B) hB

lemma for_coprod_inr (h : is_stable_by_direct_image F) (A B : C)
  [has_binary_coproduct A B] [has_initial C] (hA : arrow.mk (initial.to A) ∈ F) :
  arrow.mk (coprod.inr : B ⟶ A ⨿ B) ∈ F :=
h (is_pushout.of_has_binary_coproduct A B).flip hA

lemma for_pushout_inl (h : is_stable_by_direct_image F) {A B₁ B₂ : C} (f : A ⟶ B₁) (g : A ⟶ B₂)
  [has_pushout f g] (hg : arrow.mk g ∈ F) :
  arrow.mk (pushout.inl : B₁ ⟶ pushout f g) ∈ F :=
h (is_pushout.of_has_pushout f g) hg

lemma for_pushout_inr (h : is_stable_by_direct_image F) {A B₁ B₂ : C} (f : A ⟶ B₁) (g : A ⟶ B₂)
  [has_pushout f g] (hf : arrow.mk f ∈ F) :
  arrow.mk (pushout.inr : B₂ ⟶ pushout f g) ∈ F :=
h (is_pushout.of_has_pushout f g).flip hf

end is_stable_by_direct_image

def is_stable_by_coproduct :=
∀ ⦃I : Type v⦄ (X Y : I → C) [hX : has_coproduct X] [hY : has_coproduct Y]
  (f : Π i, X i ⟶ Y i) (hf : ∀ i, arrow.mk (f i) ∈ F),
    arrow.mk (@limits.sigma.map _ _ _ X Y hX hY f) ∈ F

namespace is_stable_by_coproduct

variable {F}

lemma binary {F : arrow_class C} (h : F.is_stable_by_coproduct)
{X₁ X₂ Y₁ Y₂ : C} [hX : has_binary_coproduct X₁ X₂] [hY : has_binary_coproduct Y₁ Y₂] (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
(hf₁ : arrow.mk f₁ ∈ F) (hf₂ : arrow.mk f₂ ∈ F) : arrow.mk (coprod.map f₁ f₂) ∈ F :=
begin
  haveI : has_coproduct (pair_function X₁ X₂) := hX,
  haveI : has_coproduct (pair_function Y₁ Y₂) := hY,
  dsimp [coprod.map],
  convert h (pair_function X₁ X₂) (pair_function Y₁ Y₂) (λ j, walking_pair.cases_on j f₁ f₂) _,
  { ext, cases x, refl, },
  { rintro (_|_), exacts [hf₁, hf₂], },
end

end is_stable_by_coproduct

def is_iso_invariant := ∀ ⦃w w' : arrow C⦄ (e : w ≅ w') (hw : w ∈ F), w' ∈ F

namespace is_iso_invariant

variable {F}

lemma iff (h : is_iso_invariant F) {w w' : arrow C} (e : w ≅ w') : w ∈ F ↔ w' ∈ F :=
begin
  split,
  exacts [λ hw, h e hw, λ hw', h e.symm hw'],
end

variable (F)

lemma of_comp_stable_and_contains_iso (h₁ : is_stable_by_composition F) (h₂ : arrow_class.isomorphisms ⊆ F) :
  is_iso_invariant F := λ w w' e hw,
begin
  have fac : w'.hom = e.inv.left ≫ w.hom ≫ e.hom.right,
  { have eq := arrow.hom.congr_right (e.inv_hom_id),
    dsimp at eq,
    rw [arrow.w_assoc e.inv, eq],
    dsimp,
    rw comp_id, },
  rw [← arrow.mk_eq w', fac],
  rw [← arrow.mk_eq w] at hw,
  exact h₁ e.inv.left _ (h₂ (mem_isomorphisms_of_is_iso _))
    (h₁ w.hom e.hom.right hw (h₂ (mem_isomorphisms_of_is_iso _))),
end

end is_iso_invariant

end arrow_class

end category_theory
