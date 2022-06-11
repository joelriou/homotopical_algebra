/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow
import for_mathlib.category_theory.arrow
import for_mathlib.category_theory.comma_op

/-!

# Classes of arrows in a category

If `C` is a category, an `arrow_class C` is a class of arrows in C. It is
implemented here as `set (arrow C)`.

If `W : arrow_class C`, and `f : X ⟶ Y` is a morphism in `C`, `W f` is the
condition that `arrow.mk f` belongs to `W`.

-/

noncomputable theory

namespace category_theory

variables (C : Type*) [category C] {D : Type*} [category D]

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

class is_stable_by_composition : Prop :=
(comp_stable : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F)

namespace is_stable_by_composition

variables {F F'}

lemma stability (h : is_stable_by_composition F)
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hf : arrow.mk f ∈ F) (hg : arrow.mk g ∈ F) :
  arrow.mk (f ≫ g) ∈ F :=
begin
  have s := h.comp_stable,
  exact s f g hf hg,
end

lemma op (h : is_stable_by_composition F) :
  is_stable_by_composition F.op :=
⟨λ X Y Z f g hf hg, h.stability g.unop f.unop hg hf⟩

lemma unop (h : is_stable_by_composition F') :
  is_stable_by_composition F'.unop :=
⟨λ X Y Z f g hf hg, h.stability g.op f.op hg hf⟩

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

end arrow_class

end category_theory