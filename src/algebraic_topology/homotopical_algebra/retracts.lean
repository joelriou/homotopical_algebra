/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.hom_class

open category_theory
open opposite

variables {C : Type*} [category C]

namespace quiver.hom

def is_retract {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') := 
  ∃ (a : X ⟶ X') (b : X' ⟶ X) (a' : Y ⟶ Y') (b' : Y' ⟶ Y),
    (f ≫ a' = a ≫ f' ∧ b ≫ f = f' ≫ b') ∧ (a ≫ b = 𝟙 X ∧ a' ≫ b' = 𝟙 Y)

def is_retract_iff_op {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') :
  f.is_retract f' ↔ f.op.is_retract f'.op :=
begin
  split,
  { intro h,
    rcases h with ⟨a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
    use [b'.op, a'.op, b.op, a.op],
    split; split,
    { exact congr_arg op comm₂, },
    { exact congr_arg op comm₁, },
    { exact congr_arg op r₂, },
    { exact congr_arg op r₁, }, },
  { intro h,
    rcases h with ⟨a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
    use [b'.unop, a'.unop, b.unop, a.unop],
    split; split,
    { exact congr_arg unop comm₂, },
    { exact congr_arg unop comm₁, },
    { exact congr_arg unop r₂, },
    { exact congr_arg unop r₁, }, },
end

end quiver.hom

namespace hom_class

def is_stable_by_retract (F : hom_class C) := ∀ (X Y : C) (f : X ⟶ Y),
  (∃ (X' Y' : C) (f' : X' ⟶ Y') (hf' : F.contains f'), f.is_retract f') → f ∈ F X Y    

lemma is_stable_by_retract_iff_op (F : hom_class C) :
  is_stable_by_retract F ↔ is_stable_by_retract F.op :=
begin
  split,
  { intros hF X Y f hf,
    rcases hf with ⟨X', Y', f', hf', a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
    apply hF _ _ f.unop,
    use [Y'.unop, X'.unop, f'.unop, hf', b'.unop, a'.unop, b.unop, a.unop],
    split; split,
    { simp only [← unop_comp, comm₂], },
    { simp only [← unop_comp, comm₁], },
    { simpa only [← unop_comp, r₂], },
    { simpa only [← unop_comp, r₁], }, },
  { intros hF X Y f hf,
    rcases hf with ⟨X', Y', f', hf', a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
    apply hF _ _ f.op,
    use [opposite.op Y', opposite.op X', f'.op, hf', b'.op, a'.op, b.op, a.op],
    split; split,
    { simp only [← op_comp, comm₂], },
    { simp only [← op_comp, comm₁], },
    { simpa only [← op_comp, r₂], },
    { simpa only [← op_comp, r₁], }, },
end

end hom_class