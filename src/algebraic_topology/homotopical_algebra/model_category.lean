/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.pullbacks
import category_theory.limits.opposites
import category_theory.localization.construction

open category_theory
open category_theory.category
open category_theory.limits
open opposite

variables (C : Type*) [category C]

@[ext]
structure category_with_fib_cof_we := (fibrations cofibrations weak_equivalences : hom_class C)

variable {C}

namespace quiver.hom

def left_lifting_property {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :=
  ∀ (f : A ⟶ X) (g : B ⟶ Y) (hfg : f ≫ p = i ≫ g), ∃ (h : B ⟶ X), f = i ≫ h ∧ g = h ≫ p

lemma left_lifting_property_iff_op {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
  i.left_lifting_property p ↔ p.op.left_lifting_property i.op :=
begin
  split,
  { intros hip f g hfg,
    rcases hip g.unop f.unop (by { exact congr_arg unop hfg.symm, }) with ⟨h, comm₁, comm₂⟩,
    use h.op,
    split,
    { exact congr_arg op comm₂, },
    { exact congr_arg op comm₁, }, },
  { intros hip f g hfg,
    rcases hip g.op f.op (by { exact congr_arg op hfg.symm, }) with ⟨h, comm₁, comm₂⟩,
    use h.unop,
    split,
    { exact congr_arg unop comm₂, },
    { exact congr_arg unop comm₁, }, },
end

lemma id_has_left_lifting_propery (A : C) {X Y : C} (p : X ⟶ Y) :
  (𝟙 A).left_lifting_property p :=
begin
  intros f g hfg,
  rw id_comp at hfg,
  use f,
  split,
  { rw id_comp, },
  { rw hfg, }
end

lemma id_has_right_lifting_property (X : C) {A B : C} (i : A ⟶ B) :
  i.left_lifting_property (𝟙 X) :=
by { rw left_lifting_property_iff_op, apply id_has_left_lifting_propery, }

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

lemma has_left_lifting_property_of_retract {A B A' B' X Y : C} (i : A ⟶ B) (p : X ⟶ Y) (i' : A' ⟶ B')
  (hii' : i.is_retract i') (hi' : i'.left_lifting_property p) : i.left_lifting_property p :=
begin
  rcases hii' with ⟨a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
  intros f g hfg,
  rcases hi' (b ≫ f) (b' ≫ g) (by { rw [assoc, hfg, ← assoc, comm₂, assoc], })
    with ⟨h, ⟨lift₁, lift₂⟩⟩,
  use a' ≫ h,
  split,
  { rw [← assoc, comm₁, assoc, ← lift₁, ← assoc, r₁, id_comp], },
  { rw [assoc, ← lift₂, ← assoc, r₂, id_comp], }
end

lemma has_right_lifting_property_of_retract {A B X Y X' Y' : C} (p : X ⟶ Y) (i : A ⟶ B) (p' : X' ⟶ Y')
  (hpp' : p.is_retract p') (hp' : i.left_lifting_property p') : i.left_lifting_property p :=
begin
  rw left_lifting_property_iff_op,
  rw is_retract_iff_op at hpp',
  apply has_left_lifting_property_of_retract p.op i.op p'.op hpp',
  rw ← left_lifting_property_iff_op,
  exact hp',
end

lemma has_left_lifting_property_of_is_iso {A B X Y : C} (i : A ⟶ B) [is_iso i] (p : X ⟶ Y) :
  i.left_lifting_property p :=
begin
  refine has_left_lifting_property_of_retract i p (𝟙 A) _ (id_has_left_lifting_propery A p),
  use [𝟙 A, 𝟙 A, inv i, i],
  split; split,
  { simp only [is_iso.hom_inv_id, comp_id], },
  { refl, },
  { rw id_comp, },
  { simp only [is_iso.inv_hom_id], },
end

lemma has_right_lifting_property_of_is_iso {A B X Y : C} (p : X ⟶ Y) [is_iso p] (i : A ⟶ B) :
  i.left_lifting_property p :=
by { rw i.left_lifting_property_iff_op, apply has_left_lifting_property_of_is_iso, }

end quiver.hom

namespace hom_class
variables (F : hom_class C) (F' : hom_class Cᵒᵖ)

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

def is_stable_by_retract := ∀ (X Y : C) (f : X ⟶ Y),
  (∃ (X' Y' : C) (f' : X' ⟶ Y') (hf' : f' ∈ F X' Y'), f.is_retract f') → f ∈ F X Y    

lemma is_stable_by_retract_iff_op :
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

def left_lifting_property (G : hom_class C) := ∀ (A B X Y : C) (i : A ⟶ B) (p : X ⟶ Y),
  i ∈ F A B → p ∈ G X Y → i.left_lifting_property p

def left_lifting_property_iff_op (G : hom_class C) :
  F.left_lifting_property G ↔ G.op.left_lifting_property F.op :=
begin
  split,
  { intro h,
    intros A B X Y i p hi hp,
    simpa only [p.unop.left_lifting_property_iff_op] using h _ _ _ _ p.unop i.unop hp hi, },
  { intro h,
    intros A B X Y i p hi hp,
    simpa only [i.left_lifting_property_iff_op] using h _ _ _ _ p.op i.op hp hi, }
end

end hom_class

variable {C}

namespace category_with_fib_cof_we

variables (data : category_with_fib_cof_we C) (data' : category_with_fib_cof_we Cᵒᵖ)

def op : (category_with_fib_cof_we Cᵒᵖ) :=
{ fibrations := data.cofibrations.op,
  cofibrations := data.fibrations.op,
  weak_equivalences := data.weak_equivalences.op }

def unop : category_with_fib_cof_we C :=
{ fibrations := data'.cofibrations.unop,
  cofibrations := data'.fibrations.unop,
  weak_equivalences := data'.weak_equivalences.unop }

lemma unop_op : data.op.unop = data :=
by { ext1; refl, }

lemma op_unop : data'.unop.op = data' :=
by { ext1; refl, }

def trivial_fibrations : hom_class C :=
  λ X Y, data.fibrations X Y ∩ data.weak_equivalences X Y

def trivial_cofibrations : hom_class C :=
  λ X Y, data.cofibrations X Y ∩ data.weak_equivalences X Y

variable (C)
def CM1 := has_finite_limits C ∧ has_finite_colimits C

variable {C}

lemma CM1_op_of_CM1 (hC : CM1 C) : CM1 Cᵒᵖ :=
begin
  haveI := hC.left,
  haveI := hC.right,
  split,
  { apply has_finite_limits_opposite, },
  { apply has_finite_colimits_opposite, },
end

def CM2 := data.weak_equivalences.three_of_two

lemma CM2_iff_op : data.CM2 ↔ data.op.CM2 :=
begin
  dsimp only [CM2],
  rw [hom_class.three_of_two_iff_op],
  reflexivity,
end

lemma CM2_iff_unop : data'.CM2 ↔ data'.unop.CM2 :=
by { rw [CM2_iff_op data'.unop, data'.op_unop], }

def CM3a := data.weak_equivalences.is_stable_by_retract
def CM3b := data.fibrations.is_stable_by_retract
def CM3c := data.cofibrations.is_stable_by_retract

def CM3 := data.CM3a ∧ data.CM3b ∧ data.CM3c

lemma CM3a_iff_op : data.CM3a ↔ data.op.CM3a :=
by { dsimp only [CM3a], erw hom_class.is_stable_by_retract_iff_op, finish, }

lemma CM3b_iff_op : data.CM3b ↔ data.op.CM3c :=
by { dsimp only [CM3b, CM3c], erw hom_class.is_stable_by_retract_iff_op, finish, }

lemma CM3c_iff_op : data.CM3c ↔ data.op.CM3b :=
by { dsimp only [CM3b, CM3c], erw hom_class.is_stable_by_retract_iff_op, finish, }

lemma CM3_iff_op : data.CM3 ↔ data.op.CM3 :=
begin
  dsimp only [CM3],
  rw [data.CM3a_iff_op, data.CM3b_iff_op, data.CM3c_iff_op],
  finish,
end

lemma CM3_iff_unop : data'.CM3 ↔ data'.unop.CM3 :=
by { rw [CM3_iff_op data'.unop, data'.op_unop], }

def CM4a := data.cofibrations.left_lifting_property data.trivial_fibrations

def CM4b := data.trivial_cofibrations.left_lifting_property data.fibrations

def CM4 := data.CM4a ∧ data.CM4b

lemma CM4a_iff_op : data.CM4a ↔ data.op.CM4b := hom_class.left_lifting_property_iff_op _ _

lemma CM4b_iff_op : data.CM4b ↔ data.op.CM4a := hom_class.left_lifting_property_iff_op _ _

lemma CM4_iff_op : data.CM4 ↔ data.op.CM4 :=
by { dsimp only [CM4], rw [data.CM4a_iff_op, data.CM4b_iff_op], finish, }

lemma CM4_iff_unop : data'.CM4 ↔ data'.unop.CM4 :=
by { rw [CM4_iff_op data'.unop, data'.op_unop], }

def CM5a := ∀ (X Y : C) (f : X ⟶ Y), ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
  i ∈ data.trivial_cofibrations X Z ∧ p ∈ data.fibrations Z Y ∧ f = i ≫ p

def CM5b := ∀ (X Y : C) (f : X ⟶ Y), ∃ (Z : C) (i : X ⟶ Z) (p : Z ⟶ Y),
  i ∈ data.cofibrations X Z ∧ p ∈ data.trivial_fibrations Z Y ∧ f = i ≫ p

def CM5 := data.CM5a ∧ data.CM5b

lemma CM5a_iff_op : data.CM5a ↔ data.op.CM5b :=
begin
  split,
  { intros h X Y f,
    rcases h Y.unop X.unop f.unop with ⟨Z, i, p, hi, hp, fac⟩,
    use [opposite.op Z, p.op, i.op, hp, hi],
    rw [← quiver.hom.op_unop f, fac, op_comp], },
  { intros h X Y f,
    rcases h _ _ f.op with ⟨Z, i, p, hi, hp, fac⟩,
    use [Z.unop, p.unop, i.unop, hp, hi],
    rw [← quiver.hom.unop_op f, fac, unop_comp], }
end

lemma CM5b_iff_op : data.CM5b ↔ data.op.CM5a :=
begin
  split,
  { intros h X Y f,
    rcases h Y.unop X.unop f.unop with ⟨Z, i, p, hi, hp, fac⟩,
    use [opposite.op Z, p.op, i.op, hp, hi],
    rw [← quiver.hom.op_unop f, fac, op_comp], },
  { intros h X Y f,
    rcases h _ _ f.op with ⟨Z, i, p, hi, hp, fac⟩,
    use [Z.unop, p.unop, i.unop, hp, hi],
    rw [← quiver.hom.unop_op f, fac, unop_comp], }
end

lemma CM5_iff_op : data.CM5 ↔ data.op.CM5 :=
by { dsimp only [CM5], rw [data.CM5a_iff_op, data.CM5b_iff_op], finish, }

lemma CM5_iff_unop : data'.CM5 ↔ data'.unop.CM5 :=
by { rw [CM5_iff_op data'.unop, data'.op_unop], }

end category_with_fib_cof_we

variables (C) 

structure model_category
  extends category_with_fib_cof_we C :=
  (CM1 : category_with_fib_cof_we.CM1 C)
  (CM2 : to_category_with_fib_cof_we.CM2)
  (CM3 : to_category_with_fib_cof_we.CM3)
  (CM4 : to_category_with_fib_cof_we.CM4)
  (CM5 : to_category_with_fib_cof_we.CM5)

namespace model_category

variables (M : model_category C) {C}

def fibrations := M.1.fibrations
def cofibrations := M.1.cofibrations
def weak_equivalences := M.1.weak_equivalences
def trivial_fibrations := M.1.trivial_fibrations
def trivial_cofibrations := M.1.trivial_cofibrations

def op : model_category Cᵒᵖ :=
{ to_category_with_fib_cof_we := M.to_category_with_fib_cof_we.op,
  CM1 := category_with_fib_cof_we.CM1_op_of_CM1 M.CM1,
  CM2 := by simpa only [← M.1.CM2_iff_op] using M.CM2,
  CM3 := by simpa only [← M.1.CM3_iff_op] using M.CM3,
  CM4 := by simpa only [← M.1.CM4_iff_op] using M.CM4,
  CM5 := by simpa only [← M.1.CM5_iff_op] using M.CM5, }

def unop [has_finite_limits C] [has_finite_colimits C]
  (M' : model_category Cᵒᵖ) : model_category C :=
{ to_category_with_fib_cof_we := M'.to_category_with_fib_cof_we.unop,
  CM1 := ⟨infer_instance, infer_instance⟩,
  CM2 := by { simpa only [← M'.1.CM2_iff_unop] using M'.CM2, },
  CM3 := by { simpa only [← M'.1.CM3_iff_unop] using M'.CM3, },
  CM4 := by { simpa only [← M'.1.CM4_iff_unop] using M'.CM4, },
  CM5 := by { simpa only [← M'.1.CM5_iff_unop] using M'.CM5, }, }

#check 42

def Ho := localization M.weak_equivalences

instance : category (Ho M) := (infer_instance : category (localization M.weak_equivalences))

notation `Ho(`M`)` := Ho M

variable {M}

def Q : C ⥤ Ho M := category_theory.localization.Q _

end model_category
