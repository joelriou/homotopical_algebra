/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.construction
import algebraic_topology.homotopical_algebra.lifting_properties

open category_theory
open category_theory.category
open category_theory.limits
open opposite

namespace algebraic_topology

variables (C : Type*) [category C]

@[ext]
structure category_with_fib_cof_we := (fibrations cofibrations weak_equivalences : hom_class C)

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

structure model_category [has_finite_limits C] [has_finite_colimits C]
  extends category_with_fib_cof_we C :=
--  (CM1 : category_with_fib_cof_we.CM1 C)
  (CM2 : to_category_with_fib_cof_we.CM2)
  (CM3 : to_category_with_fib_cof_we.CM3)
  (CM4 : to_category_with_fib_cof_we.CM4)
  (CM5 : to_category_with_fib_cof_we.CM5)

namespace model_category

variables {C} [has_finite_limits C] [has_finite_colimits C] (M : model_category C)

def fibrations := M.1.fibrations
def cofibrations := M.1.cofibrations
def weak_equivalences := M.1.weak_equivalences
def trivial_fibrations := M.1.trivial_fibrations
def trivial_cofibrations := M.1.trivial_cofibrations

def op [has_finite_limits C] [has_finite_colimits C] [has_finite_limits Cᵒᵖ] [has_finite_colimits Cᵒᵖ] :
  model_category Cᵒᵖ :=
{ to_category_with_fib_cof_we := M.to_category_with_fib_cof_we.op,
--  CM1 := category_with_fib_cof_we.CM1_op_of_CM1 M.CM1,
  CM2 := by simpa only [← M.1.CM2_iff_op] using M.CM2,
  CM3 := by simpa only [← M.1.CM3_iff_op] using M.CM3,
  CM4 := by simpa only [← M.1.CM4_iff_op] using M.CM4,
  CM5 := by simpa only [← M.1.CM5_iff_op] using M.CM5, }

def unop [has_finite_limits C] [has_finite_colimits C] [has_finite_limits Cᵒᵖ] [has_finite_colimits Cᵒᵖ]
  (M' : model_category Cᵒᵖ) : model_category C :=
{ to_category_with_fib_cof_we := M'.to_category_with_fib_cof_we.unop,
--  CM1 := ⟨infer_instance, infer_instance⟩,
  CM2 := by { simpa only [← M'.1.CM2_iff_unop] using M'.CM2, },
  CM3 := by { simpa only [← M'.1.CM3_iff_unop] using M'.CM3, },
  CM4 := by { simpa only [← M'.1.CM4_iff_unop] using M'.CM4, },
  CM5 := by { simpa only [← M'.1.CM5_iff_unop] using M'.CM5, }, }

def Ho := localization M.weak_equivalences

instance : category (Ho M) := (infer_instance : category (localization M.weak_equivalences))

variable {M}

def Q : C ⥤ Ho M := category_theory.localization.Q _

end model_category

end algebraic_topology
