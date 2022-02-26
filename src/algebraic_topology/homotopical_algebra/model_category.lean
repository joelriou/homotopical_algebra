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

variables (D : Type*) [category D]

@[ext]
structure category_with_fib_cof_we := (fibrations cofibrations weak_equivalences : hom_class D)

variable {D}

namespace category_with_fib_cof_we

variables (data : category_with_fib_cof_we D) (data' : category_with_fib_cof_we Dᵒᵖ)

@[simps]
def op : (category_with_fib_cof_we Dᵒᵖ) :=
{ fibrations := data.cofibrations.op,
  cofibrations := data.fibrations.op,
  weak_equivalences := data.weak_equivalences.op }

@[simps]
def unop : category_with_fib_cof_we D :=
{ fibrations := data'.cofibrations.unop,
  cofibrations := data'.fibrations.unop,
  weak_equivalences := data'.weak_equivalences.unop }

lemma unop_op : data.op.unop = data :=
by { ext1; refl, }

lemma op_unop : data'.unop.op = data' :=
by { ext1; refl, }

def trivial_fibrations : hom_class D :=
  λ X Y, data.fibrations X Y ∩ data.weak_equivalences X Y

def trivial_cofibrations : hom_class D :=
  λ X Y, data.cofibrations X Y ∩ data.weak_equivalences X Y

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

def CM5a := ∀ (X Y : D) (f : X ⟶ Y), ∃ (Z : D) (i : X ⟶ Z) (p : Z ⟶ Y),
  data.trivial_cofibrations.contains i ∧ data.fibrations.contains p ∧ f = i ≫ p

def CM5b := ∀ (X Y : D) (f : X ⟶ Y), ∃ (Z : D) (i : X ⟶ Z) (p : Z ⟶ Y),
  data.cofibrations.contains i ∧ data.trivial_fibrations.contains p ∧ f = i ≫ p

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

structure model_category :=
(C : Type*) [hC : category C]
(fib_cof_we : category_with_fib_cof_we C)
(CM1 : has_finite_limits C ∧ has_finite_colimits C)
(CM2 : fib_cof_we.CM2)
(CM3 : fib_cof_we.CM3)
(CM4 : fib_cof_we.CM4)
(CM5 : fib_cof_we.CM5)

namespace model_category

variable (M : model_category)

instance : category M.C := M.hC
instance : has_finite_limits M.C := M.CM1.1
instance : has_finite_colimits M.C := M.CM1.2

def fibrations := M.fib_cof_we.fibrations
def cofibrations := M.fib_cof_we.cofibrations
def weak_equivalences := M.fib_cof_we.weak_equivalences
def trivial_fibrations := M.fib_cof_we.trivial_fibrations
def trivial_cofibrations := M.fib_cof_we.trivial_cofibrations

def CM2a := M.CM2.1
def CM2b := M.CM2.2.1
def CM2c := M.CM2.2.2
def CM3a := M.CM3.1
def CM3b := M.CM3.2.1
def CM3c := M.CM3.2.2
def CM4a := M.CM4.1
def CM4b := M.CM4.2
def CM5a := M.CM5.1
def CM5b := M.CM5.2

lemma cof_comp_stable : M.cofibrations.is_stable_by_composition := sorry
lemma triv_cof_comp_stable : M.trivial_cofibrations.is_stable_by_composition := sorry
lemma fib_comp_stable : M.fibrations.is_stable_by_composition := sorry
lemma triv_fib_comp_stable : M.trivial_fibrations.is_stable_by_composition := sorry

lemma cof_contains_iso : M.cofibrations.contains_isomorphisms := sorry
lemma triv_cof_contains_iso : M.trivial_cofibrations.contains_isomorphisms := sorry
lemma fib_contains_iso : M.fibrations.contains_isomorphisms := sorry
lemma triv_fib_contains_iso : M.trivial_fibrations.contains_isomorphisms := sorry

@[simps]
def op : model_category :=
{ C := M.Cᵒᵖ,
  fib_cof_we := M.fib_cof_we.op,
  CM1 := ⟨has_finite_limits_opposite, has_finite_colimits_opposite⟩,
  CM2 := by simpa only [← M.fib_cof_we.CM2_iff_op] using M.CM2,
  CM3 := by simpa only [← M.fib_cof_we.CM3_iff_op] using M.CM3,
  CM4 := by simpa only [← M.fib_cof_we.CM4_iff_op] using M.CM4,
  CM5 := by simpa only [← M.fib_cof_we.CM5_iff_op] using M.CM5, }

@[simp]
def op_obj (X : M.C) : M.op.C := opposite.op X

def Ho := localization M.weak_equivalences

instance : category (Ho M) := (infer_instance : category (localization M.weak_equivalences))

variable {M}

def Q : M.C ⥤ Ho M := category_theory.localization.Q _

end model_category

end algebraic_topology
