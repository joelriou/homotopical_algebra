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


universes v u

namespace algebraic_topology

variables (D : Type*) [category D]

@[ext]
structure category_with_fib_cof_W := (fib cof W : arrow_class D)

variable {D}

namespace category_with_fib_cof_W

variables (data : category_with_fib_cof_W D) (data' : category_with_fib_cof_W Dᵒᵖ)

@[simps]
def op : (category_with_fib_cof_W Dᵒᵖ) :=
{ fib := data.cof.op,
  cof := data.fib.op,
  W := data.W.op }

@[simps]
def unop : category_with_fib_cof_W D :=
{ fib := data'.cof.unop,
  cof := data'.fib.unop,
  W := data'.W.unop }

lemma unop_op : data.op.unop = data :=
begin
  ext1,
  { exact arrow_class.unop_op data.fib, },
  { exact arrow_class.unop_op data.cof, },
  { exact arrow_class.unop_op data.W, },
end

lemma op_unop : data'.unop.op = data' :=
begin
  ext1,
  { exact arrow_class.op_unop data'.fib, },
  { exact arrow_class.op_unop data'.cof, },
  { exact arrow_class.op_unop data'.W, },
end

def triv_fib := data.fib ∩ data.W
def triv_cof := data.cof ∩ data.W

def CM2 := data.W.three_of_two

lemma CM2_iff_op : data.CM2 ↔ data.op.CM2 :=
begin
  dsimp only [CM2],
  rw [arrow_class.three_of_two_iff_op],
  reflexivity,
end

lemma CM2_iff_unop : data'.CM2 ↔ data'.unop.CM2 :=
by { rw [CM2_iff_op data'.unop, data'.op_unop], }

def CM3a := data.W.is_stable_by_retract
def CM3b := data.fib.is_stable_by_retract
def CM3c := data.cof.is_stable_by_retract

structure CM3 : Prop :=
(W : data.CM3a)
(fib : data.CM3b)
(cof : data.CM3c)

lemma CM3a_iff_op : data.CM3a ↔ data.op.CM3a :=
by { dsimp only [CM3a], erw arrow_class.is_stable_by_retract_iff_op, finish, }

lemma CM3b_iff_op : data.CM3b ↔ data.op.CM3c :=
by { dsimp only [CM3b, CM3c], erw arrow_class.is_stable_by_retract_iff_op, finish, }

lemma CM3c_iff_op : data.CM3c ↔ data.op.CM3b :=
by { dsimp only [CM3b, CM3c], erw arrow_class.is_stable_by_retract_iff_op, finish, }

lemma CM3_iff : data.CM3 ↔ data.CM3a ∧ data.CM3b ∧ data.CM3c :=
begin
  split,
  { intro h,
    cases h,
    finish, },
  { rintro ⟨ha, hb, hc⟩,
    exact ⟨ha, hb, hc⟩, },
end

lemma CM3_iff_op : data.CM3 ↔ data.op.CM3 :=
begin
  simp only [CM3_iff, data.CM3a_iff_op, data.CM3b_iff_op, data.CM3c_iff_op],
  finish,
end

lemma CM3_iff_unop : data'.CM3 ↔ data'.unop.CM3 :=
by { rw [CM3_iff_op data'.unop, data'.op_unop], }

def CM4a := data.cof.has_lifting_property data.triv_fib

def CM4b := data.triv_cof.has_lifting_property data.fib

def CM4 := data.CM4a ∧ data.CM4b

lemma CM4a_iff_op : data.CM4a ↔ data.op.CM4b := arrow_class.has_lifting_property_iff_op _ _
lemma CM4b_iff_op : data.CM4b ↔ data.op.CM4a := arrow_class.has_lifting_property_iff_op _ _

lemma CM4_iff_op : data.CM4 ↔ data.op.CM4 :=
by { dsimp only [CM4], rw [data.CM4a_iff_op, data.CM4b_iff_op], finish, }

lemma CM4_iff_unop : data'.CM4 ↔ data'.unop.CM4 :=
by { rw [CM4_iff_op data'.unop, data'.op_unop], }

def CM5a := arrow_class.factorisation_axiom data.triv_cof data.fib
def CM5b := arrow_class.factorisation_axiom data.cof data.triv_fib

def CM5 := data.CM5a ∧ data.CM5b

lemma CM5a_iff_op : data.CM5a ↔ data.op.CM5b := arrow_class.factorisation_axiom_iff_op _ _
lemma CM5b_iff_op : data.CM5b ↔ data.op.CM5a := arrow_class.factorisation_axiom_iff_op _ _

lemma CM5_iff_op : data.CM5 ↔ data.op.CM5 :=
by { dsimp only [CM5], rw [data.CM5a_iff_op, data.CM5b_iff_op], finish, }

lemma CM5_iff_unop : data'.CM5 ↔ data'.unop.CM5 :=
by { rw [CM5_iff_op data'.unop, data'.op_unop], }

end category_with_fib_cof_W

@[nolint check_univs]
structure model_category :=
(C : Type u) [hC : category.{v} C]
(fib_cof_we : category_with_fib_cof_W C)
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

def fib := M.fib_cof_we.fib
def cof := M.fib_cof_we.cof
def W := M.fib_cof_we.W
def triv_fib := M.fib_cof_we.triv_fib
def triv_cof := M.fib_cof_we.triv_cof

def CM4a := M.CM4.1
def CM4b := M.CM4.2
def CM5a := M.CM5.1
def CM5b := M.CM5.2

@[simps]
def op : model_category :=
{ C := M.Cᵒᵖ,
  fib_cof_we := M.fib_cof_we.op,
  CM1 := ⟨has_finite_limits_opposite, has_finite_colimits_opposite⟩,
  CM2 := by simpa only [← M.fib_cof_we.CM2_iff_op] using M.CM2,
  CM3 := by simpa only [← M.fib_cof_we.CM3_iff_op] using M.CM3,
  CM4 := by simpa only [← M.fib_cof_we.CM4_iff_op] using M.CM4,
  CM5 := by simpa only [← M.fib_cof_we.CM5_iff_op] using M.CM5, }

instance : has_finite_limits M.Cᵒᵖ := (op M).CM1.1
instance : has_finite_colimits M.Cᵒᵖ := (op M).CM1.2

def cof_retract_stable : M.cof.is_stable_by_retract := M.CM3.cof
def fib_retract_stable : M.fib.is_stable_by_retract := M.CM3.fib
def triv_cof_retract_stable : M.triv_cof.is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_intersection _ _ M.CM3.cof M.CM3.W
def triv_fib_retract_stable : M.triv_fib.is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_intersection _ _ M.CM3.fib M.CM3.W

lemma cof_equals_llp_triv_fib : M.cof = M.triv_fib.left_lifting_property_with :=
M.cof.eq_left_lifting_property_with M.triv_fib M.CM5b M.CM4a M.CM3.cof
lemma triv_cof_equals_llp_fib : M.triv_cof = M.fib.left_lifting_property_with :=
M.triv_cof.eq_left_lifting_property_with M.fib
  M.CM5a M.CM4b M.triv_cof_retract_stable

lemma fib_equals_rlp_triv_cof : M.fib = M.triv_cof.right_lifting_property_with :=
begin
  convert congr_arg arrow_class.unop M.op.cof_equals_llp_triv_fib,
  { exact (arrow_class.unop_op _).symm, },
  { apply arrow_class.op_inj,
    simpa only [← arrow_class.left_lifting_property_with_op, arrow_class.op_unop], },
end

lemma triv_fib_equals_rlp_cof : M.triv_fib = M.cof.right_lifting_property_with :=
begin
  convert congr_arg arrow_class.unop M.op.triv_cof_equals_llp_fib,
  { exact (arrow_class.unop_op _).symm, },
  { apply arrow_class.op_inj,
    simpa only [← arrow_class.left_lifting_property_with_op, arrow_class.op_unop], },
end

lemma cof_comp_stable : M.cof.is_stable_by_composition :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.is_stable_by_composition_of_llp_with, }
lemma triv_cof_comp_stable : M.triv_cof.is_stable_by_composition :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.is_stable_by_composition_of_llp_with, }

lemma fib_comp_stable : M.fib.is_stable_by_composition :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.is_stable_by_composition_of_rlp_with, }
lemma triv_fib_comp_stable : M.triv_fib.is_stable_by_composition :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.is_stable_by_composition_of_rlp_with, }

lemma cof_contains_iso : arrow_class.isomorphisms ⊆ M.cof :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.contains_isomorphisms_of_llp_with, }
lemma triv_cof_contains_iso : arrow_class.isomorphisms ⊆ M.triv_cof :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.contains_isomorphisms_of_llp_with, }
lemma fib_contains_iso : arrow_class.isomorphisms ⊆ M.fib :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.contains_isomorphisms_of_rlp_with, }
lemma triv_fib_contains_iso : arrow_class.isomorphisms ⊆ M.triv_fib :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.contains_isomorphisms_of_rlp_with, }

lemma cof_cobase_change_stable : M.cof.is_stable_by_cobase_change :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }
lemma triv_cof_cobase_change_stable : M.triv_cof.is_stable_by_cobase_change :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }
lemma fib_base_change_stable : M.fib.is_stable_by_base_change :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.is_stable_by_base_change_of_rlp_with, }
lemma triv_fib_base_change_stable : M.triv_fib.is_stable_by_base_change :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.is_stable_by_base_change_of_rlp_with, }

@[simp]
def op_obj (X : M.C) : M.op.C := opposite.op X

def Ho := localization M.W

instance : category (Ho M) := (infer_instance : category (localization M.W))

variable {M}

def Q : M.C ⥤ Ho M := category_theory.localization.Q _

end model_category

end algebraic_topology
