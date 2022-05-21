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

@[ext]
class category_with_fib_cof_W (D : Type*) [category D] :=
(fib cof W : arrow_class D)

variables {D : Type*} [category D]

namespace category_with_fib_cof_W

variables (data : category_with_fib_cof_W D) (data' : category_with_fib_cof_W Dᵒᵖ)

@[simps]
def op : category_with_fib_cof_W Dᵒᵖ :=
{ fib := data.cof.op,
  cof := data.fib.op,
  W := data.W.op }

@[simps]
def unop : category_with_fib_cof_W D :=
{ fib := data'.cof.unop,
  cof := data'.fib.unop,
  W := data'.W.unop }

lemma unop_op : data.op.unop = data :=
by ext1; apply arrow_class.unop_op

lemma op_unop : data'.unop.op = data' :=
by ext1; apply arrow_class.op_unop

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

def inverse_image {D' : Type*} [category D'] (F : D' ⥤ D) : category_with_fib_cof_W D' :=
{ fib := data.fib.inverse_image F,
  cof := data.cof.inverse_image F,
  W := data.W.inverse_image F }

end category_with_fib_cof_W

class model_category (D : Type*) [category D] extends category_with_fib_cof_W D :=
(CM1axiom : has_finite_limits D ∧ has_finite_colimits D)
(CM2axiom : to_category_with_fib_cof_W.CM2)
(CM3axiom : to_category_with_fib_cof_W.CM3)
(CM4axiom : to_category_with_fib_cof_W.CM4)
(CM5axiom : to_category_with_fib_cof_W.CM5)


namespace model_category

variable {D}
variable [M : model_category D]

include M

def CM1 := M.CM1axiom
def CM2 := M.CM2axiom
def CM3 := M.CM3axiom
def CM4 := M.CM4axiom
def CM5 := M.CM5axiom

def CM4a := (@CM4 D _ _).1
def CM4b := (@CM4 D _ _).2
def CM5a := (@CM5 D _ _).1
def CM5b := (@CM5 D _ _).2

instance : has_finite_limits D := (@CM1 D _ _).1
instance : has_finite_colimits D := (@CM1 D _ _).2

def fib := M.to_category_with_fib_cof_W.fib
def cof := M.to_category_with_fib_cof_W.cof
def W := M.to_category_with_fib_cof_W.W
def triv_fib := M.to_category_with_fib_cof_W.triv_fib
def triv_cof := M.to_category_with_fib_cof_W.triv_cof

lemma triv_cof_contains_W : (triv_cof : arrow_class D) ⊆ W := λ f hf, hf.2
lemma triv_fib_contains_W : (triv_fib : arrow_class D) ⊆ W := λ f hf, hf.2

--@[simps, protected]
instance : model_category Dᵒᵖ :=
{ to_category_with_fib_cof_W := M.to_category_with_fib_cof_W.op,
  CM1axiom := ⟨has_finite_limits_opposite, has_finite_colimits_opposite⟩,
  CM2axiom := by simpa only [← M.to_category_with_fib_cof_W.CM2_iff_op] using CM2axiom,
  CM3axiom := by simpa only [← M.to_category_with_fib_cof_W.CM3_iff_op] using CM3axiom,
  CM4axiom := by simpa only [← M.to_category_with_fib_cof_W.CM4_iff_op] using CM4axiom,
  CM5axiom := by simpa only [← M.to_category_with_fib_cof_W.CM5_iff_op] using CM5axiom, }


--variable {D}

def cof_retract_stable : (cof : arrow_class D).is_stable_by_retract := CM3.cof
def fib_retract_stable : (fib : arrow_class D).is_stable_by_retract := CM3.fib
def triv_cof_retract_stable : (triv_cof : arrow_class D).is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_intersection _ _ CM3.cof CM3.W
def triv_fib_retract_stable : (triv_fib : arrow_class D).is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_intersection _ _ CM3.fib CM3.W

lemma cof_equals_llp_triv_fib : (cof : arrow_class D) = (triv_fib : arrow_class D).left_lifting_property_with :=
(cof: arrow_class D).eq_left_lifting_property_with triv_fib CM5b CM4a CM3.cof
lemma triv_cof_equals_llp_fib : (triv_cof : arrow_class D) = (fib : arrow_class D).left_lifting_property_with :=
(triv_cof : arrow_class D).eq_left_lifting_property_with fib CM5a CM4b triv_cof_retract_stable

lemma fib_equals_rlp_triv_cof : (fib : arrow_class D) = (triv_cof : arrow_class D).right_lifting_property_with :=
begin
  convert congr_arg arrow_class.unop cof_equals_llp_triv_fib,
  { exact (arrow_class.unop_op _).symm, },
  { apply arrow_class.op_inj,
    simpa only [← arrow_class.left_lifting_property_with_op, arrow_class.op_unop], },
end

lemma triv_fib_equals_rlp_cof : (triv_fib : arrow_class D) = (cof : arrow_class D).right_lifting_property_with :=
begin
  convert congr_arg arrow_class.unop triv_cof_equals_llp_fib,
  { exact (arrow_class.unop_op _).symm, },
  { apply arrow_class.op_inj,
    simpa only [← arrow_class.left_lifting_property_with_op, arrow_class.op_unop], },
end

lemma cof_comp_stable : (cof : arrow_class D).is_stable_by_composition :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.is_stable_by_composition_of_llp_with, }
lemma triv_cof_comp_stable : (triv_cof : arrow_class D).is_stable_by_composition :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.is_stable_by_composition_of_llp_with, }

lemma fib_comp_stable : (fib : arrow_class D).is_stable_by_composition :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.is_stable_by_composition_of_rlp_with, }
lemma triv_fib_comp_stable : (triv_fib : arrow_class D).is_stable_by_composition :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.is_stable_by_composition_of_rlp_with, }

lemma cof_contains_iso : arrow_class.isomorphisms ⊆ (cof : arrow_class D) :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.contains_isomorphisms_of_llp_with, }
lemma triv_cof_contains_iso : arrow_class.isomorphisms ⊆ (triv_cof : arrow_class D) :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.contains_isomorphisms_of_llp_with, }
lemma fib_contains_iso : arrow_class.isomorphisms ⊆ (fib : arrow_class D) :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.contains_isomorphisms_of_rlp_with, }
lemma triv_fib_contains_iso : arrow_class.isomorphisms ⊆ (triv_fib : arrow_class D) :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.contains_isomorphisms_of_rlp_with, }

lemma W_contains_triv_cof : (triv_cof : arrow_class D) ⊆ W := λ f hf, hf.2
lemma cof_contains_triv_cof : (triv_cof : arrow_class D) ⊆ cof := λ f hf, hf.1
lemma W_contains_triv_fib : (triv_fib : arrow_class D) ⊆ W := λ f hf, hf.2
lemma fib_contains_triv_fib : (triv_fib : arrow_class D) ⊆ fib := λ f hf, hf.1

lemma W_contains_iso : arrow_class.isomorphisms ⊆ (W : arrow_class D) :=
begin
  intros f hf,
  suffices : f ∈ triv_cof,
  { exact W_contains_triv_cof this, },
  rw triv_cof_equals_llp_fib,
  exact (fib : arrow_class D).contains_isomorphisms_of_llp_with hf,
end 

lemma cof_iff_of_arrow_iso : (cof : arrow_class D).iff_of_arrow_iso :=
arrow_class.iff_of_arrow_iso.of_comp_stable_and_contains_iso _
  cof_comp_stable cof_contains_iso
lemma triv_cof_iff_of_arrow_iso : (triv_cof : arrow_class D).iff_of_arrow_iso :=
arrow_class.iff_of_arrow_iso.of_comp_stable_and_contains_iso _
  triv_cof_comp_stable triv_cof_contains_iso
lemma fib_iff_of_arrow_iso : (fib : arrow_class D).iff_of_arrow_iso :=
arrow_class.iff_of_arrow_iso.of_comp_stable_and_contains_iso _
  fib_comp_stable fib_contains_iso
lemma triv_fib_iff_of_arrow_iso : (triv_fib : arrow_class D).iff_of_arrow_iso :=
arrow_class.iff_of_arrow_iso.of_comp_stable_and_contains_iso _
  triv_fib_comp_stable triv_fib_contains_iso
lemma W_iff_of_arrow_iso : (W : arrow_class D).iff_of_arrow_iso :=
arrow_class.iff_of_arrow_iso.of_comp_stable_and_contains_iso _
  CM2.of_comp W_contains_iso

lemma cof_co_bc_stable : (cof : arrow_class D).is_stable_by_cobase_change :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }
lemma triv_cof_co_bc_stable : (triv_cof : arrow_class D).is_stable_by_cobase_change :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }
/-lemma fib_base_change_stable : M.fib.is_stable_by_base_change :=
by { rw fib_equals_rlp_triv_cof, apply arrow_class.is_stable_by_base_change_of_rlp_with, }
lemma triv_fib_base_change_stable : M.triv_fib.is_stable_by_base_change :=
by { rw triv_fib_equals_rlp_cof, apply arrow_class.is_stable_by_base_change_of_rlp_with, }
-/

--@[simp]
--def op_obj (X : M.C) : M.op.C := opposite.op X

variable (D)

@[derive category]
def Ho := (W : arrow_class D).localization

variable {D}

def Q : D ⥤ Ho D := arrow_class.localization.Q W

end model_category

end algebraic_topology
