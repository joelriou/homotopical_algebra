/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.factorisation_axiom
import for_mathlib.algebraic_topology.homotopical_algebra.three_of_two

open category_theory category_theory.limits

namespace algebraic_topology

variables (C : Type*) [category C]

@[ext]
class category_with_fib_cof_weq := (fib cof weq : arrow_class C)

namespace category_with_fib_cof_weq

variables {C} (data : category_with_fib_cof_weq C) (data' : category_with_fib_cof_weq Cᵒᵖ)

@[simps]
def op : category_with_fib_cof_weq Cᵒᵖ :=
{ fib := data.cof.op,
  cof := data.fib.op,
  weq := data.weq.op }

@[simps]
def unop : category_with_fib_cof_weq C :=
{ fib := data'.cof.unop,
  cof := data'.fib.unop,
  weq := data'.weq.unop }

lemma unop_op : data.op.unop = data :=
by ext1; apply arrow_class.unop_op

lemma op_unop : data'.unop.op = data' :=
by ext1; apply arrow_class.op_unop

def triv_fib := data.fib ∩ data.weq
def triv_cof := data.cof ∩ data.weq

def inverse_image {D : Type*} [category D] (F : D ⥤ C) : category_with_fib_cof_weq D :=
{ fib := data.fib.inverse_image F,
  cof := data.cof.inverse_image F,
  weq := data.weq.inverse_image F }

def CM2 := data.weq.three_of_two
lemma CM2_iff_op : data.CM2 ↔ data.op.CM2 := arrow_class.three_of_two.iff_op _

def CM3a := data.weq.is_stable_by_retract
def CM3b := data.fib.is_stable_by_retract
def CM3c := data.cof.is_stable_by_retract

structure CM3 : Prop :=
(weq : data.CM3a)
(fib : data.CM3b)
(cof : data.CM3c)

namespace CM3

variable {data}

def triv_cof (h : data.CM3) : data.triv_cof.is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_inter h.cof h.weq
def triv_fib (h : data.CM3) : data.triv_fib.is_stable_by_retract :=
arrow_class.is_stable_by_retract.of_inter h.fib h.weq

end CM3

lemma CM3a_iff_op : data.CM3a ↔ data.op.CM3a := arrow_class.is_stable_by_retract.iff_op _
lemma CM3b_iff_op : data.CM3b ↔ data.op.CM3c := arrow_class.is_stable_by_retract.iff_op _
lemma CM3c_iff_op : data.CM3c ↔ data.op.CM3b := arrow_class.is_stable_by_retract.iff_op _
lemma CM3_iff : data.CM3 ↔ data.CM3a ∧ data.CM3b ∧ data.CM3c :=
by { split; rintro ⟨a, b, c⟩; exact ⟨a, b, c⟩, }
lemma CM3_iff_op : data.CM3 ↔ data.op.CM3 :=
by { simp only [CM3_iff, ← CM3a_iff_op, ← CM3b_iff_op, ← CM3c_iff_op], tauto, }

def CM4a := data.triv_cof.has_lifting_property data.fib
def CM4b := data.cof.has_lifting_property data.triv_fib
def CM4 := data.CM4a ∧ data.CM4b
lemma CM4a_iff_op : data.CM4a ↔ data.op.CM4b := arrow_class.has_lifting_property.iff_op _ _
lemma CM4b_iff_op : data.CM4b ↔ data.op.CM4a := arrow_class.has_lifting_property.iff_op _ _
lemma CM4_iff_op : data.CM4 ↔ data.op.CM4 :=
by { dsimp only [CM4], rw [← CM4a_iff_op, ← CM4b_iff_op], tauto, }

def CM5a := factorisation_axiom data.triv_cof data.fib
def CM5b := factorisation_axiom data.cof data.triv_fib
def CM5 := data.CM5a ∧ data.CM5b

lemma CM5a_iff_op : data.CM5a ↔ data.op.CM5b := factorisation_axiom.iff_op _ _
lemma CM5b_iff_op : data.CM5b ↔ data.op.CM5a := factorisation_axiom.iff_op _ _
lemma CM5_iff_op : data.CM5 ↔ data.op.CM5 :=
by { dsimp only [CM5], rw [← CM5a_iff_op, ← CM5b_iff_op], tauto, }

end category_with_fib_cof_weq

end algebraic_topology