/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category_axioms

noncomputable theory

open category_theory category_theory.limits

namespace algebraic_topology

variables (C : Type*) [category C]

class model_category extends category_with_fib_cof_weq C :=
(CM1axiom : has_finite_limits C ∧ has_finite_colimits C)
(CM2axiom : to_category_with_fib_cof_weq.CM2)
(CM3axiom : to_category_with_fib_cof_weq.CM3)
(CM4axiom : to_category_with_fib_cof_weq.CM4)
(CM5axiom : to_category_with_fib_cof_weq.CM5)

namespace model_category

variable {C}
variable [M : model_category C]
include M

def fib := M.fib
def cof := M.cof
def weq := M.weq
def triv_fib := M.to_category_with_fib_cof_weq.triv_fib
def triv_cof := M.to_category_with_fib_cof_weq.triv_cof

def CM1 := M.CM1axiom
def CM2 := M.CM2axiom
def CM3 := M.CM3axiom
def CM4 := M.CM4axiom
def CM5 := M.CM5axiom

def CM3a : M.to_category_with_fib_cof_weq.CM3a := CM3.weq
def CM3b : M.to_category_with_fib_cof_weq.CM3b := CM3.fib
def CM3c : M.to_category_with_fib_cof_weq.CM3c := CM3.cof
def CM4a : M.to_category_with_fib_cof_weq.CM4a := CM4.1
def CM4b : M.to_category_with_fib_cof_weq.CM4b := CM4.2
def CM5a : M.to_category_with_fib_cof_weq.CM5a := CM5.1
def CM5b : M.to_category_with_fib_cof_weq.CM5b := CM5.2

instance : has_finite_limits C := CM1.1
instance : has_finite_colimits C := CM1.2

instance : model_category Cᵒᵖ :=
{ to_category_with_fib_cof_weq := M.to_category_with_fib_cof_weq.op,
  CM1axiom := ⟨has_finite_limits_opposite, has_finite_colimits_opposite⟩,
  CM2axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM2_iff_op] using CM2axiom,
  CM3axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM3_iff_op] using CM3axiom,
  CM4axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM4_iff_op] using CM4axiom,
  CM5axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM5_iff_op] using CM5axiom, }

variables {A B X Y Z : C} (i : A ⟶ B) {p : X ⟶ Y} {q : Y ⟶ Z} {f : X ⟶ Y} (hip : is_retract_hom i p)

class cofibration := (mem : arrow.mk i ∈ M.cof)
class fibration := (mem : arrow.mk i ∈ M.fib)
class weak_eq := (mem : arrow.mk i ∈ M.weq)

variable {i}

instance CM4a' [hi₁ : cofibration i] [hi₂ : weak_eq i] [hp : fibration p] :
  has_lifting_property_new i p := CM4a i ⟨hi₁.mem, hi₂.mem⟩ p hp.mem
instance CM4b' [hi : cofibration i] [hp₁ : fibration p] [hp₂ : weak_eq p] :
  has_lifting_property_new i p := CM4b i hi.mem p ⟨hp₁.mem, hp₂.mem⟩


lemma cofibration_retract_stable [hp : cofibration p] : cofibration i := ⟨CM3.cof i p hip hp.mem⟩
lemma fibration_retract_stable [hp : fibration p] : fibration i := ⟨CM3.fib i p hip hp.mem⟩
lemma weq_retract_stable [hp : weak_eq p] : weak_eq i := ⟨CM3.weq i p hip hp.mem⟩

lemma cof_eq_llp_with_triv_fib : cof = (triv_fib : arrow_class C).llp_with :=
factorisation_axiom.eq_llp_with CM5b CM4b CM3.cof
lemma triv_fib_eq_rlp_with_cof : triv_fib = (cof : arrow_class C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5b CM4b CM3.triv_fib
lemma triv_cof_eq_llp_with_fib : triv_cof = (fib : arrow_class C).llp_with :=
factorisation_axiom.eq_llp_with CM5a CM4a CM3.triv_cof
lemma fib_eq_rlp_with_triv_cof : fib = (triv_cof : arrow_class C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5a CM4a CM3.fib

lemma cof_comp_stable : (cof : arrow_class C).is_stable_by_composition :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.llp_with_is_stable_by_composition, }
lemma fib_comp_stable : (fib : arrow_class C).is_stable_by_composition :=
by { rw fib_eq_rlp_with_triv_cof, apply arrow_class.rlp_with_is_stable_by_composition, }

instance comp_weak_eq [hp : weak_eq p] [hq : weak_eq q] : weak_eq (p ≫ q) :=
⟨CM2.of_comp p q hp.mem hq.mem⟩
instance comp_cofibration [hp : cofibration p] [hq : cofibration q] : cofibration (p ≫ q) :=
⟨cof_comp_stable p q hp.mem hq.mem⟩
instance comp_fibration [hp : fibration p] [hq : fibration q] : fibration (p ≫ q) :=
⟨fib_comp_stable p q hp.mem hq.mem⟩

lemma cof_contains_iso : arrow_class.isomorphisms ⊆ (cof : arrow_class C) :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.isomorphisms_subset_llp_with, }
lemma fib_contains_iso : arrow_class.isomorphisms ⊆ (fib : arrow_class C) :=
by { rw fib_eq_rlp_with_triv_cof, apply arrow_class.isomorphisms_subset_rlp_with, }
lemma triv_cof_contains_iso : arrow_class.isomorphisms ⊆ (triv_cof : arrow_class C) :=
by { rw triv_cof_eq_llp_with_fib, apply arrow_class.isomorphisms_subset_llp_with, }
lemma triv_fib_contains_iso : arrow_class.isomorphisms ⊆ (triv_fib : arrow_class C) :=
by { rw triv_fib_eq_rlp_with_cof, apply arrow_class.isomorphisms_subset_rlp_with, }
lemma weq_contains_iso : arrow_class.isomorphisms ⊆ (weq : arrow_class C) := λ f hf,
(triv_cof_contains_iso hf).2

instance CM5a_cofibration : cofibration (CM5a.i f) := ⟨(CM5a.i_mem f).1⟩
instance CM5a_weak_eq : weak_eq (CM5a.i f) := ⟨(CM5a.i_mem f).2⟩
instance CM5a_fibration : fibration (CM5a.p f) := ⟨CM5a.p_mem f⟩

instance CM5b_cofibration : cofibration (CM5b.i f) := ⟨CM5b.i_mem f⟩
instance CM5b_fibration : fibration (CM5b.p f) := ⟨(CM5b.p_mem f).1⟩
instance CM5b_weak_eq : weak_eq (CM5b.p f) := ⟨(CM5b.p_mem f).2⟩

/-lemma cof_co_bc_stable : (cof : arrow_class D).is_stable_by_cobase_change :=
by { rw cof_equals_llp_triv_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }
lemma triv_cof_co_bc_stable : (triv_cof : arrow_class D).is_stable_by_cobase_change :=
by { rw triv_cof_equals_llp_fib, apply arrow_class.is_stable_by_cobase_change_of_llp_with, }-/

end model_category

end algebraic_topology