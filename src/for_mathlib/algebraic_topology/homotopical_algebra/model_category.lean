/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category_axioms

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

def CM1 := M.CM1axiom
def CM2 := M.CM2axiom
def CM3 := M.CM3axiom
def CM4 := M.CM4axiom
def CM5 := M.CM5axiom

def CM3a : M.to_category_with_fib_cof_weq.CM3a := CM3.W
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

variables {A B X Y Z : C} (f : X ⟶ Y)

class cofibration := (mem : arrow.mk f ∈ M.cof)
class fibration := (mem : arrow.mk f ∈ M.fib)
class weq := (mem : arrow.mk f ∈ M.W)

instance CM4a' (i : A ⟶ B) (p : X ⟶ Y) [hi₁ : cofibration i] [hi₂ : weq i] [hp : fibration p] :
  has_lifting_property_new i p := CM4a i ⟨hi₁.mem, hi₂.mem⟩ p hp.mem
instance CM4b' (i : A ⟶ B) (p : X ⟶ Y) [hi : cofibration i] [hp₁ : fibration p] [hp₂ : weq p] :
  has_lifting_property_new i p := CM4b i hi.mem p ⟨hp₁.mem, hp₂.mem⟩

instance comp_weq (f : X ⟶ Y) (g : Y ⟶ Z) [hf : weq f] [hg : weq g] : weq (f ≫ g) :=
⟨CM2.of_comp f g hf.mem hg.mem⟩

end model_category

end algebraic_topology