/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm1
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a
import for_mathlib.algebra.homology.termwise_split
import for_mathlib.algebra.homology.lifting

noncomputable theory

open category_theory category_theory.category algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace bounded_above_cochain_complex

namespace projective_model_structure

open cochain_complex.hom_complex

section

variables {A B : bounded_above_cochain_complex C} (i : A ⟶ B) (hi : arrow_classes.cof i)
include hi

def cof_quotient : bounded_above_cochain_complex C := limits.cokernel i

def splittings_of_cof (n : ℤ) : splitting (i.f n) ((limits.cokernel.π i).f n) :=
begin
  sorry,
end

def cocycle_of_cof : cocycle (limits.cokernel i).obj A.obj 1 :=
twist.iso_of_termwise_split.z (splittings_of_cof i hi)

def iso_twist_of_cof : twist (cocycle_of_cof i hi) ≅ B.obj :=
twist.iso_of_termwise_split (splittings_of_cof i hi)

def arrow_iso_of_cof : arrow.mk (twist.inr (cocycle_of_cof i hi)) ≅ arrow.mk (ι.map i) := sorry

end

def CM4a : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4a :=
λ A B X Y i hi p hp, begin
  --cochain_complex.lifting.lift_of_coboundary
  sorry,
end

def CM4b : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4b := sorry

def CM4 : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4 :=
  ⟨CM4a, CM4b⟩

end projective_model_structure

end bounded_above_cochain_complex
