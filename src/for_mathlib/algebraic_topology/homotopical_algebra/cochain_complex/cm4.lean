/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a

open category_theory category_theory.category algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace bounded_above_cochain_complex

namespace projective_model_structure

def CM4a : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4a := sorry
def CM4b : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4b := sorry

def CM4 : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM4 :=
  ⟨CM4a, CM4b⟩

end projective_model_structure

end bounded_above_cochain_complex
