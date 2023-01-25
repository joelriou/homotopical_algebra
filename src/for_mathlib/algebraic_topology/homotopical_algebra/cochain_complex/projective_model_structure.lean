/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm1
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm2
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm3
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm4
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5b

noncomputable theory

open category_theory category_theory.preadditive algebraic_topology

variables {C : Type*} [category C] [abelian C] [enough_projectives C]

namespace cochain_complex

namespace minus

@[simps]
def projective_model_structure : model_category (cochain_complex.minus C) :=
{ to_category_with_fib_cof_weq := projective_model_structure.arrow_classes C,
  CM1axiom := projective_model_structure.CM1,
  CM2axiom := projective_model_structure.CM2,
  CM3axiom := projective_model_structure.CM3,
  CM4axiom := projective_model_structure.CM4,
  CM5axiom := projective_model_structure.CM5, }

end minus

end cochain_complex
