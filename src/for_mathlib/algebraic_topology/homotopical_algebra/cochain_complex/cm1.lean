/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic

open category_theory category_theory.limits

variables {C : Type*} [category C] [abelian C]

namespace bounded_above_cochain_complex

instance : has_finite_limits (bounded_above_cochain_complex C) := sorry
instance : has_finite_colimits (bounded_above_cochain_complex C) := sorry

namespace projective_model_structure

lemma CM1 : has_finite_limits (bounded_above_cochain_complex C) ∧
  has_finite_colimits (bounded_above_cochain_complex C) :=
⟨infer_instance, infer_instance⟩

end projective_model_structure

end bounded_above_cochain_complex
