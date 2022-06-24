/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.projective_model_structure

open category_theory category_theory.preadditive algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace bounded_above_cochain_complex

local attribute [instance] projective_model_structure


end bounded_above_cochain_complex
