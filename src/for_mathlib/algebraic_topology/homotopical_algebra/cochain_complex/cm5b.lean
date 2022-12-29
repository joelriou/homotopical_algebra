/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a

open category_theory category_theory.category algebraic_topology

variables {C : Type*} [category C] [abelian C] [enough_projectives C]

namespace bounded_above_cochain_complex

namespace projective_model_structure

def CM5b : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5b :=
begin
  intro,
  sorry
end

def CM5 : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5 :=
  ⟨CM5a, CM5b⟩


end projective_model_structure

end bounded_above_cochain_complex
