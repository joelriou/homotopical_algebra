/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic

open category_theory category_theory.preadditive algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace cochain_complex

namespace projective_structure

def CM2 : (arrow_classes C).CM2 :=
{ of_comp := λ X Y Z f g hf hg, begin
    dsimp at hf hg ⊢,
    rw quasi_isomorphisms.mem_iff at hf hg ⊢,
    haveI := hf,
    haveI := hg,
    exact quasi_iso_comp f g,
  end,
  of_comp_left := λ X Y Z f g hf hfg, begin
    dsimp at hf hfg ⊢,
    rw quasi_isomorphisms.mem_iff at hf hfg ⊢,
    haveI := hf,
    haveI := hfg,
    exact quasi_iso_of_comp_left f g,
  end,
  of_comp_right := λ X Y Z f g hg hfg, begin
    dsimp at hg hfg ⊢,
    rw quasi_isomorphisms.mem_iff at hg hfg ⊢,
    haveI := hg,
    haveI := hfg,
    exact quasi_iso_of_comp_right f g,
  end, }

end projective_structure

end cochain_complex

namespace bounded_above_cochain_complex

namespace projective_structure

def CM2 : (arrow_classes C).CM2 :=
category_with_fib_cof_weq.CM2.inverse_image (cochain_complex.projective_structure.CM2) bounded_above_cochain_complex.ι

end projective_structure

end bounded_above_cochain_complex
