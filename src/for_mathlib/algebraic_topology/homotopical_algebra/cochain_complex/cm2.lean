/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic

open category_theory category_theory.preadditive algebraic_topology

variables (C : Type*) [category C] [abelian C]

namespace cochain_complex

lemma three_of_two_quasi_isomorphisms {ι : Type*} (c : complex_shape ι):
  (quasi_isomorphisms C c).three_of_two :=
{ of_comp := λ X Y Z f g hf hg, begin
    rw mem_quasi_isomorphisms_iff at hf hg ⊢,
    haveI := hf,
    haveI := hg,
    exact quasi_iso_comp f g,
  end,
  of_comp_left := λ X Y Z f g hf hfg, begin
    rw mem_quasi_isomorphisms_iff at hf hfg ⊢,
    haveI := hf,
    haveI := hfg,
    exact quasi_iso_of_comp_left f g,
  end,
  of_comp_right := λ X Y Z f g hg hfg, begin
    rw mem_quasi_isomorphisms_iff at hg hfg ⊢,
    haveI := hg,
    haveI := hfg,
    exact quasi_iso_of_comp_right f g,
  end, }

namespace minus

namespace projective_model_structure

variable {C}

def CM2 : (arrow_classes C).CM2 :=
morphism_property.three_of_two.for_inverse_image
  (three_of_two_quasi_isomorphisms C (complex_shape.up ℤ)) _

end projective_model_structure

end minus

end cochain_complex
