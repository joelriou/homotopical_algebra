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

def CM3 : (arrow_classes C).CM3 :=
{ weq := λ X₁ X₂ Y₁ Y₂ f g hfg hg, ⟨λ n, begin
    have hfg' := is_retract.imp_of_functor (homology_functor _ _ n).map_arrow _ _ hfg,
    apply arrow_class.is_stable_by_retract.for_isomorphisms _ _ hfg',
    apply hg.1,
  end⟩,
  cof := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, mono_with_projective_coker.is_stable_by_retract C _ _
    (is_retract.imp_of_functor (homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n),
  fib := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, arrow_class.is_stable_by_retract.for_epimorphisms _ _
    (is_retract.imp_of_functor (homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n), }

end projective_structure

end cochain_complex

namespace bounded_above_cochain_complex

namespace projective_structure

def CM3 : (arrow_classes C).CM3 :=
category_with_fib_cof_weq.CM3.inverse_image (cochain_complex.projective_structure.CM3) bounded_above_cochain_complex.ι

end projective_structure

end bounded_above_cochain_complex
