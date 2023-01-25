/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic

open category_theory category_theory.preadditive algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace cochain_complex

namespace minus

namespace projective_model_structure

def CM3 : (arrow_classes C).CM3 :=
{ weq := λ X₁ X₂ Y₁ Y₂ f g hfg hg n,
    morphism_property.is_stable_by_retract.for_isomorphisms _ _
      (is_retract.imp_of_functor (minus.ι ⋙ homology_functor _ _ n).map_arrow _ _ hfg) (hg n),
  cof := λ X₁ X₂ Y₁ Y₂ f g hfg hg n,
    mono_with_projective_coker.is_stable_by_retract C  _ _
      (is_retract.imp_of_functor
        (minus.ι ⋙ homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n),
  fib := λ X₁ X₂ Y₁ Y₂ f g hfg hg n,
    morphism_property.is_stable_by_retract.for_epimorphisms _ _
      (is_retract.imp_of_functor
        (minus.ι ⋙ homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n), }

end projective_model_structure

end minus

end cochain_complex
