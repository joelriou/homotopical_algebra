/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category
import category_theory.abelian.basic
import category_theory.preadditive.projective
import algebra.homology.homological_complex
import algebra.homology.quasi_iso

open category_theory category_theory.limits category_theory.category
open algebraic_topology

noncomputable theory

namespace algebra

namespace homology

variables {C : Type*} [category C] [abelian C]

namespace chain_complex

def projective_structure : category_with_fib_cof_weq (chain_complex C ℕ) :=
{ weq := λ w, quasi_iso w.hom,
  fib := λ w, ∀ i, epi (w.hom.f i),
  cof := λ w, ∀ i, mono (w.hom.f i) ∧ (projective (cokernel (w.hom.f i))), }

namespace projective_structure

instance : model_category (chain_complex C ℕ) :=
{ to_category_with_fib_cof_weq := projective_structure,
  CM1axiom := sorry,
  CM2axiom := sorry,
  CM3axiom := sorry,
  CM4axiom := sorry,
  CM5axiom := sorry, }

end projective_structure

end chain_complex

end homology

end algebra
