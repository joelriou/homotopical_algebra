/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.abelian.basic
import category_theory.preadditive.projective
import algebraic_topology.homotopical_algebra.model_category
import algebra.homology.homological_complex
import algebra.homology.quasi_iso

open category_theory category_theory.limits
open algebraic_topology

variables (C : Type*) [category C] [abelian C] [enough_projectives C]

namespace algebra

namespace homology

@[derive category]
def Cminus := { K : chain_complex C ℤ // ∃ (r : ℤ), ∀ (i : ℤ) (hi : i < r), nonempty (is_initial (K.X i)) }

namespace projective_structure

def Cminus_fib_cof_W : category_with_fib_cof_W (Cminus C) :=
{ W := λ w, quasi_iso w.hom,
  fib := λ w, ∀ (i : ℤ), epi (w.hom.f i),
  cof := λ w, ∀ (i : ℤ), mono (w.hom.f i) ∧ (projective (cokernel (w.hom.f i))) }

variable {C}

def CM1a : has_finite_limits (Cminus C) := sorry
def CM1b : has_finite_colimits (Cminus C) := sorry
def CM2 : (Cminus_fib_cof_W C).CM2 := sorry
def CM3 : (Cminus_fib_cof_W C).CM3 := sorry
def CM4 : (Cminus_fib_cof_W C).CM4 := sorry
def CM5 : (Cminus_fib_cof_W C).CM5 := sorry

variable (C)

def model : model_category :=
{ C := Cminus C,
  fib_cof_we := Cminus_fib_cof_W C,
  CM1 := ⟨CM1a, CM1b⟩,
  CM2 := CM2,
  CM3 := CM3,
  CM4 := CM4,
  CM5 := CM5 }

end projective_structure

end homology

end algebra

