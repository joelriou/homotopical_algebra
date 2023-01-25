/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category
import for_mathlib.category_theory.preadditive.mono_with_projective_coker
import algebra.homology.quasi_iso
import for_mathlib.algebra.homology.derived_category_plus

noncomputable theory

open category_theory category_theory.limits category_theory.category
open algebraic_topology cochain_complex.hom_complex category_theory.preadditive

open_locale zero_object

variables (C : Type*) [category C] [abelian C]

namespace cochain_complex

namespace minus

namespace projective_model_structure

variable {C}

def weq : morphism_property (cochain_complex.minus C) :=
(quasi_isomorphisms C (complex_shape.up ℤ)).inverse_image cochain_complex.minus.ι

lemma mem_weq_iff {X Y : cochain_complex.minus C} (f : X ⟶ Y) :
  weq f ↔ quasi_iso (ι.map f) :=
⟨λ h, ⟨λ n, h n⟩, λ h, h.is_iso⟩

def cof : morphism_property (cochain_complex.minus C) :=
λ X Y f, ∀ n, mono_with_projective_coker C (f.f n)

lemma cof_is_stable_under_composition :
  (cof : morphism_property (cochain_complex.minus C)).stable_under_composition :=
λ X Y Z f g hf hg n,
mono_with_projective_coker.is_stable_by_composition _ _ _ (hf _) (hg _)

def fib : morphism_property (cochain_complex.minus C) :=
λ X Y f, ∀ (n : ℤ), epi (f.f n)

variable (C)

@[simps]
def arrow_classes :
  category_with_fib_cof_weq (cochain_complex.minus C) :=
{ weq := weq,
  fib := fib,
  cof := cof, }

end projective_model_structure

end minus

end cochain_complex
