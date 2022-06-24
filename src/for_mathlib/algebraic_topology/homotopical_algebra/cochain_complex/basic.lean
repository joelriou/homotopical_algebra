/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category
import for_mathlib.category_theory.preadditive.mono_with_projective_coker
--import category_theory.abelian.basic
--import category_theory.preadditive.projective
--import algebra.homology.homological_complex
import algebra.homology.quasi_iso
--import for_mathlib.category_theory.limits.kernel_functor
import for_mathlib.algebra.homology.twist_cocycle
--import tactic.linarith

noncomputable theory

open category_theory category_theory.limits category_theory.category
open algebraic_topology cochain_complex.hom_complex category_theory.preadditive

open_locale zero_object

variables (C : Type*) [category C]

namespace cochain_complex

variables (α : Type*) [add_right_cancel_semigroup α] [has_one α]

def quasi_isomorphisms [has_zero_morphisms C] [has_cokernels C] [has_images C] [has_equalizers C]
  [has_zero_object C] [has_image_maps C] :
  arrow_class (cochain_complex C α) :=
λ w, quasi_iso w.hom

namespace quasi_isomorphisms

lemma mem_iff [has_zero_morphisms C] [has_cokernels C] [has_images C] [has_equalizers C]
  [has_zero_object C] [has_image_maps C] {X Y : cochain_complex C α} (f : X ⟶ Y) :
  arrow.mk f ∈ quasi_isomorphisms C α ↔ quasi_iso f := by refl

end quasi_isomorphisms

def degreewise_epi [preadditive C] : arrow_class (cochain_complex C α) :=
λ w, ∀ n, epi (w.hom.f n)

def degreewise_mono_with_projective_coker [preadditive C] :
  arrow_class (cochain_complex C α) :=
λ w, ∀ n, arrow.mk (w.hom.f n) ∈ mono_with_projective_coker C

@[simps]
def projective_structure.arrow_classes [abelian C] :
  category_with_fib_cof_weq (cochain_complex C ℤ) :=
{ weq := quasi_isomorphisms C ℤ,
  fib := degreewise_epi C ℤ,
  cof := degreewise_mono_with_projective_coker C ℤ, }

end cochain_complex

@[derive category]
def bounded_above_cochain_complex [preadditive C] := { K : cochain_complex C ℤ // K.is_bounded_above }

namespace bounded_above_cochain_complex

variable {C}

def ι [preadditive C] :
  bounded_above_cochain_complex C ⥤ cochain_complex C ℤ := full_subcategory_inclusion _

variable (C)

@[simps]
def projective_model_structure.arrow_classes [abelian C] :
  category_with_fib_cof_weq (bounded_above_cochain_complex C) :=
category_with_fib_cof_weq.inverse_image (cochain_complex.projective_structure.arrow_classes C)
  bounded_above_cochain_complex.ι

end bounded_above_cochain_complex
