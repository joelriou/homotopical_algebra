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
import for_mathlib.category_theory.limits.kernel_functor

open category_theory category_theory.limits category_theory.category
open algebraic_topology

noncomputable theory

namespace algebra

namespace homology

variables (C : Type*) [category C] [abelian C]

namespace chain_complex

def projective_structure : category_with_fib_cof_weq (chain_complex C ℕ) :=
{ weq := λ w, quasi_iso w.hom,
  fib := λ w, ∀ n, epi (w.hom.f n),
  cof := λ w, ∀ n, mono (w.hom.f n) ∧ (projective (cokernel (w.hom.f n))), }

variable {C}
namespace projective_structure

def CM2 : (projective_structure C).CM2 :=
{ of_comp := λ X Y Z f g (hf : quasi_iso f) (hg : quasi_iso g), begin
    haveI := hf,
    haveI := hg,
    exact quasi_iso_comp f g,
  end,
  of_comp_left := λ X Y Z f g (hf : quasi_iso f) (hfg : quasi_iso (f ≫ g)), begin
    haveI := hf,
    haveI := hfg,
    convert quasi_iso_of_comp_left f g,
  end,
  of_comp_right := λ X Y Z f g (hg : quasi_iso g) (hfg : quasi_iso (f ≫ g)), begin
    haveI := hg,
    haveI := hfg,
    convert quasi_iso_of_comp_right f g,
  end, }

def CM3 : (projective_structure C).CM3 :=
{ weq := λ X₁ X₂ Y₁ Y₂ f g hfg hg, ⟨λ n, begin
    have hfg' := is_retract.imp_of_functor (homology_functor _ _ n).map_arrow
      (arrow.mk f) (arrow.mk g) hfg,
    apply arrow_class.is_stable_by_retract.for_isomorphisms _ _ hfg',
    apply hg.1,
  end⟩,
  cof := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, begin
    split,
    { exact arrow_class.is_stable_by_retract.for_monomorphisms _ _ 
      (is_retract.imp_of_functor (homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n).1, },
    { exact projective.of_retract (is_retract.imp_of_functor
      ((homological_complex.eval _ _ n).map_arrow ⋙ limits.cokernel_functor C) _ _ hfg) (hg n).2, },
  end,
  fib := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, arrow_class.is_stable_by_retract.for_epimorphisms _ _ 
      (is_retract.imp_of_functor (homological_complex.eval _ _ n).map_arrow _ _ hfg) (hg n), }

def CM4 : (projective_structure C).CM4 := sorry
def CM5 : (projective_structure C).CM5 := sorry

instance : model_category (chain_complex C ℕ) :=
{ to_category_with_fib_cof_weq := projective_structure C,
  CM1axiom := sorry,
  CM2axiom := CM2,
  CM3axiom := CM3,
  CM4axiom := CM4,
  CM5axiom := CM5, }

end projective_structure

end chain_complex

end homology

end algebra
