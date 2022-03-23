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
import algebraic_topology.homotopical_algebra.misc

open category_theory category_theory.limits category_theory.category
open algebraic_topology

noncomputable theory

variables {C : Type*} [category C]

namespace category_theory

namespace projective

lemma of_retract {P Q : C} (hPQ : is_retract P Q) (hQ : projective Q) : projective P :=
begin
  refine ⟨_⟩,
  intros E X f e,
  introI,
  rcases hPQ with ⟨s, r, hsr⟩,
  have hQ' := hQ.1,
  cases hQ' (r ≫ f) e with g hg,
  use s ≫ g,
  rw [assoc, hg, ← assoc, hsr, id_comp],
end

end projective

end category_theory

variables [abelian C] [enough_projectives C]

namespace algebra

namespace homology

variable (C)

@[derive category]
def Cminus := { K : chain_complex C ℤ // ∃ (r : ℤ), ∀ (i : ℤ) (hi : i < r), nonempty (is_initial (K.X i)) }

namespace Cminus

variable {C}

def homology_functor (i : ℤ) : Cminus C ⥤ C := induced_functor _ ⋙ homology_functor _ _ i

def eval (i : ℤ) : Cminus C ⥤ C := induced_functor _ ⋙ homological_complex.eval _ _ i

namespace projective_structure

variable (C)

def Cminus_fib_cof_W : category_with_fib_cof_W (Cminus C) :=
{ W := λ w, quasi_iso w.hom,
  fib := λ w, ∀ (i : ℤ), epi (w.hom.f i),
  cof := λ w, ∀ (i : ℤ), mono (w.hom.f i) ∧ (projective (cokernel (w.hom.f i))), }

variable {C}

def CM1a : has_finite_limits (Cminus C) := sorry
def CM1b : has_finite_colimits (Cminus C) := sorry

def CM2 : (Cminus_fib_cof_W C).CM2 :=
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
def CM3 : (Cminus_fib_cof_W C).CM3 :=
{ W := λ f f' hf' hff', ⟨λ i, begin
    refine arrow_class.is_stable_by_retract.for_isomorphisms _ _ _
      (is_retract_imp_of_functor (homology_functor i).map_arrow f f' hff'),
    apply hf'.1,
  end⟩,
  cof := λ f f' hf' hff' i, begin
    split,
    { exact arrow_class.is_stable_by_retract.for_monomorphisms _ _ (by exact (hf' i).1)
      (is_retract_imp_of_functor (eval i).map_arrow f f' hff'), },
    { apply category_theory.projective.of_retract _ (hf' i).2,
      sorry, },
  end,
  fib := λ f f' hf' hff' i, arrow_class.is_stable_by_retract.for_epimorphisms _ _ (by exact hf' i)
      (is_retract_imp_of_functor (eval i).map_arrow f f' hff'), }
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

end Cminus

end homology

end algebra

