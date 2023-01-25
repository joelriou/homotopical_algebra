/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm1
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a
import for_mathlib.algebra.homology.termwise_split
import for_mathlib.algebra.homology.lifting

noncomputable theory

open category_theory category_theory.category algebraic_topology

namespace category_theory

variables {C D : Type*} [category C] [category D]
  {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)

lemma has_lifting_property.iff_of_fully_faithful (F : C ⥤ D)
  [full F] [faithful F] :
  has_lifting_property (F.map i) (F.map p) ↔
    has_lifting_property i p :=
begin
  split,
  { introI,
    exact ⟨λ f g sq, ⟨⟨{ l := F.preimage ((sq.map F).lift),
      fac_left' := F.map_injective (by simp),
      fac_right' := F.map_injective (by simp), }⟩⟩⟩, },
  { introI,
    refine ⟨λ f g sq, _⟩,
    have sq' : comm_sq (F.preimage f) i p (F.preimage g) :=
      ⟨F.map_injective (by simp only [functor.map_comp, functor.image_preimage, sq.w])⟩,
    exact ⟨⟨{ l := F.map sq'.lift,
      fac_left' :=
        by simpa only [F.map_comp, F.image_preimage] using F.congr_map sq'.fac_left,
      fac_right' :=
        by simpa only [F.map_comp, F.image_preimage] using F.congr_map sq'.fac_right, }⟩⟩, },
end

end category_theory

variables {C : Type*} [category C] [abelian C]

namespace cochain_complex

namespace minus

namespace projective_model_structure

open cochain_complex.hom_complex

section

variables {A B : minus C} (i : A ⟶ B) (hi : (arrow_classes C).cof i)
include hi

def splittings_of_cof (n : ℤ) : splitting (i.f n) ((limits.cokernel.π i).f n) :=
begin
-- show that it is a short_exact sequence
-- show that the cokernel is projective
-- then there is a splitting...
  sorry,
end

def cocycle_of_cof : cocycle (limits.cokernel i).obj A.obj 1 :=
twist.iso_of_termwise_split.z (splittings_of_cof i hi)

def iso_twist_of_cof : twist (cocycle_of_cof i hi) ≅ B.obj :=
twist.iso_of_termwise_split (splittings_of_cof i hi)

def arrow_iso_of_cof : arrow.mk (twist.inr (cocycle_of_cof i hi)) ≅ arrow.mk (ι.map i) := sorry

end

def CM4a : (arrow_classes C).CM4a :=
λ A B X Y i hi p hp, begin
  --has_lifting_property.iff_of_arrow_iso_left (arrow_iso_of_cof i hi.1) p,
  --cochain_complex.lifting.lift_of_coboundary
  sorry,
end

def CM4b : (arrow_classes C).CM4b := sorry

def CM4 : (arrow_classes C).CM4 :=
  ⟨CM4a, CM4b⟩

end projective_model_structure

end minus

end cochain_complex
