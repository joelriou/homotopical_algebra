/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cylinder

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.category
open algebraic_topology

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]

include M

structure brown_factorisation_triv_cof {X Y : C} (f : X ⟶ Y) :=
(Z : C) (i : X ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
(fac₁ : f = i ≫ p)
(fac₂ : s ≫ p = 𝟙 _)
(triv_cof_i : arrow.mk i ∈ (triv_cof : arrow_class C))
(triv_cof_s : arrow.mk s ∈ (triv_cof : arrow_class C))
(triv_fib_p : arrow.mk p ∈ (triv_fib : arrow_class C))

lemma exists_brown_factorisation_W_between_cofibrant_objects {X Y : C} [hX : is_cofibrant X] [hY : is_cofibrant Y]
  (f : X ⟶ Y) (hf : arrow.mk f ∈ (W : arrow_class C)) :
  nonempty (brown_factorisation_triv_cof f) :=
begin
  rcases CM5b (arrow.mk (coprod.desc f (𝟙 Y))) with ⟨Z, j, p, fac, ⟨hj, hp⟩⟩,
  dsimp at fac,
  exact nonempty.intro
  { Z := Z,
    i := coprod.inl ≫ j,
    p := p,
    s := coprod.inr ≫ j,
    fac₁ := by rw [assoc, ← fac, coprod.inl_desc],
    fac₂ := by rw [assoc, ← fac, coprod.inr_desc],
    triv_cof_i := begin
      split,
      { have h := cof_co_bc_stable.for_coprod_inl X Y hY.cof,
        exact cof_comp_stable _ _ _ coprod.inl j h hj, },
      { apply CM2.of_comp_right _ p hp.2,
        rw [assoc, ← fac, coprod.inl_desc],
        exact hf, },
    end,
    triv_cof_s := begin
      split,
      { have h := cof_co_bc_stable.for_coprod_inr X Y hX.cof,
        exact cof_comp_stable _ _ _ coprod.inr j h hj, },
      { apply CM2.of_comp_right _ p hp.2,
        rw [assoc, ← fac, coprod.inr_desc],
        apply W_contains_iso,
        exact is_iso.of_iso (iso.refl _), },
    end,
    triv_fib_p := hp },
end

end model_category

end algebraic_topology