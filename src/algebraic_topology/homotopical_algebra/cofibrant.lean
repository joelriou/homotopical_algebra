/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category

noncomputable theory

open category_theory
open category_theory.limits
open algebraic_topology

variables {M : model_category}

namespace algebraic_topology

namespace model_category

class is_cofibrant (A : M.C) := (cof : arrow.mk (initial.to A) ∈ M.cof)

class is_fibrant (A : M.C) := (fib : arrow.mk (terminal.from A) ∈ M.fib)

lemma arrow_iso_of_map_from_initial {I A : M.C} (hI : is_initial I) (f : I ⟶ A) :
  arrow.mk (initial.to A) ≅ arrow.mk f :=
begin
  refine arrow.mk_iso _ (iso.refl _) _,
  { exact is_initial.unique_up_to_iso initial_is_initial hI, },
  { dsimp, apply subsingleton.elim, },
end

lemma arrow_iso_of_map_to_terminal {T A : M.C} (hT : is_terminal T) (f : A ⟶ T) :
  arrow.mk f ≅ arrow.mk (terminal.from A) :=
begin
  refine arrow.mk_iso (iso.refl _) _ _,
  { exact is_terminal.unique_up_to_iso hT terminal_is_terminal, },
  { dsimp, apply subsingleton.elim, },
end

lemma is_cofibrant_equiv_of_map_from_initial {I A : M.C} (hI : is_initial I) (f : I ⟶ A) :
  is_cofibrant A ≃ (arrow.mk f ∈ M.cof) :=
{ to_fun := λ h, begin
    rw ← M.cof_iff_of_arrow_iso _ _ (arrow_iso_of_map_from_initial hI f),
    exact h.cof,
  end,
  inv_fun := λ h, begin
    rw ← M.cof_iff_of_arrow_iso _ _ (arrow_iso_of_map_from_initial hI f) at h,
    exact ⟨h⟩,
  end,
  left_inv := λ h, by { rcases h with ⟨w⟩, refl, },
  right_inv := λ h, rfl }

lemma is_fibrant_equiv_of_map_to_terminal {T A : M.C} (hT : is_terminal T) (f : A ⟶ T) :
  is_fibrant A ≃ (arrow.mk f ∈ M.fib) :=
{ to_fun := λ h, begin
    rw M.fib_iff_of_arrow_iso _ _ (arrow_iso_of_map_to_terminal hT f),
    exact h.fib,
  end,
  inv_fun := λ h, begin
    rw M.fib_iff_of_arrow_iso _ _ (arrow_iso_of_map_to_terminal hT f) at h,
    exact ⟨h⟩,
  end,
  left_inv := λ h, by { rcases h with ⟨w⟩, refl, },
  right_inv := λ h, rfl }

lemma is_cofibrant_equiv_op (A : M.C) : is_cofibrant A ≃ is_fibrant (M.op_obj A) :=
begin
  let ι := initial.to A,
  calc is_cofibrant A ≃ arrow.mk ι ∈ M.cof :
            is_cofibrant_equiv_of_map_from_initial initial_is_initial ι
  ... ≃ arrow.mk ι.op ∈ M.op.fib : by refl
  ... ≃ is_fibrant (M.op_obj A) : (is_fibrant_equiv_of_map_to_terminal _ _).symm,
  { refine terminal_op_of_initial initial_is_initial, },
end

lemma is_fibrant_equiv_op (A : M.C) : is_fibrant A ≃ is_cofibrant (M.op_obj A) :=
begin
  let π := terminal.from A,
  calc is_fibrant A ≃ arrow.mk π ∈ M.fib :
            is_fibrant_equiv_of_map_to_terminal terminal_is_terminal π
  ... ≃ arrow.mk π.op ∈ M.op.cof : by refl
  ... ≃ is_cofibrant (M.op_obj A) : (is_cofibrant_equiv_of_map_from_initial _ _).symm,
  { refine initial_op_of_terminal terminal_is_terminal, },
end

end model_category

end algebraic_topology
