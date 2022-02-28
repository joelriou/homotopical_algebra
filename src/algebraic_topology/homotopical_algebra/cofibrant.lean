/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category

open category_theory
open category_theory.limits
open algebraic_topology

variables {M : model_category}

namespace algebraic_topology

namespace model_category

@[simp]
def cofibrant (A : M.C) : Prop := arrow.mk (initial.to A) ∈ M.cofibrations

@[simp]
def fibrant (A : M.C) : Prop := arrow.mk (terminal.from A) ∈ M.fibrations

lemma cofibrant_of_cofibration_from_initial (i : arrow M.C)
  (hi₁ : i ∈ M.cofibrations) (hi₂ : is_initial i.left) : cofibrant i.right :=
begin
  have h : initial.to i.right = initial.to i.left ≫ i.hom := subsingleton.elim _ _,
  dsimp only [cofibrant],
  rw h,
  apply M.cof_comp_stable,
  { apply M.cof_contains_iso,
    exact is_iso.of_iso (is_initial.unique_up_to_iso initial_is_initial hi₂), },
  { rw arrow.mk_eq, exact hi₁, },
end

lemma fibrant_of_fibration_to_terminal (p : arrow M.C)
  (hp₁ : p ∈ M.fibrations) (hp₂ : is_terminal p.right) : fibrant p.left :=
begin
  have h : terminal.from p.left = p.hom ≫ terminal.from p.right := subsingleton.elim _ _,
  dsimp only [fibrant],
  rw h,
  apply M.fib_comp_stable,
  { rw arrow.mk_eq, exact hp₁, },
  { apply M.fib_contains_iso,
    exact is_iso.of_iso (is_terminal.unique_up_to_iso hp₂ terminal_is_terminal), }
end

lemma cofibrant_iff_op (A : M.C) : cofibrant A ↔ fibrant (M.op_obj A) :=
begin
  split,
  { intro hA,
    dsimp only [fibrant],
    erw [arrow_class.mem_op_iff M.cofibrations, arrow.unop_mk],
    convert M.cof_comp_stable _ _ _ (terminal.from (opposite.op (⊥_ M.C))).unop (initial.to A) _ hA, swap,
    { apply M.cof_contains_iso,
      rw [← arrow.unop_mk, ← arrow_class.mem_op_iff,
        arrow_class.op_isomorphisms_eq, arrow_class.mem_isomorphisms_iff],
      let e : (opposite.op (⊥_ M.C)) ≅ ⊤_ _ := is_terminal.unique_up_to_iso
        (terminal_op_of_initial initial_is_initial) terminal_is_terminal,
      convert is_iso.of_iso e, },
    apply quiver.hom.op_inj,
    simp only [quiver.hom.op_unop, op_comp],
    apply is_terminal.hom_ext,
    exact terminal_is_terminal, },
  { intro hA,
    apply cofibrant_of_cofibration_from_initial _ hA,
    dsimp,
    apply initial_unop_of_terminal,
    exact terminal_is_terminal, },
end

lemma fibrant_iff_op (A : M.C) : fibrant A ↔ cofibrant (M.op_obj A) := sorry

end model_category

end algebraic_topology
