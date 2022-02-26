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

@[simp]
def cofibrant (A : M.C) : Prop := M.cofibrations.contains (initial.to A)

@[simp]
def fibrant (A : M.C) : Prop := M.fibrations.contains (terminal.from A)

lemma cofibrant_of_cofibration_from_initial {A B : M.C} (i : A ⟶ B)
  (hi : M.cofibrations.contains i) (hA : is_initial A) : cofibrant B :=
begin
  have h : initial.to B = initial.to A ≫ i := subsingleton.elim _ _,
  dsimp only [cofibrant],
  rw h,
  apply M.cof_comp_stable,
  { apply M.cof_contains_iso,
    exact is_iso.of_iso (is_initial.unique_up_to_iso initial_is_initial hA), },
  { exact hi, },
end

lemma fibrant_of_fibration_to_terminal {X Y : M.C} (p : X ⟶ Y)
  (hp : M.fibrations.contains p) (hY : is_terminal Y) : fibrant X :=
begin
  have h : terminal.from X = p ≫ terminal.from Y := subsingleton.elim _ _,
  dsimp only [fibrant],
  rw h,
  apply M.fib_comp_stable,
  { exact hp, },
  { apply M.fib_contains_iso,
    exact is_iso.of_iso (is_terminal.unique_up_to_iso hY terminal_is_terminal), }
end

lemma cofibrant_iff_op (A : M.C) : cofibrant A ↔ fibrant (M.op_obj A) :=
begin
  split,
  { intro hA,
    dsimp only [fibrant, model_category.op_obj],
    sorry, },
  { intro hA,
    apply cofibrant_of_cofibration_from_initial _ hA,
    apply initial_unop_of_terminal,
    exact terminal_is_terminal, },
end


end model_category

end algebraic_topology