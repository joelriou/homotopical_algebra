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

lemma arrow.op_mk {T : Type*} [category T] {X Y : T} (f : X ⟶ Y) : (arrow.mk f).op = arrow.mk f.op :=
begin
  sorry
end

lemma arrow.unop_mk {T : Type*} [category T] {X Y : T} (f : opposite.op X ⟶ opposite.op Y) :
  (arrow.mk f).unop = arrow.mk f.unop :=
begin
  sorry
end

lemma cofibrant_iff_op (A : M.C) : cofibrant A ↔ fibrant (M.op_obj A) :=
begin
  split,
  { intro hA,
    dsimp only [model_category.op_obj, fibrant],
    erw arrow_class.mem_op_iff M.cofibrations,
    dsimp ,
    dsimp only [cofibrant] at hA,
--    dsimp only [model_category.op_obj],
    rw ← arrow.unop_op (arrow.mk _) at hA,
    rw ← arrow_class.mem_op_iff at hA,
    rw arrow.mk_op at hA,
--    apply fibrant_of_fibration_to_terminal _ hA,
    have pif := fibrant_of_fibration_to_terminal,
    dsimp,
--    have paf := fibrant_of_fibration_to_terminal _ _,
  --  dsimp only [fibrant, model_category.op_obj],
    --dsimp,
    --dsimp at hA,
   -- sorry,
   sorry,
     },
  { intro hA,
    apply cofibrant_of_cofibration_from_initial _ hA,
    dsimp,
    apply initial_unop_of_terminal,
    exact terminal_is_terminal, },
end


end model_category

end algebraic_topology