/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category

noncomputable theory

open category_theory category_theory.limits opposite

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C] (A B X Y : C)
include M

abbreviation is_cofibrant (B : C) := cofibration (initial.to B)
abbreviation is_fibrant (B : C) := fibration (terminal.from B)

variables {A B X Y}

namespace cofibration

lemma from_initial (f : A ⟶ B) [is_cofibrant B] (hA : is_initial A) : cofibration f :=
begin
  have fac : f = (is_initial.unique_up_to_iso hA initial_is_initial).hom ≫ initial.to B :=
    by apply hA.hom_ext,
  rw fac,
  apply_instance,
end

end cofibration

namespace fibration

lemma from_terminal (f : X ⟶ Y) [is_fibrant X] (hY : is_terminal Y) : fibration f :=
begin
  have fac : f = terminal.from X ≫ (is_terminal.unique_up_to_iso terminal_is_terminal hY).hom :=
    by apply hY.hom_ext,
  rw fac,
  apply_instance,
end

end fibration

namespace is_cofibrant

def of_initial (hA : is_initial A) : is_cofibrant A :=
begin
  change cofibration (initial.to A),
  rw [show initial.to A = (is_initial.unique_up_to_iso initial_is_initial hA).hom,
    by apply subsingleton.elim],
  apply_instance,
end

def mk (f : A ⟶ B) [cofibration f] (hA : is_initial A) : is_cofibrant B :=
begin
  change cofibration (initial.to B),
  rw [show initial.to B = initial.to A ≫ f, by apply subsingleton.elim],
  haveI : is_cofibrant A := of_initial hA,
  apply_instance,
end

end is_cofibrant

namespace is_fibrant

def of_terminal (hY : is_terminal Y) : is_fibrant Y :=
begin
  change fibration (terminal.from Y),
  rw [show terminal.from Y = (is_terminal.unique_up_to_iso hY terminal_is_terminal).hom,
    by apply subsingleton.elim],
  apply_instance,
end

def mk (f : X ⟶ Y) [fibration f] (hY : is_terminal Y) : is_fibrant X :=
begin
  change fibration (terminal.from X),
  rw [show terminal.from X = f ≫ terminal.from Y, by apply subsingleton.elim],
  haveI : is_fibrant Y := of_terminal hY,
  apply_instance,
end

lemma op (hX : is_fibrant X) : is_cofibrant (op X) :=
begin
  haveI : cofibration (terminal.from X).op := fibration.op infer_instance,
  exact is_cofibrant.mk (terminal.from X).op (initial_op_of_terminal terminal_is_terminal),
end

lemma unop {X : Cᵒᵖ} (hX : is_fibrant X) : is_cofibrant X.unop :=
begin
  haveI : cofibration (terminal.from X).unop := fibration.unop infer_instance,
  exact is_cofibrant.mk (terminal.from X).unop (initial_unop_of_terminal terminal_is_terminal),
end

end is_fibrant

namespace is_cofibrant

lemma op (hB : is_cofibrant B) : is_fibrant (op B) :=
begin
  haveI : fibration (initial.to B).op := cofibration.op infer_instance,
  exact is_fibrant.mk (initial.to B).op (terminal_op_of_initial initial_is_initial),
end

lemma unop {B : Cᵒᵖ} (hB : is_cofibrant B) : is_fibrant B.unop :=
begin
  haveI : fibration (initial.to B).unop := cofibration.unop infer_instance,
  exact is_fibrant.mk (initial.to B).unop (terminal_unop_of_initial initial_is_initial),
end

end is_cofibrant

end model_category

end algebraic_topology