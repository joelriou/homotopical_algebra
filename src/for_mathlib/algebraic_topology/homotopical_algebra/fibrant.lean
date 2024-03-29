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

variables {C : Type*} [category C] [model_category C] (A B X Y : C)

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

lemma of_initial (hA : is_initial A) : is_cofibrant A :=
begin
  change cofibration (initial.to A),
  rw [show initial.to A = (is_initial.unique_up_to_iso initial_is_initial hA).hom,
    by apply subsingleton.elim],
  apply_instance,
end

lemma mk (f : A ⟶ B) [cofibration f] (hA : is_initial A) : is_cofibrant B :=
begin
  change cofibration (initial.to B),
  rw [show initial.to B = initial.to A ≫ f, by apply subsingleton.elim],
  haveI : is_cofibrant A := of_initial hA,
  apply_instance,
end

end is_cofibrant

namespace is_fibrant

lemma of_terminal (hY : is_terminal Y) : is_fibrant Y :=
begin
  change fibration (terminal.from Y),
  rw [show terminal.from Y = (is_terminal.unique_up_to_iso hY terminal_is_terminal).hom,
    by apply subsingleton.elim],
  apply_instance,
end

lemma mk (f : X ⟶ Y) [fibration f] (hY : is_terminal Y) : is_fibrant X :=
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

instance cofibration_coprod_inl [hB : is_cofibrant B] : cofibration (coprod.inl : A ⟶ A ⨿ B) :=
⟨cof_is_stable_under_cobase_change.coprod_inl A B hB.property⟩

instance cofibration_coprod_inr [hA : is_cofibrant A] : cofibration (coprod.inr : B ⟶ A ⨿ B) :=
⟨cof_is_stable_under_cobase_change.coprod_inr A B hA.property⟩

instance fibration_prod_fst [hY : is_fibrant Y] : fibration (limits.prod.fst : X ⨯ Y ⟶ X) :=
⟨fib_is_stable_under_base_change.prod_fst X Y hY.property⟩

instance fibration_prod_snd [hX : is_fibrant X] : fibration (limits.prod.snd : X ⨯ Y ⟶ Y) :=
⟨fib_is_stable_under_base_change.prod_snd X Y hX.property⟩

instance : is_fibrant (terminal C) :=
by { haveI : is_iso (terminal.from (terminal C)) := by convert is_iso.id _, apply_instance, }

instance : is_cofibrant (initial C) :=
by { haveI : is_iso (initial.to (initial C)) := by convert is_iso.id _, apply_instance, }

instance is_fibrant_CM5a_obj {X Y : C} (f : X ⟶ Y) [is_fibrant Y] :
  is_fibrant (CM5a.obj f) :=
begin
  change fibration _,
  have eq : terminal.from (factorisation_axiom.obj CM5a f) = (CM5a.p f) ≫ terminal.from _ :=
    subsingleton.elim _ _,
  rw eq,
  apply_instance,
end

instance is_fibrant_CM5b_obj {X Y : C} (f : X ⟶ Y) [is_fibrant Y] :
  is_fibrant (CM5b.obj f) :=
begin
  change fibration _,
  have eq : terminal.from (factorisation_axiom.obj CM5b f) = (CM5b.p f) ≫ terminal.from _ :=
    subsingleton.elim _ _,
  rw eq,
  apply_instance,
end

instance is_cofibrant_CM5a_obj {X Y : C} (f : X ⟶ Y) [is_cofibrant X] :
  is_cofibrant (CM5a.obj f) :=
begin
  change cofibration _,
  have eq : initial.to (factorisation_axiom.obj CM5a f) = initial.to _ ≫ (CM5a.i f) :=
    subsingleton.elim _ _,
  rw eq,
  apply_instance,
end

instance is_cofibrant_CM5b_obj {X Y : C} (f : X ⟶ Y) [is_cofibrant X] :
  is_cofibrant (CM5b.obj f) :=
begin
  change cofibration _,
  have eq : initial.to (factorisation_axiom.obj CM5b f) = initial.to _ ≫ (CM5b.i f) :=
    subsingleton.elim _ _,
  rw eq,
  apply_instance,
end

end model_category

end algebraic_topology
