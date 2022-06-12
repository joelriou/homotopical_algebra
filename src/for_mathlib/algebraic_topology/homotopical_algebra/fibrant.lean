/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category

noncomputable theory

open category_theory category_theory.limits

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

end model_category

end algebraic_topology