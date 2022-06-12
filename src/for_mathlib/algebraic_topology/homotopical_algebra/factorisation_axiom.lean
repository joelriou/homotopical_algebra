/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.comm_sq_lift

noncomputable theory

open category_theory category_theory.category category_theory.limits opposite

namespace algebraic_topology

variables {C : Type*} [category C] (F G : arrow_class C) {F' G' : arrow_class Cᵒᵖ}

def factorisation_axiom :=
∀ ⦃X Z : C⦄ (f : X ⟶ Z), ∃ (Y : C) (i : X ⟶ Y) (hi : arrow.mk i ∈ F)
  (p : Y ⟶ Z) (hp : arrow.mk p ∈ G), i ≫ p = f

namespace factorisation_axiom

variables {X Y Z : C}

variables {F G}

def obj (h : factorisation_axiom F G) (f : X ⟶ Z) : C := (h f).some

def i (h : factorisation_axiom F G) (f : X ⟶ Z) : X ⟶ h.obj f := (h f).some_spec.some
def p (h : factorisation_axiom F G) (f : X ⟶ Z) : h.obj f ⟶ Z := (h f).some_spec.some_spec.some_spec.some

lemma i_mem (h : factorisation_axiom F G) (f : X ⟶ Z) : arrow.mk (h.i f) ∈ F :=
(h f).some_spec.some_spec.some
lemma p_mem (h : factorisation_axiom F G) (f : X ⟶ Z) : arrow.mk (h.p f) ∈ G :=
(h f).some_spec.some_spec.some_spec.some_spec.some

@[simp, reassoc]
lemma fac (h : factorisation_axiom F G) (f : X ⟶ Z) : (h.i f) ≫ (h.p f) = f :=
(h f).some_spec.some_spec.some_spec.some_spec.some_spec

lemma op (h : factorisation_axiom F G) : factorisation_axiom G.op F.op :=
λ X Z f,
begin
  rcases h f.unop with ⟨Y, i, hi, p, hp, fac⟩,
  use [op Y, p.op, hp, i.op, hi],
  rw [← op_comp, fac, f.op_unop],
end

lemma unop (h : factorisation_axiom F' G') : factorisation_axiom G'.unop F'.unop :=
λ X Z f,
begin
  rcases h f.op with ⟨Y, i, hi, p, hp, fac⟩,
  use [Y.unop, p.unop, hp, i.unop, hi],
  rw [← unop_comp, fac, f.unop_op],
end

variables (F G F' G')

lemma iff_op : factorisation_axiom F G ↔ factorisation_axiom G.op F.op := ⟨op, unop⟩
lemma iff_unop : factorisation_axiom F' G' ↔ factorisation_axiom G'.unop F'.unop := ⟨unop, op⟩

lemma is_retract_of_fac_and_llp (i : X ⟶ Z) {j : X ⟶ Y} {p : Y ⟶ Z} (fac : j ≫ p = i)
  [has_lifting_property_new i p] : is_retract_hom i j :=
begin
  have fac₂ : j ≫ p = i ≫ 𝟙 Z,
  { rw [comp_id, fac], },
  have sq := (comm_sq.mk fac₂).lift,
  let s : arrow.mk i ⟶ arrow.mk j :=
  { left := 𝟙 X,
    right := (comm_sq.mk fac₂).lift,
    w' := by { dsimp, simp only [functor.id_map, arrow.mk_hom, comm_sq.fac_left, id_comp], }, },
  let r : arrow.mk j ⟶ arrow.mk i :=
  { left := 𝟙 X,
    right := p,
    w' := by { dsimp, simp only [id_comp, fac], }, },
  use [s, r],
  ext,
  { dsimp, rw id_comp, },
  { dsimp, rw comm_sq.fac_right, },
end

variables {F G}

lemma eq_llp_with
  (h₁ : factorisation_axiom F G) (h₂ : F.has_lifting_property G)
  (h₃ : F.is_stable_by_retract) : F = G.llp_with :=
begin
  ext i,
  rcases i with ⟨X, Y, i⟩,
  split,
  { exact λ hi X Y, h₂ i hi, },
  { intro hi,
    rcases h₁ i with ⟨Z, j, hj, p, hp, fac⟩,
    haveI : has_lifting_property_new i p := hi p hp,
    exact h₃ i j (is_retract_of_fac_and_llp i fac) hj, },
end

lemma eq_rlp_with
  (h₁ : factorisation_axiom F G) (h₂ : F.has_lifting_property G)
  (h₃ : G.is_stable_by_retract) : G = F.rlp_with :=
by rw [← G.unop_op, eq_llp_with h₁.op h₂.op h₃.op, F.llp_with_op, arrow_class.unop_op]

end factorisation_axiom

end algebraic_topology
