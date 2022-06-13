/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fibrant

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.category
open algebraic_topology
open opposite

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

namespace brown_factorisation

variables {X Y : C} (f : X ⟶ Y)

namespace cofibrant

def obj := CM5b.obj (coprod.desc f (𝟙 Y))

def i : X ⟶ obj f := coprod.inl ≫ CM5b.i (coprod.desc f (𝟙 Y))
def p : obj f ⟶ Y := CM5b.p (coprod.desc f (𝟙 Y))
def s : Y ⟶ obj f := coprod.inr ≫ CM5b.i (coprod.desc f (𝟙 Y))

@[simp, reassoc]
lemma fac₁ : i f ≫ p f = f :=
by simp only [i, p, assoc, factorisation_axiom.fac, coprod.inl_desc]

@[simp, reassoc]
lemma fac₂ : s f ≫ p f = 𝟙 Y :=
by simp only [s, p, assoc, factorisation_axiom.fac, coprod.inr_desc]

instance weak_eq_p : weak_eq (p f) := by { dsimp [p], apply_instance, }

instance weak_eq_s : weak_eq (s f) :=
weak_eq.of_comp_right (s f) (p f) infer_instance (by { rw fac₂, apply_instance, })

instance weak_eq_i [weak_eq f] : weak_eq (i f) :=
weak_eq.of_comp_right (i f) (p f) infer_instance (by { rw fac₁, apply_instance, })

instance fibration_p : fibration (p f) := by { dsimp [p], apply_instance, }

instance cof_i [is_cofibrant Y] : cofibration (i f) := by { dsimp [i], apply_instance, }
instance cof_s [is_cofibrant X] : cofibration (s f) := by { dsimp [s], apply_instance, }

end cofibrant

namespace fibrant

def obj := (cofibrant.obj f.op).unop

def i : X ⟶ obj f := (cofibrant.p f.op).unop
def p : obj f ⟶ Y := (cofibrant.i f.op).unop
def r : obj f ⟶ X := (cofibrant.s f.op).unop

@[simp, reassoc]
lemma fac₁ : i f ≫ p f = f :=
by { dsimp only [i, p], rw [← unop_comp, cofibrant.fac₁, f.unop_op], }

@[simp, reassoc]
lemma fac₂ : i f ≫ r f = 𝟙 _ :=
by { dsimp only [i, r], rw [← unop_comp, cofibrant.fac₂], refl, }

instance weak_eq_i : weak_eq (i f) := (infer_instance : weak_eq (cofibrant.p f.op)).unop
instance weak_eq_r : weak_eq (r f) := (infer_instance : weak_eq (cofibrant.s f.op)).unop
instance weak_eq_p [hf : weak_eq f] : weak_eq (p f) :=
by { haveI := hf.op, apply weak_eq.unop, apply_instance, }
instance cof_i : cofibration (i f) := (infer_instance : fibration (cofibrant.p f.op)).unop
instance fib_p [hX : is_fibrant X] : fibration (p f) :=
by { haveI := hX.op, apply cofibration.unop, apply_instance, }
instance fib_s [hY : is_fibrant Y] : fibration (r f) :=
by { haveI := hY.op, apply cofibration.unop, apply_instance, }

end fibrant

end brown_factorisation

end model_category

end algebraic_topology
