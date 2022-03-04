/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cylinder

noncomputable theory

open category_theory
open category_theory.limits
open algebraic_topology

namespace algebraic_topology

namespace model_category

variables (M : model_category)

@[derive category]
def cofibrant_objects := { X : M.C // nonempty (is_cofibrant X) }

namespace cofibrant_objects

variable {M}

def right_homotopy : hom_rel M.cofibrant_objects := λ A X f₁ f₂,
∃ (P : path_object X.1), nonempty (P.pre.right_homotopy f₁ f₂)

namespace right_homotopy

def symm {A X : M.cofibrant_objects } {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) :
  right_homotopy f₂ f₁ := 
by { cases H with P hP, use P.symm, exact nonempty.intro hP.some.symm, }

lemma comp_left {A B X : M.cofibrant_objects}
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_homotopy g g') :
  right_homotopy (f ≫ g) (f ≫ g') :=
by { cases H with P hP, use P, exact nonempty.intro (hP.some.comp_left f), }

lemma comp_right {A B X : M.cofibrant_objects}
  {f f' : A ⟶ B} {g : B ⟶ X} (H : right_homotopy f f') :
  right_homotopy (f ≫ g) (f' ≫ g) :=
begin
  cases H with P hP,
  let C := (cylinder_exists A.1).some,
  suffices hl : C.to_precylinder.left_homotopy (f ≫ g) (f' ≫ g),
  { let P' := (path_object_exists X.1).some,
    haveI := A.2.some,
    use [P', nonempty.intro (P'.right_homotopy_of_left_homotopy C _ _ hl)], },
  suffices hl' : C.to_precylinder.left_homotopy f f',
  { exact hl'.comp_right g, },
  { exact @cylinder.left_homotopy_of_right_homotopy M _ _ sorry C P _ _ hP.some,
    -- se ramener au cas où B est fibrant ?
  },
end

end right_homotopy

inductive right_ho_trans_closure {A X : M.cofibrant_objects} : (A ⟶ X) → (A ⟶ X) → Prop
| right_homotopy {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) : right_ho_trans_closure f₁ f₂
| trans {f₁ f₂ f₃ : A ⟶ X} (H₁₂ : right_ho_trans_closure f₁ f₂) (H₂₃ : right_ho_trans_closure f₂ f₃) :
  right_ho_trans_closure f₁ f₃

namespace right_ho_trans_closure

lemma is_equiv (A X : M.cofibrant_objects) : is_equiv (A ⟶ X) right_ho_trans_closure :=
{ refl := λ f, right_homotopy begin
    cases path_object_exists X.1 with P hP,
    use P,
    exact nonempty.intro (pre_path_object.right_homotopy.refl f),
  end,
  trans := λ f₁ f₂ f₃, right_ho_trans_closure.trans,
  symm := λ f g H, begin
    induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₂₁ H₃₂,
    { exact right_homotopy H₁₂.symm, },
    { exact trans H₃₂ H₂₁, }
  end, }

lemma comp_left (A B X : M.cofibrant_objects)
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_ho_trans_closure g g') :
    right_ho_trans_closure (f ≫ g) (f ≫ g') :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy (H₁₂.comp_left f), },
  { exact trans H₁₂' H₂₃', }
end

lemma comp_right (A B X : M.cofibrant_objects)
  (f f' : A ⟶ B) {g : B ⟶ X} (H : right_ho_trans_closure f f') :
    right_ho_trans_closure (f ≫ g) (f' ≫ g) :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy H₁₂.comp_right, },
  { exact trans H₁₂' H₂₃', },
end

end right_ho_trans_closure

variable (M)

def right_ho_trans_closure_hom_rel : hom_rel M.cofibrant_objects := λ X Y, cofibrant_objects.right_ho_trans_closure

def congruence : congruence (right_ho_trans_closure_hom_rel M) :=
{ is_equiv := right_ho_trans_closure.is_equiv,
  comp_left := right_ho_trans_closure.comp_left,
  comp_right := right_ho_trans_closure.comp_right }

@[derive category]
def Ho := quotient (right_ho_trans_closure_hom_rel M)

def L : M.cofibrant_objects ⥤ cofibrant_objects.Ho M :=
quotient.functor (right_ho_trans_closure_hom_rel M)

end cofibrant_objects

@[derive category]
def fibrant_objects := { X : M.C // nonempty (is_fibrant X) }

def fibrant_and_cofibrant_objects := { X : M.C // nonempty (is_fibrant X) ∧ nonempty (is_cofibrant X) }

end model_category

end algebraic_topology
