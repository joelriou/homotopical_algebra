/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow_class
import category_theory.lifting_properties
--import algebraic_topology.homotopical_algebra.retracts

open category_theory
open category_theory.category
open opposite

variables {C : Type*} [category C]

namespace category_theory

namespace arrow

lemma lift_struct_equiv_op {i p : arrow C} (sq : i ⟶ p) : lift_struct sq ≃ lift_struct (op_hom sq) :=
{ to_fun := λ L,
  { lift := L.lift.op,
    fac_left' := congr_arg (λ (φ : _ ⟶ _), φ.op) L.fac_right,
    fac_right' := congr_arg (λ (φ : _ ⟶ _), φ.op) L.fac_left, },
  inv_fun := λ L,
  { lift := L.lift.unop,
    fac_left' := congr_arg (λ (φ : _ ⟶ _), φ.unop) L.fac_right,
    fac_right' := congr_arg (λ (φ : _ ⟶ _), φ.unop) L.fac_left },
  left_inv := λ L, by { cases L, refl, },
  right_inv := λ L, by { cases L, refl, }, }

lemma has_lift_iff_op {i p : arrow C} (sq : i ⟶ p) : has_lift sq ↔ has_lift (op_hom sq) :=
begin
  split,
  { intro h,
    letI := h.1,
    exact ⟨equiv.nonempty (lift_struct_equiv_op sq).symm⟩, },
  { intro h,
    letI := h.1,
    exact ⟨equiv.nonempty (lift_struct_equiv_op sq)⟩, },
end

lemma has_lifting_property_iff_op (i p : arrow C) :
  has_lifting_property i p ↔ has_lifting_property p.op i.op :=
begin
  split; intro h; refine ⟨_⟩; intro sq,
  { rw [op_unop_hom sq, ← has_lift_iff_op],
    apply h.1, },
  { rw has_lift_iff_op,
    apply h.1, }
end


/-
lemma has_right_lifting_property_of_retract {A B X Y X' Y' : C} (p : X ⟶ Y) (i : A ⟶ B) (p' : X' ⟶ Y')
  (hpp' : p.is_retract p') (hp' : i.left_lifting_property p') : i.left_lifting_property p :=
begin
  rw left_lifting_property_iff_op,
  rw is_retract_iff_op at hpp',
  apply has_left_lifting_property_of_retract p.op i.op p'.op hpp',
  rw ← left_lifting_property_iff_op,
  exact hp',
end-/

end arrow

namespace arrow_class

def has_lifting_property (F G : arrow_class C) := ∀ (i p : arrow C),
  i ∈ F → p ∈ G → has_lifting_property i p

def has_lifting_property_iff_op (F G : arrow_class C) :
  F.has_lifting_property G ↔ G.op.has_lifting_property F.op :=
begin
  split,
  { intro h,
    intros i p hi hp,
    simpa only [arrow.op_unop, p.unop.has_lifting_property_iff_op i.unop] using h p.unop i.unop hp hi, },
  { intro h,
    intros i p hi hp,
    have h' := h p.op i.op (by { rw [mem_op_iff, p.unop_op], exact hp, })
      (by { rw [mem_op_iff, i.unop_op], exact hi, }),
    simpa only [i.has_lifting_property_iff_op] using h',
    }
end

end arrow_class

end category_theory

