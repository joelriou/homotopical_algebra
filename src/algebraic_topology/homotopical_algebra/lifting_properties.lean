/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.hom_class
import algebraic_topology.homotopical_algebra.retracts

open category_theory
open category_theory.category
open opposite

variables {C : Type*} [category C]

namespace quiver.hom

def left_lifting_property {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :=
  ∀ (f : A ⟶ X) (g : B ⟶ Y) (hfg : f ≫ p = i ≫ g), ∃ (h : B ⟶ X), f = i ≫ h ∧ g = h ≫ p

lemma left_lifting_property_iff_op {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
  i.left_lifting_property p ↔ p.op.left_lifting_property i.op :=
begin
  split,
  { intros hip f g hfg,
    rcases hip g.unop f.unop (by { exact congr_arg unop hfg.symm, }) with ⟨h, comm₁, comm₂⟩,
    use h.op,
    split,
    { exact congr_arg op comm₂, },
    { exact congr_arg op comm₁, }, },
  { intros hip f g hfg,
    rcases hip g.op f.op (by { exact congr_arg op hfg.symm, }) with ⟨h, comm₁, comm₂⟩,
    use h.unop,
    split,
    { exact congr_arg unop comm₂, },
    { exact congr_arg unop comm₁, }, },
end

lemma id_has_left_lifting_propery (A : C) {X Y : C} (p : X ⟶ Y) :
  (𝟙 A).left_lifting_property p :=
begin
  intros f g hfg,
  rw id_comp at hfg,
  use f,
  split,
  { rw id_comp, },
  { rw hfg, }
end

lemma id_has_right_lifting_property (X : C) {A B : C} (i : A ⟶ B) :
  i.left_lifting_property (𝟙 X) :=
by { rw left_lifting_property_iff_op, apply id_has_left_lifting_propery, }

lemma has_left_lifting_property_of_retract {A B A' B' X Y : C} (i : A ⟶ B) (p : X ⟶ Y) (i' : A' ⟶ B')
  (hii' : i.is_retract i') (hi' : i'.left_lifting_property p) : i.left_lifting_property p :=
begin
  rcases hii' with ⟨a, b, a', b', ⟨comm₁, comm₂⟩, ⟨r₁,r₂⟩⟩,
  intros f g hfg,
  rcases hi' (b ≫ f) (b' ≫ g) (by { rw [assoc, hfg, ← assoc, comm₂, assoc], })
    with ⟨h, ⟨lift₁, lift₂⟩⟩,
  use a' ≫ h,
  split,
  { rw [← assoc, comm₁, assoc, ← lift₁, ← assoc, r₁, id_comp], },
  { rw [assoc, ← lift₂, ← assoc, r₂, id_comp], }
end

lemma has_right_lifting_property_of_retract {A B X Y X' Y' : C} (p : X ⟶ Y) (i : A ⟶ B) (p' : X' ⟶ Y')
  (hpp' : p.is_retract p') (hp' : i.left_lifting_property p') : i.left_lifting_property p :=
begin
  rw left_lifting_property_iff_op,
  rw is_retract_iff_op at hpp',
  apply has_left_lifting_property_of_retract p.op i.op p'.op hpp',
  rw ← left_lifting_property_iff_op,
  exact hp',
end

lemma has_left_lifting_property_of_is_iso {A B X Y : C} (i : A ⟶ B) [is_iso i] (p : X ⟶ Y) :
  i.left_lifting_property p :=
begin
  refine has_left_lifting_property_of_retract i p (𝟙 A) _ (id_has_left_lifting_propery A p),
  use [𝟙 A, 𝟙 A, inv i, i],
  split; split,
  { simp only [is_iso.hom_inv_id, comp_id], },
  { refl, },
  { rw id_comp, },
  { simp only [is_iso.inv_hom_id], },
end

lemma has_right_lifting_property_of_is_iso {A B X Y : C} (p : X ⟶ Y) [is_iso p] (i : A ⟶ B) :
  i.left_lifting_property p :=
by { rw i.left_lifting_property_iff_op, apply has_left_lifting_property_of_is_iso, }

end quiver.hom

namespace hom_class

def left_lifting_property (F G : hom_class C) := ∀ (A B X Y : C) (i : A ⟶ B) (p : X ⟶ Y),
  F.contains i → G.contains p → i.left_lifting_property p

def left_lifting_property_iff_op (F G : hom_class C) :
  F.left_lifting_property G ↔ G.op.left_lifting_property F.op :=
begin
  split,
  { intro h,
    intros A B X Y i p hi hp,
    simpa only [p.unop.left_lifting_property_iff_op] using h _ _ _ _ p.unop i.unop hp hi, },
  { intro h,
    intros A B X Y i p hi hp,
    simpa only [i.left_lifting_property_iff_op] using h _ _ _ _ p.op i.op hp hi, }
end

end hom_class
