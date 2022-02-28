/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow_class
import category_theory.lifting_properties
import category_theory.retracts

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

lemma has_left_lifting_property_of_retract (i j p : arrow C) (hij : is_retract i j)
  (hjp : has_lifting_property j p) : has_lifting_property i p :=
begin
  refine ⟨_⟩,
  intro sq,
  rcases hij with ⟨s, r, fac⟩,
  have hjp' := hjp.sq_has_lift,
  let l := (hjp' (r ≫ sq)).exists_lift.some,
  exact ⟨nonempty.intro 
  { lift := s.right ≫ l.lift,
    fac_left' := begin
      have fac₁ := congr_arg (λ (φ : i ⟶ i), (φ.left : i.left ⟶ i.left)) fac,
      have hl₁ := l.fac_left,
      dsimp at fac₁ hl₁,
      rw [← id_comp sq.left, ← fac₁, assoc, ← hl₁, ← assoc, ← assoc],
      congr' 1,
      exact s.w.symm,
    end,
    fac_right' := begin
      have fac₂ := congr_arg (λ (φ : i ⟶ i), (φ.right : i.right ⟶ i.right)) fac,
      have hl₂ := l.fac_right,
      dsimp at fac₂ hl₂,
      rw [← id_comp sq.right, ← fac₂, assoc, assoc],
      congr',
    end} ⟩
end

lemma has_right_lifting_property_of_retract (q i p : arrow C) (hqp : is_retract q p)
  (hip : has_lifting_property i p) : has_lifting_property i q :=
begin
  rw has_lifting_property_iff_op at ⊢ hip,
  rw is_retract_iff_op at hqp,
  exact has_left_lifting_property_of_retract q.op p.op i.op hqp hip,
end

end arrow

namespace arrow_class

@[protected]
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

namespace has_lifting_property

def op {F G : arrow_class C} := (has_lifting_property_iff_op F G).mp
def unop {F G : arrow_class C} := (has_lifting_property_iff_op F G).mpr

end has_lifting_property

@[simp]
def left_lifting_property_with (G : arrow_class C) : arrow_class C :=
λ f, ∀ (g : arrow C), g ∈ G → has_lifting_property f g

@[simp]
def right_lifting_property_with (F : arrow_class C) : arrow_class C :=
λ g, ∀ (f : arrow C), f ∈ F → has_lifting_property f g

def left_lifting_property_with_op (F : arrow_class C) :
  F.op.left_lifting_property_with = F.right_lifting_property_with.op :=
begin
  ext g,
  split,
  { intro h,
    rw mem_op_iff,
    intros f hf,
    rw [arrow.has_lifting_property_iff_op, g.op_unop],
    exact h f.op (by { rw [mem_op_iff, f.unop_op], exact hf }), },
  { intro h,
    intros f hf,
    rw mem_op_iff at h hf,
    have h' := h f.unop hf,
    rw [arrow.has_lifting_property_iff_op] at h',
    simpa only [arrow.op_unop] using h', }
end

def right_lifting_property_with_op (F : arrow_class C) :
  F.op.right_lifting_property_with = F.left_lifting_property_with.op :=
begin
  ext f,
  split,
  { intro h,
    rw mem_op_iff,
    intros g hg,
    rw [arrow.has_lifting_property_iff_op, f.op_unop],
    exact h g.op (by { rw [mem_op_iff, g.unop_op], exact hg }), },
  { intro h,
    intros g hg,
    rw mem_op_iff at h hg,
    have h' := h g.unop hg,
    rw [arrow.has_lifting_property_iff_op] at h',
    simpa only [arrow.op_unop] using h', }
end

lemma is_stable_by_retract_of_llp_with (G : arrow_class C) :
  G.left_lifting_property_with.is_stable_by_retract :=
begin
  intros f f' hf' hff' g hg,
  exact f.has_left_lifting_property_of_retract f' g hff' (hf' g hg),
end

lemma is_stable_by_retract_of_rlp_with (F : arrow_class C) :
  F.right_lifting_property_with.is_stable_by_retract :=
begin
  intros g g' hg' hgg' f hf,
  exact g.has_right_lifting_property_of_retract f g' hgg' (hg' f hf),
end

lemma is_stable_by_composition_of_llp_with (G : arrow_class C) :
  G.left_lifting_property_with.is_stable_by_composition := sorry

lemma is_stable_by_composition_of_rlp_with (F : arrow_class C) :
  F.right_lifting_property_with.is_stable_by_composition := sorry

lemma contains_isomorphisms_of_llp_with (G : arrow_class C) :
  isomorphisms ⊆ G.left_lifting_property_with := sorry

lemma contains_isomorphisms_of_rlp_with (F : arrow_class C) :
  isomorphisms ⊆ F.right_lifting_property_with := sorry


end arrow_class

namespace arrow

lemma is_retract_of_factorisation_and_left_lifting_property
  (i : arrow C) {Z : C} (j : i.left ⟶ Z) (p : Z ⟶ i.right) (fac : i.hom = j ≫ p)
  (hip : has_lifting_property i (arrow.mk p)) :
is_retract i (mk j) :=
begin
  let sq : i ⟶ mk p :=
  { left := j,
    right := 𝟙 i.right,
    w' := by { erw [fac, comp_id], refl, }, },
  have hip' := hip.sq_has_lift,
  let l := (hip' sq).exists_lift.some,
  let s : i ⟶ mk j :=
  { left := 𝟙 i.left,
    right := l.lift,
    w' := by simpa only [functor.map_id, id_comp] using l.fac_left.symm, },
  let r : mk j ⟶ i :=
  { left := 𝟙 i.left,
    right := p,
    w' := by { erw [id_comp, fac], refl, }, },
  use [s, r],
  ext,
  { dsimp,
    erw id_comp, },
  { exact l.fac_right, }
end

lemma congr_hom {f g : arrow C} (h : f = g) :
  f.hom = eq_to_hom (by rw h) ≫ g.hom ≫ eq_to_hom (by rw h) :=
by { subst f, erw [id_comp, comp_id], }

end arrow

namespace arrow_class


lemma eq_left_lifting_property_with (F G : arrow_class C)
  (h₁ : arrow_class.factorisation_axiom F G) (h₂ : F.has_lifting_property G)
  (h₃ : F.is_stable_by_retract) :
  F = G.left_lifting_property_with :=
begin
  ext f,
  split,
  { intros hf g hg,
    exact h₂ f g hf hg, },
  { intro hf,
    rcases h₁ f with ⟨Z, j, p, fac, ⟨hj, hp⟩⟩,
    have fac' := arrow.congr_hom fac,
    erw [id_comp, comp_id] at fac',
    have hf' := f.is_retract_of_factorisation_and_left_lifting_property j p fac' (hf (arrow.mk p) hp),
    exact h₃ f _ hj hf', }
end

lemma eq_right_lifting_property_with (F G : arrow_class C)
  (h₁ : arrow_class.factorisation_axiom F G) (h₂ : F.has_lifting_property G)
  (h₃ : G.is_stable_by_retract) :
  G = F.right_lifting_property_with :=
begin
  have h := G.op.eq_left_lifting_property_with F.op h₁.op h₂.op h₃.op,
  rw left_lifting_property_with_op at h,
  rw [← G.unop_op, h, arrow_class.unop_op],
end

end arrow_class

end category_theory

