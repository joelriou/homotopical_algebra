/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.comm_sq
import for_mathlib.category_theory.retracts
import for_mathlib.category_theory.arrow_class

noncomputable theory

open category_theory.category category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

variables {A B B' X Y Y' : C} {f : A ⟶ X} {i : A ⟶ B} (i' : B ⟶ B') {p : X ⟶ Y} (p' : Y ⟶ Y') {g : B ⟶ Y}
variables {W Z : C} {q : W ⟶ Z} {f' : X ⟶ W} {g' : Y ⟶ Z}

namespace limits

namespace comm_sq

@[ext, nolint has_inhabited_instance]
structure lifts (sq : comm_sq f i p g) :=
(l : B ⟶ X) (fac_left : i ≫ l = f) (fac_right : l ≫ p = g)

namespace lifts

def op {sq : comm_sq f i p g} (l : lifts sq) : lifts sq.op :=
{ l := l.l.op,
  fac_left := by rw [← op_comp, l.fac_right],
  fac_right := by rw [← op_comp, l.fac_left], }

def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : comm_sq f i p g}
  (l : lifts sq) : lifts sq.unop :=
{ l := l.l.unop,
  fac_left := by rw [← unop_comp, l.fac_right],
  fac_right := by rw [← unop_comp, l.fac_left], }

def op_equiv (sq : comm_sq f i p g) : lifts sq ≃ lifts sq.op :=
{ to_fun := op, 
  inv_fun := unop,
  left_inv := by tidy,
  right_inv := by tidy, }

def unop_equiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : comm_sq f i p g) :
  lifts sq ≃ lifts sq.unop :=
{ to_fun := unop, 
  inv_fun := op,
  left_inv := by tidy,
  right_inv := by tidy, }

end lifts

/-lemma comp (sq₁ : comm_sq f i p g) (sq₂ : comm_sq f' p q g') :
  comm_sq (f ≫ f') i q (g ≫ g') :=
⟨by simp only [assoc, sq₂.w, sq₁.w_assoc]⟩

namespace lifts

def comp {sq₁ : comm_sq f i p g} {sq₂ : comm_sq f' p q g'}
  (l₁ : lifts sq₁) (l₂ : lifts sq₂) : lifts (sq₁.comp sq₂) :=
{ l := l₁.l ≫ p ≫ l₂.l,
  fac_left := by rw [l₂.fac_left, ← assoc, l₁.fac_left],
  fac_right := begin
    simp only [assoc, l₂.fac_right],
    simp only [← assoc, l₁.fac_right],
  end }

end lifts-/

variable (sq : comm_sq f i p g)

class has_lift : Prop := (exists_lift : nonempty sq.lifts)

namespace has_lift

lemma iff : has_lift sq ↔ nonempty sq.lifts :=
begin
  split,
  { intro h,
    exact h.exists_lift, },
  { intro h,
    exact mk h, },
end

lemma iff_op : has_lift sq ↔ has_lift sq.op :=
begin
  rw [iff, iff],
  exact nonempty.congr (lifts.op_equiv sq).to_fun (lifts.op_equiv sq).inv_fun,
end

lemma iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (sq : comm_sq f i p g) :
  has_lift sq ↔ has_lift sq.unop :=
begin
  rw [iff, iff],
  exact nonempty.congr (lifts.unop_equiv sq).to_fun (lifts.unop_equiv sq).inv_fun,
end

end has_lift

def lift [hsq : has_lift sq] : B ⟶ X :=
hsq.exists_lift.some.l

@[simp, reassoc]
lemma fac_left [hsq : has_lift sq] : i ≫ sq.lift = f :=
hsq.exists_lift.some.fac_left

@[simp, reassoc]
lemma fac_right [hsq : has_lift sq] : sq.lift ≫ p = g :=
hsq.exists_lift.some.fac_right

end comm_sq

end limits

variables (i p)
open limits

class has_lifting_property_new : Prop :=
(sq_has_lift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : comm_sq f i p g), sq.has_lift)

@[priority 100]
instance sq_has_lift_of_has_lifting_property (sq : comm_sq f i p g)
  [hip : has_lifting_property_new i p] : sq.has_lift := by apply hip.sq_has_lift

namespace has_lifting_property_new

variables {i p}

def op (h : has_lifting_property_new i p) : has_lifting_property_new p.op i.op :=
begin
  constructor,
  intros f g sq,
  simp only [comm_sq.has_lift.iff_unop, quiver.hom.unop_op],
  haveI := h,
  apply_instance,
end

def unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y}
  (h : has_lifting_property_new i p) : has_lifting_property_new p.unop i.unop :=
begin
  constructor,
  intros f g sq,
  rw comm_sq.has_lift.iff_op,
  simp only [quiver.hom.op_unop],
  haveI := h,
  apply_instance,
end

lemma iff_op : has_lifting_property_new i p ↔ has_lifting_property_new p.op i.op := ⟨op, unop⟩

lemma iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
  has_lifting_property_new i p ↔ has_lifting_property_new p.unop i.unop := ⟨unop, op⟩

variables (i p)

@[priority 100]
instance of_left_iso [is_iso i] : has_lifting_property_new i p :=
⟨λ f g sq, ⟨nonempty.intro 
  { l := inv i ≫ f,
    fac_left := by simp only [is_iso.hom_inv_id_assoc],
    fac_right := by simp only [sq.w, assoc, is_iso.inv_hom_id_assoc], }⟩⟩

@[priority 100]
instance of_right_iso [is_iso p] : has_lifting_property_new i p :=
⟨λ f g sq, ⟨nonempty.intro
  { l := g ≫ inv p,
    fac_left := by simp only [← sq.w_assoc, is_iso.hom_inv_id, comp_id],
    fac_right := by simp only [assoc, is_iso.inv_hom_id, comp_id], }⟩⟩

instance of_comp_left [has_lifting_property_new i p] [has_lifting_property_new i' p] :
  has_lifting_property_new (i ≫ i') p :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw assoc at fac,
  exact ⟨nonempty.intro
  { l := (comm_sq.mk (comm_sq.mk fac).fac_right).lift,
    fac_left := by simp only [assoc, comm_sq.fac_left],
    fac_right := by simp only [comm_sq.fac_right], }⟩,
end⟩

instance of_comp_right [has_lifting_property_new i p] [has_lifting_property_new i p'] :
  has_lifting_property_new i (p ≫ p') :=
⟨λ f g sq, begin
  have fac := sq.w,
  rw ← assoc at fac,
  let sq₂ := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
  exact ⟨nonempty.intro 
  { l := (comm_sq.mk ((comm_sq.mk fac).fac_left.symm)).lift,
    fac_left := by simp only [comm_sq.fac_left],
    fac_right := by simp only [comm_sq.fac_right_assoc, comm_sq.fac_right], }⟩,
end⟩

lemma of_retract_left {A' B' : C} {i : A ⟶ B} {i' : A' ⟶ B'} {p : X ⟶ Y}
  (h : is_retract_hom i i') [has_lifting_property_new i' p] :
  has_lifting_property_new i p :=
begin
  constructor,
  intros f g sq,
  rcases h with ⟨s, r, hsr⟩,
  have fac : (r.left ≫ f) ≫ p = i' ≫ (r.right ≫ g) :=
    by simpa only [assoc, sq.w] using arrow.w_assoc r g,
  constructor,
  exact nonempty.intro
  { l := s.right ≫ (comm_sq.mk fac).lift,
    fac_left := begin
      have hs := arrow.w s,
      simp only [arrow.mk_hom] at hs,
      rw [← assoc, ← hs, assoc, comm_sq.fac_left, ← assoc, ← comma.comp_left, hsr, arrow.id_left],
      apply id_comp,
    end,
    fac_right := begin
      rw [assoc, comm_sq.fac_right, ← assoc, ← comma.comp_right, hsr, arrow.id_right],
      apply id_comp,
    end, },
end

lemma of_retract_right {X' Y' : C} {i : A ⟶ B} {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (h : is_retract_hom p p') [hip' : has_lifting_property_new i p'] :
  has_lifting_property_new i p :=
begin
  rw iff_op at ⊢ hip',
  rw is_retract_hom.iff_op at h,
  haveI := hip',
  exact of_retract_left h,
end

end has_lifting_property_new

namespace arrow_class

@[protected]
def has_lifting_property (F G : arrow_class C) :=
∀ ⦃A B X Y : C⦄ (i : A ⟶ B) (hi : arrow.mk i ∈ F) (p : X ⟶ Y) (hp : arrow.mk p ∈ G),
has_lifting_property_new i p

namespace has_lifting_property

def has_lift {F G : arrow_class C} (h : has_lifting_property F G)
{A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
(sq : comm_sq f i p g) (hi : arrow.mk i ∈ F) (hp : arrow.mk p ∈ G) :
  sq.has_lift := by { haveI := h i hi p hp, apply_instance, }

def op {F G : arrow_class C} (h : has_lifting_property F G) :
  has_lifting_property G.op F.op :=
λ A B X Y i hi p hp, (h p.unop hp i.unop hi).op

def unop {F G : arrow_class Cᵒᵖ} (h : has_lifting_property F G) :
  has_lifting_property G.unop F.unop :=
λ A B X Y i hi p hp, (h p.op hp i.op hi).unop

lemma iff_op (F G : arrow_class C) :
  has_lifting_property F G ↔ has_lifting_property G.op F.op := ⟨op, unop⟩

lemma iff_unop (F' G' : arrow_class Cᵒᵖ) :
  has_lifting_property F' G' ↔ has_lifting_property G'.unop F'.unop := ⟨unop, op⟩

end has_lifting_property

def has_lifting_property_iff_op (F G : arrow_class C) :
  F.has_lifting_property G ↔ G.op.has_lifting_property F.op :=
begin
  split,
  { intro h,
    intros A B X Y i hi p hp,
    constructor,
    intros f g sq,
    rw comm_sq.has_lift.iff_unop,
    haveI := h p.unop hp i.unop hi,
    apply_instance, },
  { intro h,
    intros A B X Y i hi p hp,
    constructor,
    intros f g sq,
    rw comm_sq.has_lift.iff_op,
    haveI := h p.op hp i.op hi,
    apply_instance, },
end

@[simp]
def llp_with (G : arrow_class C) : arrow_class C :=
λ i, ∀ {X Y : C} (p : X ⟶ Y), arrow.mk p ∈ G → has_lifting_property_new i.hom p

@[simp]
def rlp_with (F : arrow_class C) : arrow_class C :=
λ p, ∀ {X Y : C} (i : X ⟶ Y), arrow.mk i ∈ F → has_lifting_property_new i p.hom

def llp_with_op (F : arrow_class C) :
  F.op.llp_with = F.rlp_with.op :=
begin
  ext i,
  split,
  { intros h X Y p hp,
    simpa only [has_lifting_property_new.iff_unop] using h p.op hp, },
  { intros h X Y p hp,
    have hp' := h p.unop hp,
    rw has_lifting_property_new.iff_op at hp',
    exact hp', },
end

def llp_with_unop (F : arrow_class Cᵒᵖ) :
  F.unop.rlp_with = F.llp_with.unop :=
begin
  have h := llp_with_op F.unop,
  rw F.op_unop at h,
  rw [h, arrow_class.unop_op],
end

def rlp_with_op (F : arrow_class C) :
  F.op.rlp_with = F.llp_with.op :=
begin
  ext p,
  split,
  { intros h X Y i hi,
    have paf := h i.op,
    simpa only [has_lifting_property_new.iff_unop] using h i.op hi, },
  { intros h X Y i hi,
    have hi' := h i.unop hi,
    rw has_lifting_property_new.iff_op at hi',
    exact hi', },
end

def rlp_with_unop (F : arrow_class Cᵒᵖ) :
   F.unop.llp_with = F.rlp_with.unop :=
begin
  have h := rlp_with_op F.unop,
  rw F.op_unop at h,
  rw [h, arrow_class.unop_op],
end

lemma llp_with_is_stable_by_composition (F : arrow_class C) :
  F.llp_with.is_stable_by_composition :=
⟨λ X Y Z f g hf hg A B p hp, begin
  rw arrow.mk_hom,
  haveI : has_lifting_property_new f p := hf p hp,
  haveI : has_lifting_property_new g p := hg p hp,
  apply_instance,
end⟩

lemma rlp_with_is_stable_by_composition (F : arrow_class C) :
  F.rlp_with.is_stable_by_composition :=
⟨λ A B C f g hf hg X Y i hi, begin
  rw arrow.mk_hom,
  haveI : has_lifting_property_new i f := hf i hi,
  haveI : has_lifting_property_new i g := hg i hi,
  apply_instance,
end⟩

end arrow_class

end category_theory
