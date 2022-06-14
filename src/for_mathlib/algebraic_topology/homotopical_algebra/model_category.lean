/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category_axioms

noncomputable theory

open category_theory category_theory.limits

namespace algebraic_topology

variables (C : Type*) [category C]

class model_category extends category_with_fib_cof_weq C :=
(CM1axiom : has_finite_limits C ∧ has_finite_colimits C)
(CM2axiom : to_category_with_fib_cof_weq.CM2)
(CM3axiom : to_category_with_fib_cof_weq.CM3)
(CM4axiom : to_category_with_fib_cof_weq.CM4)
(CM5axiom : to_category_with_fib_cof_weq.CM5)

namespace model_category

variable {C}
variable [M : model_category C]
include M

def fib := M.fib
def cof := M.cof
def weq := M.weq
def triv_fib := M.to_category_with_fib_cof_weq.triv_fib
def triv_cof := M.to_category_with_fib_cof_weq.triv_cof

lemma CM1 : has_finite_limits C ∧ has_finite_colimits C := M.CM1axiom
lemma CM2 : M.to_category_with_fib_cof_weq.CM2 := M.CM2axiom
lemma CM3 : M.to_category_with_fib_cof_weq.CM3 := M.CM3axiom
lemma CM3a : M.to_category_with_fib_cof_weq.CM3a := CM3.weq
lemma CM3b : M.to_category_with_fib_cof_weq.CM3b := CM3.fib
lemma CM3c : M.to_category_with_fib_cof_weq.CM3c := CM3.cof
lemma CM4 : M.to_category_with_fib_cof_weq.CM4 := M.CM4axiom
lemma CM4a : M.to_category_with_fib_cof_weq.CM4a := CM4.1
lemma CM4b : M.to_category_with_fib_cof_weq.CM4b := CM4.2
lemma CM5 : M.to_category_with_fib_cof_weq.CM5 := M.CM5axiom
lemma CM5a : M.to_category_with_fib_cof_weq.CM5a := CM5.1
lemma CM5b : M.to_category_with_fib_cof_weq.CM5b := CM5.2

@[priority 100] instance : has_finite_limits C := CM1.1
@[priority 100] instance : has_finite_colimits C := CM1.2

instance : model_category Cᵒᵖ :=
{ to_category_with_fib_cof_weq := M.to_category_with_fib_cof_weq.op,
  CM1axiom := ⟨has_finite_limits_opposite, has_finite_colimits_opposite⟩,
  CM2axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM2_iff_op] using CM2axiom,
  CM3axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM3_iff_op] using CM3axiom,
  CM4axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM4_iff_op] using CM4axiom,
  CM5axiom := by simpa only [← M.to_category_with_fib_cof_weq.CM5_iff_op] using CM5axiom, }

variables {A B X Y Z : C} (i : A ⟶ B) {p : X ⟶ Y} {q : Y ⟶ Z} {f : X ⟶ Y} (hip : is_retract_hom i p)

class cofibration : Prop := (mem : arrow.mk i ∈ M.cof)
class fibration : Prop := (mem : arrow.mk i ∈ M.fib)
class weak_eq : Prop := (mem : arrow.mk i ∈ M.weq)

variable {i}

@[priority 100] instance CM4a' [hi₁ : cofibration i] [hi₂ : weak_eq i] [hp : fibration p] :
  has_lifting_property_new i p := CM4a i ⟨hi₁.mem, hi₂.mem⟩ p hp.mem
@[priority 100] instance CM4b' [hi : cofibration i] [hp₁ : fibration p] [hp₂ : weak_eq p] :
  has_lifting_property_new i p := CM4b i hi.mem p ⟨hp₁.mem, hp₂.mem⟩

lemma cofibration_retract_stable [hp : cofibration p] : cofibration i := ⟨CM3.cof i p hip hp.mem⟩
lemma fibration_retract_stable [hp : fibration p] : fibration i := ⟨CM3.fib i p hip hp.mem⟩
lemma weq_retract_stable [hp : weak_eq p] : weak_eq i := ⟨CM3.weq i p hip hp.mem⟩

lemma cof_eq_llp_with_triv_fib : cof = (triv_fib : arrow_class C).llp_with :=
factorisation_axiom.eq_llp_with CM5b CM4b CM3.cof
lemma triv_fib_eq_rlp_with_cof : triv_fib = (cof : arrow_class C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5b CM4b CM3.triv_fib
lemma triv_cof_eq_llp_with_fib : triv_cof = (fib : arrow_class C).llp_with :=
factorisation_axiom.eq_llp_with CM5a CM4a CM3.triv_cof
lemma fib_eq_rlp_with_triv_cof : fib = (triv_cof : arrow_class C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5a CM4a CM3.fib

lemma cof_comp_stable : (cof : arrow_class C).is_stable_by_composition :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.is_stable_by_composition.for_llp_with, }
lemma fib_comp_stable : (fib : arrow_class C).is_stable_by_composition :=
by { rw fib_eq_rlp_with_triv_cof, apply arrow_class.is_stable_by_composition.for_rlp_with, }

instance comp_weak_eq [hp : weak_eq p] [hq : weak_eq q] : weak_eq (p ≫ q) :=
⟨CM2.of_comp p q hp.mem hq.mem⟩
instance comp_cofibration [hp : cofibration p] [hq : cofibration q] : cofibration (p ≫ q) :=
⟨cof_comp_stable p q hp.mem hq.mem⟩
instance comp_fibration [hp : fibration p] [hq : fibration q] : fibration (p ≫ q) :=
⟨fib_comp_stable p q hp.mem hq.mem⟩

namespace weak_eq

variables (p q)

lemma of_comp_left (hp : weak_eq p) (hpq : weak_eq (p ≫ q)) : weak_eq q :=
⟨CM2.of_comp_left p q hp.mem hpq.mem⟩
lemma of_comp_left' [hp : weak_eq p] [hpq : weak_eq (p ≫ q)] : weak_eq q :=
of_comp_left p q hp hpq

lemma of_comp_right (hq : weak_eq q) (hpq : weak_eq (p ≫ q)) : weak_eq p :=
⟨CM2.of_comp_right p q hq.mem hpq.mem⟩
lemma of_comp_right' [hq : weak_eq q] [hpq : weak_eq (p ≫ q)] : weak_eq p :=
of_comp_right p q hq hpq

end weak_eq

lemma cof_contains_iso : arrow_class.isomorphisms ⊆ (cof : arrow_class C) :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.isomorphisms_subset_llp_with, }
lemma fib_contains_iso : arrow_class.isomorphisms ⊆ (fib : arrow_class C) :=
by { rw fib_eq_rlp_with_triv_cof, apply arrow_class.isomorphisms_subset_rlp_with, }
lemma triv_cof_contains_iso : arrow_class.isomorphisms ⊆ (triv_cof : arrow_class C) :=
by { rw triv_cof_eq_llp_with_fib, apply arrow_class.isomorphisms_subset_llp_with, }
lemma triv_fib_contains_iso : arrow_class.isomorphisms ⊆ (triv_fib : arrow_class C) :=
by { rw triv_fib_eq_rlp_with_cof, apply arrow_class.isomorphisms_subset_rlp_with, }
lemma weq_contains_iso : arrow_class.isomorphisms ⊆ (weq : arrow_class C) := λ f hf,
(triv_cof_contains_iso hf).2

@[priority 100] instance cofibration_of_is_iso [is_iso p] : cofibration p :=
⟨cof_contains_iso (arrow_class.mem_isomorphisms_of_is_iso p)⟩
@[priority 100] instance fibration_of_is_iso [is_iso p] : fibration p :=
⟨fib_contains_iso (arrow_class.mem_isomorphisms_of_is_iso p)⟩
@[priority 100] instance weak_eq_of_is_iso [is_iso p] : weak_eq p :=
⟨weq_contains_iso (arrow_class.mem_isomorphisms_of_is_iso p)⟩

instance CM5a_cofibration : cofibration (CM5a.i f) := ⟨(CM5a.i_mem f).1⟩
instance CM5a_weak_eq : weak_eq (CM5a.i f) := ⟨(CM5a.i_mem f).2⟩
instance CM5a_fibration : fibration (CM5a.p f) := ⟨CM5a.p_mem f⟩

instance CM5b_cofibration : cofibration (CM5b.i f) := ⟨CM5b.i_mem f⟩
instance CM5b_fibration : fibration (CM5b.p f) := ⟨(CM5b.p_mem f).1⟩
instance CM5b_weak_eq : weak_eq (CM5b.p f) := ⟨(CM5b.p_mem f).2⟩

lemma cof_is_stable_by_direct_image : (cof : arrow_class C).is_stable_by_direct_image :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.is_stable_by_direct_image.for_llp_with, }
lemma triv_cof_is_stable_by_direct_image : (triv_cof : arrow_class C).is_stable_by_direct_image :=
by { rw triv_cof_eq_llp_with_fib, apply arrow_class.is_stable_by_direct_image.for_llp_with, }

lemma cof_is_stable_by_coproduct : (cof : arrow_class C).is_stable_by_coproduct :=
by { rw cof_eq_llp_with_triv_fib, apply arrow_class.is_stable_by_coproduct.for_llp_with, }
lemma triv_cof_is_stable_by_coproduct : (triv_cof : arrow_class C).is_stable_by_coproduct :=
by { rw triv_cof_eq_llp_with_fib, apply arrow_class.is_stable_by_coproduct.for_llp_with, }

lemma cof_is_iso_invariant : (cof : arrow_class C).is_iso_invariant :=
arrow_class.is_iso_invariant.of_comp_stable_and_contains_iso cof cof_comp_stable cof_contains_iso
lemma fib_is_iso_invariant : (fib : arrow_class C).is_iso_invariant :=
arrow_class.is_iso_invariant.of_comp_stable_and_contains_iso fib fib_comp_stable fib_contains_iso
lemma weq_is_iso_invariant : (weq : arrow_class C).is_iso_invariant :=
arrow_class.is_iso_invariant.of_comp_stable_and_contains_iso weq CM2.of_comp weq_contains_iso

namespace cofibration

lemma op (hi : cofibration i) : fibration i.op := ⟨hi.mem⟩
lemma unop {A B : Cᵒᵖ} {i : A ⟶ B} (hi : cofibration i) : fibration i.unop := ⟨hi.mem⟩

lemma direct_image ⦃f : A ⟶ X⦄ ⦃i : A ⟶ B⦄ ⦃i' : X ⟶ Y⦄ ⦃g : B ⟶ Y⦄
  (h : is_pushout f i i' g) [hi : cofibration i] : cofibration i' :=
⟨cof_is_stable_by_direct_image h hi.mem⟩

lemma direct_image_is_weak_eq ⦃f : A ⟶ X⦄ ⦃i : A ⟶ B⦄ ⦃i' : X ⟶ Y⦄ ⦃g : B ⟶ Y⦄
  (h : is_pushout f i i' g) [hi₁ : cofibration i] [hi₂ : weak_eq i] : weak_eq i' :=
⟨(triv_cof_is_stable_by_direct_image h ⟨hi₁.mem, hi₂.mem⟩).2⟩

instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hg : cofibration g] :
  cofibration (pushout.inl : X₁ ⟶ pushout f g) :=
⟨cof_is_stable_by_direct_image.for_pushout_inl f g hg.mem⟩

instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hf : cofibration f] :
  cofibration (pushout.inr : X₂ ⟶ pushout f g) :=
⟨cof_is_stable_by_direct_image.for_pushout_inr f g hf.mem⟩

instance {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [h₁ : cofibration f₁] [h₂ : cofibration f₂] :
  cofibration (coprod.map f₁ f₂) :=
⟨cof_is_stable_by_coproduct.binary f₁ f₂ h₁.mem h₂.mem⟩

instance {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [h₁ : cofibration f₁] [h₂ : cofibration f₂]
  [h₁' : weak_eq f₁] [h₂' : weak_eq f₂] :
  weak_eq (coprod.map f₁ f₂) :=
⟨(triv_cof_is_stable_by_coproduct.binary f₁ f₂ ⟨h₁.mem, h₁'.mem⟩ ⟨h₂.mem, h₂'.mem⟩).2⟩

lemma iso_invariance {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  cofibration f₁ ↔ cofibration f₂ :=
begin
  split,
  { exact λ h, ⟨cof_is_iso_invariant e h.mem⟩, },
  { exact λ h, ⟨cof_is_iso_invariant e.symm h.mem⟩, },
end

end cofibration

namespace fibration

lemma op (hp : fibration p) : cofibration p.op := ⟨hp.mem⟩
lemma unop {X Y : Cᵒᵖ} {p : X ⟶ Y} (hp : fibration p) : cofibration p.unop := ⟨hp.mem⟩

variable (p)
lemma iff_op : fibration p ↔ cofibration p.op := ⟨op, cofibration.unop⟩
lemma iff_unop {X Y : Cᵒᵖ} (p : X ⟶ Y) : fibration p ↔ cofibration p.unop := ⟨unop, cofibration.op⟩

lemma iso_invariance {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  fibration f₁ ↔ fibration f₂ :=
begin
  split,
  { exact λ h, ⟨fib_is_iso_invariant e h.mem⟩, },
  { exact λ h, ⟨fib_is_iso_invariant e.symm h.mem⟩, },
end

end fibration

namespace cofibration

variable (p)

lemma iff_op : cofibration p ↔ fibration p.op := ⟨op, fibration.unop⟩
lemma iff_unop {X Y : Cᵒᵖ} (p : X ⟶ Y) : cofibration p ↔ fibration p.unop := ⟨unop, fibration.op⟩

end cofibration

namespace weak_eq

lemma op (hp : weak_eq p) : weak_eq p.op := ⟨hp.mem⟩
lemma unop {X Y : Cᵒᵖ} {p : X ⟶ Y} (hp : weak_eq p) : weak_eq p.unop := ⟨hp.mem⟩

instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hg₁ : cofibration g] [hg₂ : weak_eq g] :
  weak_eq (pushout.inl : X₁ ⟶ pushout f g) :=
⟨(triv_cof_is_stable_by_direct_image.for_pushout_inl f g ⟨hg₁.mem, hg₂.mem⟩).2⟩

instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hf₁ : cofibration f] [hf₂ : weak_eq f] :
  weak_eq (pushout.inr : X₂ ⟶ pushout f g) :=
⟨(triv_cof_is_stable_by_direct_image.for_pushout_inr f g ⟨hf₁.mem, hf₂.mem⟩).2⟩

lemma iso_invariance {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  weak_eq f₁ ↔ weak_eq f₂ :=
begin
  split,
  { exact λ h, ⟨weq_is_iso_invariant e h.mem⟩, },
  { exact λ h, ⟨weq_is_iso_invariant e.symm h.mem⟩, },
end

end weak_eq

end model_category

end algebraic_topology
