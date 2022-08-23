/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category_axioms
import category_theory.limits.opposites
import category_theory.limits.shapes.comm_sq

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

variables {A B X Y Z : C} (i : A ⟶ B) {p : X ⟶ Y} {q : Y ⟶ Z} {f : X ⟶ Y}
  (hip : is_retract_hom i p)

class cofibration : Prop := (property : cof i)
class fibration : Prop := (property : fib i)
class weak_eq : Prop := (property : weq i)

variable {i}

@[priority 100] instance CM4a' [hi₁ : cofibration i] [hi₂ : weak_eq i] [hp : fibration p] :
  has_lifting_property i p := CM4a i ⟨hi₁.property, hi₂.property⟩ p hp.property
@[priority 100] instance CM4b' [hi : cofibration i] [hp₁ : fibration p] [hp₂ : weak_eq p] :
  has_lifting_property i p := CM4b i hi.property p ⟨hp₁.property, hp₂.property⟩

lemma cofibration_retract_stable [hp : cofibration p] : cofibration i :=
⟨CM3.cof i p hip hp.property⟩
lemma fibration_retract_stable [hp : fibration p] : fibration i :=
⟨CM3.fib i p hip hp.property⟩
lemma weq_retract_stable [hp : weak_eq p] : weak_eq i :=
⟨CM3.weq i p hip hp.property⟩

lemma cof_eq_llp_with_triv_fib : cof = (triv_fib : morphism_property C).llp_with :=
factorisation_axiom.eq_llp_with CM5b CM4b CM3.cof
lemma triv_fib_eq_rlp_with_cof : triv_fib = (cof : morphism_property C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5b CM4b CM3.triv_fib
lemma triv_cof_eq_llp_with_fib : triv_cof = (fib : morphism_property C).llp_with :=
factorisation_axiom.eq_llp_with CM5a CM4a CM3.triv_cof
lemma fib_eq_rlp_with_triv_cof : fib = (triv_cof : morphism_property C).rlp_with :=
factorisation_axiom.eq_rlp_with CM5a CM4a CM3.fib

lemma cof_stable_under_composition : (cof : morphism_property C).stable_under_composition :=
by { rw cof_eq_llp_with_triv_fib, apply morphism_property.llp_with.stable_under_composition, }
lemma fib_stable_under_composition : (fib : morphism_property C).stable_under_composition :=
by { rw fib_eq_rlp_with_triv_cof, apply morphism_property.rlp_with.stable_under_composition, }

instance comp_weak_eq [hp : weak_eq p] [hq : weak_eq q] : weak_eq (p ≫ q) :=
⟨CM2.of_comp p q hp.property hq.property⟩
instance comp_cofibration [hp : cofibration p] [hq : cofibration q] : cofibration (p ≫ q) :=
⟨cof_stable_under_composition p q hp.property hq.property⟩
instance comp_fibration [hp : fibration p] [hq : fibration q] : fibration (p ≫ q) :=
⟨fib_stable_under_composition p q hp.property hq.property⟩

namespace weak_eq

variables (p q)

lemma of_comp_left (hp : weak_eq p) (hpq : weak_eq (p ≫ q)) : weak_eq q :=
⟨CM2.of_comp_left p q hp.property hpq.property⟩
lemma of_comp_left' [hp : weak_eq p] [hpq : weak_eq (p ≫ q)] : weak_eq q :=
of_comp_left p q hp hpq

lemma of_comp_right (hq : weak_eq q) (hpq : weak_eq (p ≫ q)) : weak_eq p :=
⟨CM2.of_comp_right p q hq.property hpq.property⟩
lemma of_comp_right' [hq : weak_eq q] [hpq : weak_eq (p ≫ q)] : weak_eq p :=
of_comp_right p q hq hpq

end weak_eq

lemma cof_contains_iso : morphism_property.isomorphisms C ⊆ cof :=
by { rw cof_eq_llp_with_triv_fib, apply morphism_property.llp_with.contains_iso, }
lemma fib_contains_iso : morphism_property.isomorphisms C ⊆ fib :=
by { rw fib_eq_rlp_with_triv_cof, apply morphism_property.rlp_with.contains_iso, }
lemma triv_cof_contains_iso : morphism_property.isomorphisms C ⊆ triv_cof :=
by { rw triv_cof_eq_llp_with_fib, apply morphism_property.llp_with.contains_iso, }
lemma triv_fib_contains_iso : morphism_property.isomorphisms C ⊆ triv_fib :=
by { rw triv_fib_eq_rlp_with_cof, apply morphism_property.rlp_with.contains_iso, }
lemma weq_contains_iso : morphism_property.isomorphisms C ⊆ weq :=
λ X Y f hf, (triv_cof_contains_iso f hf).2

@[priority 100] instance cofibration_of_is_iso [is_iso p] : cofibration p :=
⟨cof_contains_iso p (morphism_property.isomorphisms.infer_property _)⟩
@[priority 100] instance fibration_of_is_iso [is_iso p] : fibration p :=
⟨fib_contains_iso p (morphism_property.isomorphisms.infer_property _)⟩
@[priority 100] instance weak_eq_of_is_iso [is_iso p] : weak_eq p :=
⟨weq_contains_iso p (morphism_property.isomorphisms.infer_property _)⟩

instance CM5a_cofibration : cofibration (CM5a.i f) := ⟨(CM5a.i_property f).1⟩
instance CM5a_weak_eq : weak_eq (CM5a.i f) := ⟨(CM5a.i_property f).2⟩
instance CM5a_fibration : fibration (CM5a.p f) := ⟨CM5a.p_property f⟩

instance CM5b_cofibration : cofibration (CM5b.i f) := ⟨CM5b.i_property f⟩
instance CM5b_fibration : fibration (CM5b.p f) := ⟨(CM5b.p_property f).1⟩
instance CM5b_weak_eq : weak_eq (CM5b.p f) := ⟨(CM5b.p_property f).2⟩

--lemma cof_is_stable_by_direct_image : (cof : arrow_class C).is_stable_by_direct_image :=
--by { rw cof_eq_llp_with_triv_fib, apply arrow_class.is_stable_by_direct_image.for_llp_with, }
--lemma triv_cof_is_stable_by_direct_image : (triv_cof : arrow_class C).is_stable_by_direct_image :=
--by { rw triv_cof_eq_llp_with_fib, apply arrow_class.is_stable_by_direct_image.for_llp_with, }

lemma cof_stable_under_coproducts : (cof : morphism_property C).stable_under_coproducts :=
by { rw cof_eq_llp_with_triv_fib, apply morphism_property.llp_with.stable_under_coproducts, }
lemma triv_cof_stable_under_coproducts : (triv_cof : morphism_property C).stable_under_coproducts :=
by { rw triv_cof_eq_llp_with_fib, apply morphism_property.llp_with.stable_under_coproducts, }

lemma fib_is_stable_under_base_change :
  (fib : morphism_property C).stable_under_base_change :=
by { rw fib_eq_rlp_with_triv_cof, apply morphism_property.rlp_with.stable_under_base_change, }
lemma triv_fib_is_stable_under_base_change :
  (triv_fib : morphism_property C).stable_under_base_change :=
by { rw triv_fib_eq_rlp_with_cof, apply morphism_property.rlp_with.stable_under_base_change, }

lemma fib_stable_under_products : (fib : morphism_property C).stable_under_products :=
by { rw fib_eq_rlp_with_triv_cof, apply morphism_property.rlp_with.stable_under_products, }
lemma triv_fib_stable_under_products : (triv_fib : morphism_property C).stable_under_products :=
by { rw triv_fib_eq_rlp_with_cof, apply morphism_property.rlp_with.stable_under_products, }


lemma cof_respects_iso : (cof : morphism_property C).respects_iso :=
morphism_property.respects_iso.of_stable_under_composition_and_contains_iso
  cof_stable_under_composition cof_contains_iso
lemma fib_respects_iso : (fib : morphism_property C).respects_iso :=
morphism_property.respects_iso.of_stable_under_composition_and_contains_iso
  fib_stable_under_composition fib_contains_iso
lemma weq_respects_iso : (weq : morphism_property C).respects_iso :=
morphism_property.respects_iso.of_stable_under_composition_and_contains_iso
  CM2.of_comp weq_contains_iso

namespace cofibration

lemma op (hi : cofibration i) : fibration i.op := ⟨hi.property⟩
lemma unop {A B : Cᵒᵖ} {i : A ⟶ B} (hi : cofibration i) : fibration i.unop := ⟨hi.property⟩
lemma iff_cof : cofibration i ↔ cof i := ⟨λ h, h.property, λ h, ⟨h⟩⟩

/-lemma direct_image ⦃f : A ⟶ X⦄ ⦃i : A ⟶ B⦄ ⦃i' : X ⟶ Y⦄ ⦃g : B ⟶ Y⦄
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
⟨(triv_cof_is_stable_by_coproduct.binary f₁ f₂ ⟨h₁.mem, h₁'.mem⟩ ⟨h₂.mem, h₂'.mem⟩).2⟩-/

lemma respects_iso {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  cofibration f₁ ↔ cofibration f₂ :=
by simpa only [iff_cof] using cof_respects_iso.arrow_mk_iso_iff e

end cofibration

namespace fibration

lemma op (hp : fibration p) : cofibration p.op := ⟨hp.property⟩
lemma unop {X Y : Cᵒᵖ} {p : X ⟶ Y} (hp : fibration p) : cofibration p.unop := ⟨hp.property⟩
lemma iff_fib : fibration i ↔ fib i := ⟨λ h, h.property, λ h, ⟨h⟩⟩

variable (p)
lemma iff_op : fibration p ↔ cofibration p.op := ⟨op, cofibration.unop⟩
lemma iff_unop {X Y : Cᵒᵖ} (p : X ⟶ Y) : fibration p ↔ cofibration p.unop := ⟨unop, cofibration.op⟩

lemma respects_iso {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  fibration f₁ ↔ fibration f₂ :=
by simpa only [iff_fib] using fib_respects_iso.arrow_mk_iso_iff e

end fibration

namespace cofibration

variable (p)

lemma iff_op : cofibration p ↔ fibration p.op := ⟨op, fibration.unop⟩
lemma iff_unop {X Y : Cᵒᵖ} (p : X ⟶ Y) : cofibration p ↔ fibration p.unop := ⟨unop, fibration.op⟩

end cofibration

namespace weak_eq

lemma op (hp : weak_eq p) : weak_eq p.op := ⟨hp.property⟩
lemma unop {X Y : Cᵒᵖ} {p : X ⟶ Y} (hp : weak_eq p) : weak_eq p.unop := ⟨hp.property⟩
lemma iff_weq : weak_eq i ↔ weq i := ⟨λ h, h.property, λ h, ⟨h⟩⟩

--instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hg₁ : cofibration g] [hg₂ : weak_eq g] :
--  weak_eq (pushout.inl : X₁ ⟶ pushout f g) :=
--⟨(triv_cof_is_stable_by_direct_image.for_pushout_inl f g ⟨hg₁.mem, hg₂.mem⟩).2⟩

--instance {A X₁ X₂ : C} (f : A ⟶ X₁) (g : A ⟶ X₂) [hf₁ : cofibration f] [hf₂ : weak_eq f] :
--  weak_eq (pushout.inr : X₂ ⟶ pushout f g) :=
--⟨(triv_cof_is_stable_by_direct_image.for_pushout_inr f g ⟨hf₁.mem, hf₂.mem⟩).2⟩

lemma respects_iso {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (e : arrow.mk f₁ ≅ arrow.mk f₂) :
  weak_eq f₁ ↔ weak_eq f₂ :=
by simpa only [iff_weq] using weq_respects_iso.arrow_mk_iso_iff e

end weak_eq

end model_category

end algebraic_topology
