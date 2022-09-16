/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fibrant

noncomputable theory

open category_theory category_theory.limits
open category_theory.category opposite

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

variables (A B : C)

structure precylinder  :=
(I : C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A) [weq_σ : weak_eq σ]
(σd₀' : d₀ ≫ σ = 𝟙 A . obviously) (σd₁' : d₁ ≫ σ = 𝟙 A . obviously)

namespace precylinder

variables {A} (P : precylinder A)

restate_axiom σd₀'
restate_axiom σd₁'
attribute [simp, reassoc] σd₀ σd₁

instance weq_σ' : weak_eq P.σ := P.weq_σ
instance weq_d₀ : weak_eq P.d₀ := weak_eq.of_comp_right P.d₀ P.σ infer_instance
  (by { rw σd₀, apply_instance, })
instance weq_d₁ : weak_eq P.d₁ := weak_eq.of_comp_right P.d₁ P.σ infer_instance
  (by { rw σd₁, apply_instance, })

@[simps]
def change_I {I' : C} {f : P.I ⟶ I'} {g : I' ⟶ A} (fac : f ≫ g = P.σ) [weak_eq f] :
  precylinder A :=
begin
  haveI := weak_eq.of_comp_left f g infer_instance (by {rw fac, apply_instance, }),
  exact
  { I := I',
    d₀ := P.d₀ ≫ f,
    d₁ := P.d₁ ≫ f,
    σ := g,
    σd₀' := by { simp only [assoc, fac, σd₀], },
    σd₁' := by { simp only [assoc, fac, σd₁], }, },
end

@[simp]
def ι := coprod.desc P.d₀ P.d₁

@[simps]
def symm : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ, }

end precylinder

structure cylinder extends precylinder A :=
[cof_ι : cofibration to_precylinder.ι]

namespace cylinder

variable {A}

def mk' (P : precylinder A) (h : cofibration P.ι) : cylinder A :=
by { haveI := h, exact mk P, }

abbreviation pre (Q : cylinder A) := Q.to_precylinder

instance cof_ι' (Q : cylinder A) : cofibration Q.pre.ι := Q.cof_ι

variable (A)

def some : cylinder A :=
begin
  let φ := coprod.desc (𝟙 A) (𝟙 A),
  let P : precylinder A :=
  { I := CM5b.obj φ,
    σ := CM5b.p φ,
    d₀ := coprod.inl ≫ CM5b.i φ,
    d₁ := coprod.inr ≫ CM5b.i φ, },
  apply mk' P,
  rw [show P.ι = CM5b.i φ, by tidy],
  apply_instance,
end

instance : inhabited (cylinder A) := ⟨some A⟩
instance : inhabited (precylinder A) := ⟨(some A).pre⟩

variables {A} (Q : cylinder A)

instance cof_d₀ [is_cofibrant A] : cofibration (Q.d₀) :=
begin
  rw [show Q.d₀ = coprod.inl ≫ Q.pre.ι, by simp only [precylinder.ι, coprod.inl_desc]],
  apply_instance,
end

instance cof_d₁ [is_cofibrant A] : cofibration (Q.d₁) :=
begin
  rw [show Q.d₁ = coprod.inr ≫ Q.pre.ι, by simp only [precylinder.ι, coprod.inr_desc]],
  apply_instance,
end

instance is_cofibrant_I [is_cofibrant A] : is_cofibrant Q.I :=
begin
  change cofibration _,
  rw subsingleton.elim (initial.to Q.I) (initial.to A ≫ Q.d₀),
  apply_instance,
end

@[simps]
def symm : cylinder A := mk' Q.pre.symm
begin
  have eq : Q.pre.symm.ι = (coprod.braiding A A).hom ≫ Q.pre.ι,
  { simp only [precylinder.ι, precylinder.symm_d₀, precylinder.symm_d₁, coprod.braiding_hom,
      coprod.desc_comp, coprod.inr_desc, coprod.inl_desc], },
  rw eq,
  apply_instance,
end

@[simps]
def trans [is_cofibrant A] (Q Q' : cylinder A) : cylinder A :=
begin
  let φ := pushout.desc Q.σ Q'.σ (by rw [Q.pre.σd₁, Q'.pre.σd₀]),
  haveI : weak_eq φ,
  { apply weak_eq.of_comp_left (Q.d₀ ≫ pushout.inl),
    { apply_instance, },
    { simp only [assoc, pushout.inl_desc, precylinder.σd₀],
      apply_instance, }, },
  let P : precylinder A :=
  { I := pushout Q.d₁ Q'.d₀,
    d₀ := Q.d₀ ≫ pushout.inl,
    d₁ := Q'.d₁ ≫ pushout.inr,
    σ := φ, },
  apply mk' P,
  let ψ : Q.pre.I ⨿ A ⟶ P.I := coprod.desc pushout.inl (Q'.d₁ ≫ pushout.inr),
  have eq : P.ι = (coprod.map Q.d₀ (𝟙 A)) ≫ ψ,
  { by simp only [precylinder.ι, coprod.map_desc, id_comp], },
  rw eq,
  have fac : coprod.map Q.d₁ (𝟙 A) ≫ ψ = Q'.pre.ι ≫ pushout.inr,
  { dsimp [ψ],
    ext,
    { simp only [coprod.map_desc, coprod.inl_desc, coprod.desc_comp, pushout.condition], },
    { simp only [coprod.map_desc, id_comp, coprod.inr_desc, coprod.desc_comp], }, },
  have sq : is_pushout Q.pre.d₁ (coprod.inl ≫ Q'.pre.ι)
    (coprod.inl ≫ ψ) pushout.inr := by simpa only [precylinder.ι, coprod.inl_desc]
    using is_pushout.of_has_pushout Q.pre.d₁ Q'.pre.d₀,
  haveI : cofibration ψ := cofibration.direct_image
    (is_pushout.of_bot sq fac (is_pushout.of_coprod_inl_with_id Q.d₁ A).flip),
  apply_instance,
end

end cylinder

structure pre_path_object :=
(I : C) (d₀ d₁: I ⟶ B) (σ : B ⟶ I) [weq_σ : weak_eq σ]
(d₀σ' : σ ≫ d₀ = 𝟙 B . obviously) (d₁σ' : σ ≫ d₁ = 𝟙 B . obviously)

namespace pre_path_object

restate_axiom d₀σ'
restate_axiom d₁σ'
attribute [simp, reassoc] d₀σ d₁σ

variables {B} (P : pre_path_object B)

instance : weak_eq P.σ := P.weq_σ

@[simps]
def op (P : pre_path_object B) : precylinder (op B) :=
begin
  haveI : weak_eq P.σ.op := weak_eq.op infer_instance,
  exact
  { I := op P.I,
    d₀ := P.d₀.op,
    d₁ := P.d₁.op,
    σ := P.σ.op,
    σd₀' := by simp only [← op_comp, d₀σ, op_id],
    σd₁' := by simp only [← op_comp, d₁σ, op_id], }
end

@[simps]
def unop {B : Cᵒᵖ} (P : pre_path_object B) : precylinder B.unop :=
begin
  haveI : weak_eq P.σ.unop := weak_eq.unop infer_instance,
  exact
  { I := unop P.I,
    d₀ := P.d₀.unop,
    d₁ := P.d₁.unop,
    σ := P.σ.unop,
    σd₀' := by simp only [← unop_comp, d₀σ, unop_id],
    σd₁' := by simp only [← unop_comp, d₁σ, unop_id], }
end

end pre_path_object

namespace precylinder

variable {A}

@[simps]
def op (P : precylinder A) : pre_path_object (op A) :=
begin
  haveI : weak_eq P.σ.op := weak_eq.op infer_instance,
  exact
  { I := op P.I,
    d₀ := P.d₀.op,
    d₁ := P.d₁.op,
    σ := P.σ.op,
    d₀σ' := by simp only [← op_comp, σd₀, op_id],
    d₁σ' := by simp only [← op_comp, σd₁, op_id], }
end

@[simps]
def unop {A : Cᵒᵖ} (P : precylinder A) : pre_path_object (unop A) :=
begin
  haveI : weak_eq P.σ.unop := weak_eq.unop infer_instance,
  exact
  { I := unop P.I,
    d₀ := P.d₀.unop,
    d₁ := P.d₁.unop,
    σ := P.σ.unop,
    d₀σ' := by simp only [← unop_comp, σd₀, unop_id],
    d₁σ' := by simp only [← unop_comp, σd₁, unop_id], }
end

lemma unop_op (P : precylinder A) : P.op.unop = P := by { cases P, refl, }
lemma op_unop {A : Cᵒᵖ} (P : precylinder A) : P.unop.op = P := by { cases P, refl, }

end precylinder

namespace pre_path_object

variables {B} (P : pre_path_object B)

lemma unop_op : P.op.unop = P := by { cases P, refl, }
lemma op_unop {B : Cᵒᵖ} (P : precylinder B) : P.unop.op = P := by { cases P, refl, }

instance weq_d₀ : weak_eq P.d₀ := weak_eq.unop (infer_instance : weak_eq P.op.d₀)
instance weq_d₁ : weak_eq P.d₁ := weak_eq.unop (infer_instance : weak_eq P.op.d₁)

@[simps]
def change_I {I' : C} {f : I' ⟶ P.I} {g : B ⟶ I'} (fac : g ≫ f = P.σ) [weak_eq f] :
  pre_path_object B :=
begin
  haveI : weak_eq f.op := weak_eq.op infer_instance,
  have eq : f.op ≫ g.op = P.σ.op := by rw [← op_comp, fac],
  exact (P.op.change_I eq).unop,
end

@[simp]
def π := prod.lift P.d₀ P.d₁

lemma fibration_π_iff_cofibration_op_ι (P : pre_path_object B) :
  fibration P.π ↔ cofibration P.op.ι :=
by simpa only [fibration.iff_op]
  using cofibration.respects_iso _ _ (arrow.iso_op_prod_lift P.d₀ P.d₁)

lemma fibration_π_iff_cofibration_unop_ι {B : Cᵒᵖ} (P : pre_path_object B) :
  fibration P.π ↔ cofibration P.unop.ι :=
by simpa only [fibration.iff_unop]
  using cofibration.respects_iso _ _ (arrow.iso_unop_prod_lift P.d₀ P.d₁)

@[simps]
def symm : pre_path_object B :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ, }

end pre_path_object

structure path_object extends pre_path_object B :=
[fib_π : fibration to_pre_path_object.π]

namespace path_object

variable {B}

def mk' (P : pre_path_object B) (h : fibration P.π) : path_object B :=
by { haveI := h, exact mk P, }

abbreviation pre (Q : path_object B) := Q.to_pre_path_object

instance (Q : path_object B) : fibration Q.pre.π := Q.fib_π

@[simps]
def change_I {B : C} (P : path_object B) {Z : C} {f : B ⟶ Z} {g : Z ⟶ P.I}
  (fac : f ≫ g = P.σ) [fibration g] [weak_eq g] : path_object B :=
begin
  haveI : fibration (P.pre.change_I fac).π,
  { convert (infer_instance : fibration (g ≫ P.π)),
    simp only [pre_path_object.π, pre_path_object.change_I_d₀,
      pre_path_object.change_I_d₁, prod.comp_lift], },
  exact path_object.mk (P.pre.change_I fac),
end

end path_object

namespace cylinder

@[simps]
def unop {A : Cᵒᵖ} (Q : cylinder A) : path_object A.unop :=
begin
  apply path_object.mk' Q.pre.unop,
  rw [pre_path_object.fibration_π_iff_cofibration_op_ι, precylinder.op_unop],
  apply_instance,
end

variable {A}

@[simps]
def op (Q : cylinder A) : path_object (op A) :=
begin
  apply path_object.mk' Q.pre.op,
  rw [pre_path_object.fibration_π_iff_cofibration_unop_ι, precylinder.unop_op],
  apply_instance,
end

end cylinder

namespace path_object

variable {B}

@[simps]
def op (Q : path_object B) : cylinder (op B) :=
begin
  apply cylinder.mk' Q.pre.op,
  rw ← Q.pre.fibration_π_iff_cofibration_op_ι,
  apply_instance,
end

@[simps]
def unop {B : Cᵒᵖ} (Q : path_object B) : cylinder B.unop :=
begin
  apply cylinder.mk' Q.pre.unop,
  rw ← Q.pre.fibration_π_iff_cofibration_unop_ι,
  apply_instance,
end

variable (B)

def some : path_object B := (cylinder.some (opposite.op B)).unop

instance : inhabited (path_object B) := ⟨some B⟩
instance : inhabited (pre_path_object B) := ⟨(some B).pre⟩

variable {B}

@[simp]
def symm (P : path_object B) : path_object B := P.op.symm.unop

@[simps]
def trans [hB : is_fibrant B] (P P' : path_object B) : path_object B :=
by { haveI := hB.op, exact (P.op.trans P'.op).unop, }
/- TODO : use change_I to replace the dual of the pushout by a pullback -/

end path_object

end model_category

end algebraic_topology
