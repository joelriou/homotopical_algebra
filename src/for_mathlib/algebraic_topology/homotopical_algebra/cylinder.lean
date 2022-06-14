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

variable (A : C)
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

def pre_path_object (A : C) := precylinder (op A)
def path_object (A : C) := cylinder (op A)

namespace pre_path_object

variables {A} (P : pre_path_object A)

def I' := P.I.unop
def d₀' : P.I' ⟶ A := P.d₀.unop
def d₁' : P.I' ⟶ A := P.d₁.unop
def σ' : A ⟶ P.I' := P.σ.unop
instance : weak_eq P.σ' := P.weq_σ.unop
instance : weak_eq P.d₀' := P.weq_d₀.unop
instance : weak_eq P.d₁' := P.weq_d₁.unop

lemma d₀σ' : P.σ' ≫ P.d₀' = 𝟙 A :=
by { apply quiver.hom.op_inj, exact precylinder.σd₀ P, }

lemma d₁σ' : P.σ' ≫ P.d₁' = 𝟙 A :=
by { apply quiver.hom.op_inj, exact precylinder.σd₁ P, }

def change_I' {I' : C} {f : I' ⟶ P.I'} {g : A ⟶ I'} (fac : g ≫ f = P.σ') [hf : weak_eq f] :
  pre_path_object A :=
begin
  haveI : weak_eq f.op := hf.op,
  exact P.change_I (show f.op ≫ g.op = P.σ, by simpa only [← op_comp, fac]),
end

def π := prod.lift P.d₀' P.d₁'

lemma fibration_π_iff_cofibration_ι (P : pre_path_object A) :
  fibration P.π ↔ cofibration P.ι :=
by simpa only [fibration.iff_op]
  using cofibration.iso_invariance _ _ (arrow.iso_op_prod_lift P.d₀' P.d₁')

end pre_path_object

end model_category

end algebraic_topology
