/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fibrant

noncomputable theory

open category_theory category_theory.limits
open category_theory.category

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

variable (A : C)
structure precylinder  :=
(I : C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A) [weq_σ : weak_eq σ]
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)

namespace precylinder

variables {A} (P : precylinder A)

@[simp, reassoc] lemma d₀_comp_σ : P.d₀ ≫ P.σ = 𝟙 A := P.σd₀
@[simp, reassoc] lemma d₁_comp_σ : P.d₁ ≫ P.σ = 𝟙 A := P.σd₁

instance weq_σ' : weak_eq P.σ := P.weq_σ
instance weq_d₀ : weak_eq P.d₀ := weak_eq.of_comp_right P.d₀ P.σ infer_instance
  (by { rw [d₀_comp_σ], apply_instance, })
instance weq_d₁ : weak_eq P.d₁ := weak_eq.of_comp_right P.d₁ P.σ infer_instance
  (by { rw [d₁_comp_σ], apply_instance, })

def change_I {I' : C} {f : P.I ⟶ I'} {g : I' ⟶ A} (fac : f ≫ g = P.σ) [weak_eq f] :
  precylinder A :=
begin
  haveI := weak_eq.of_comp_left f g infer_instance (by {rw fac, apply_instance, }),
  exact 
  { I := I',
    d₀ := P.d₀ ≫ f,
    d₁ := P.d₁ ≫ f,
    σ := g,
    σd₀ := by { simp only [assoc, fac, d₀_comp_σ], },
    σd₁ := by { simp only [assoc, fac, d₁_comp_σ], }, },
end

@[simp]
def ι := coprod.desc P.d₀ P.d₁

@[simps]
def symm : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀, }

end precylinder

structure cylinder extends precylinder A :=
[cof_ι : cofibration to_precylinder.ι]

namespace cylinder

variable {A}

def mk' (P : precylinder A) (h : cofibration P.ι) : cylinder A :=
by { haveI := h, exact mk P, }

instance cof_ι' (Q : cylinder A) : cofibration Q.to_precylinder.ι := Q.cof_ι

variable (A)

def some : cylinder A :=
begin
  let φ := coprod.desc (𝟙 A) (𝟙 A),
  let P : precylinder A :=
  { I := CM5b.obj φ,
    σ := CM5b.p φ,
    d₀ := coprod.inl ≫ CM5b.i φ,
    d₁ := coprod.inr ≫ CM5b.i φ,
    σd₀ := by { dsimp [φ], simp only [assoc, factorisation_axiom.fac, coprod.inl_desc], },
    σd₁ := by { dsimp [φ], simp only [assoc, factorisation_axiom.fac, coprod.inr_desc], }, },
  apply mk' P,
  rw [show P.ι = CM5b.i φ, by tidy],
  apply_instance,
end

instance : inhabited (cylinder A) := ⟨some A⟩
instance : inhabited (precylinder A) := ⟨(some A).to_precylinder⟩

variables {A} (Q : cylinder A)

instance cof_d₀ [is_cofibrant A] : cofibration (Q.d₀) :=
begin
  rw [show Q.d₀ = coprod.inl ≫ Q.to_precylinder.ι, by simp only [precylinder.ι, coprod.inl_desc]],
  apply_instance,
end

instance cof_d₁ [is_cofibrant A] : cofibration (Q.d₁) :=
begin
  rw [show Q.d₁ = coprod.inr ≫ Q.to_precylinder.ι, by simp only [precylinder.ι, coprod.inr_desc]],
  apply_instance,
end

@[simps]
def symm : cylinder A := mk' Q.to_precylinder.symm
begin
  have eq : Q.to_precylinder.symm.ι = (coprod.braiding A A).hom ≫ Q.to_precylinder.ι,
  { simp only [precylinder.ι, precylinder.symm_d₀, precylinder.symm_d₁, coprod.braiding_hom,
      coprod.desc_comp, coprod.inr_desc, coprod.inl_desc], },
  rw eq,
  apply_instance,
end

def is_pushout_ad_hoc {A B : C} (f : A ⟶ B) (X : C) :
  is_pushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl :=
is_pushout.of_is_colimit' (comm_sq.mk (coprod.inl_map f (𝟙 X)))
{ desc := λ s, coprod.desc (s.ι.app walking_span.right) (coprod.inr ≫ s.ι.app walking_span.left),
  fac' := λ s, begin
    have h₁ := s.ι.naturality walking_span.hom.fst,
    have h₂ := s.ι.naturality walking_span.hom.snd,
    dsimp at h₁ h₂,
    simp only [comp_id] at h₁ h₂,
    have eq : f ≫ s.ι.app walking_span.right = coprod.inl ≫ pushout_cocone.inl s,
    { rw [h₂, ← h₁], },
    rintro (_|_|_),
    { dsimp, simpa only [coprod.inl_map, assoc, coprod.inl_desc, pushout_cocone.condition_zero] using eq, },
    { ext,
      { simpa only [comm_sq.cocone_ι_app, coprod.map_desc, coprod.inl_desc] using eq, },
      { simp only [comm_sq.cocone_ι_app, coprod.map_desc, id_comp, coprod.inr_desc], }, },
    { simp only [comm_sq.cocone_ι_app, coprod.inl_desc], },
  end,
  uniq' := λ s g h, begin
    have h₁ := h walking_span.left,
    have h₂ := h walking_span.right,
    dsimp at h₁ h₂,
    ext,
    { simp only [h₂, coprod.inl_desc], },
    { simp only [← h₁, coprod.inr_map_assoc, id_comp, coprod.inr_desc], },
  end, }

@[simps]
def trans [is_cofibrant A] (Q Q' : cylinder A) : cylinder A :=
begin
  let φ := pushout.desc Q.σ Q'.σ (by rw [Q.σd₁, Q'.σd₀]),
  haveI : weak_eq φ,
  { apply weak_eq.of_comp_left (Q.d₀ ≫ pushout.inl),
    { apply_instance, },
    { simp only [assoc, pushout.inl_desc, precylinder.d₀_comp_σ],
      apply_instance, }, },
  let P : precylinder A :=
  { I := pushout Q.d₁ Q'.d₀,
    d₀ := Q.d₀ ≫ pushout.inl,
    d₁ := Q'.d₁ ≫ pushout.inr,
    σ := φ,
    σd₀ := by simp only [assoc, pushout.inl_desc, precylinder.d₀_comp_σ],
    σd₁ := by simp only [assoc, pushout.inr_desc, precylinder.d₁_comp_σ], },
  apply mk' P,
  let ψ : Q.to_precylinder.I ⨿ A ⟶ P.I := coprod.desc pushout.inl (Q'.d₁ ≫ pushout.inr),
  have eq : P.ι = (coprod.map Q.d₀ (𝟙 A)) ≫ ψ,
  { by simp only [precylinder.ι, coprod.map_desc, id_comp], },
  rw eq,
  have fac₂ : coprod.map Q.d₁ (𝟙 A) ≫ ψ = Q'.to_precylinder.ι ≫ pushout.inr,
  { dsimp [ψ],
    ext,
    { simp only [coprod.map_desc, coprod.inl_desc, coprod.desc_comp, pushout.condition], },
    { simp only [coprod.map_desc, id_comp, coprod.inr_desc, coprod.desc_comp], }, },
  have sq₁ := is_pushout_ad_hoc Q'.d₁ A,
  have sq₂ := comm_sq.mk fac₂,
/-  have sq₁₂ := comm_sq.paste_vert sq₁.to_comm_sq sq₂,
  have sq₃ := is_pushout_ad_hoc (Q'.d₁ ≫ pushout.inr : A ⟶ P.I) A,
  have foo := is_pushout.of_bot (sq₃) fac₂,
  let sq := is_pushout.of_is_colimit' (comm_sq.mk fac₂) sorry,-/
  haveI : cofibration ψ,
  { refine cofibration.direct_image (is_pushout.of_is_colimit' (comm_sq.mk fac₂) _),
    sorry, },
  apply_instance,
end

end cylinder

end model_category

end algebraic_topology
