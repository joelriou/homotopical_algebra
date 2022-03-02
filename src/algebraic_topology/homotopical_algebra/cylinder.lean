/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cofibrant

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open algebraic_topology

variables {M : model_category}

namespace algebraic_topology

namespace model_category

structure precylinder (A : M.C) :=
(I : M.C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A)
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)
(Wσ : arrow.mk σ ∈ M.W)

structure cylinder (A : M.C) extends precylinder A :=
(cof : arrow.mk (coprod.desc d₀ d₁) ∈ M.cof)

lemma cylinder_exists (A : M.C) : ∃ (C : cylinder A), arrow.mk C.σ ∈ M.fib :=
begin
  rcases M.CM5b (arrow.mk (coprod.desc (𝟙 A) (𝟙 A))) with ⟨Z, i, p, fac, ⟨hi, hp⟩⟩,
  let C : cylinder A :=
  { I := Z,
    d₀ := coprod.inl ≫ i,
    d₁ := coprod.inr ≫ i,
    σ := p,
    σd₀ := by rw [assoc, ← fac, arrow.mk_hom, coprod.inl_desc],
    σd₁ := by rw [assoc, ← fac, arrow.mk_hom, coprod.inr_desc],
    Wσ := hp.2,
    cof := begin
      convert hi,
      ext,
      { simp only [coprod.inl_desc], },
      { simp only [coprod.inr_desc], },
     end },
  use [C, hp.1],
end

def path_object (A : M.C) := @cylinder M.op (opposite.op A)

namespace path_object

variables {A : M.C} (P : path_object A)
def I' : M.C := opposite.unop P.I
def d₀' : P.I' ⟶ A := P.d₀.unop
def d₁' : P.I' ⟶ A := P.d₁.unop
def σ' : A ⟶ P.I' := P.σ.unop
def σd₀' : P.σ' ≫ P.d₀' = 𝟙 A := by { apply quiver.hom.op_inj, exact P.σd₀, }
def σd₁' : P.σ' ≫ P.d₁' = 𝟙 A := by { apply quiver.hom.op_inj, exact P.σd₁, }
def Wσ' : arrow.mk P.σ' ∈ M.W := P.Wσ

end path_object

variable {M}

namespace precylinder

def Wd₀ {A : M.C} (P : precylinder A) : arrow.mk P.d₀ ∈ M.W :=
begin
  apply M.CM2.of_comp_right P.d₀ P.σ P.Wσ,
  rw P.σd₀,
  apply M.W_contains_iso,
  exact is_iso.of_iso (iso.refl A),
end

def Wd₁ {A : M.C} (P : precylinder A) : arrow.mk P.d₁ ∈ M.W :=
begin
  apply M.CM2.of_comp_right P.d₁ P.σ P.Wσ,
  rw P.σd₁,
  apply M.W_contains_iso,
  exact is_iso.of_iso (iso.refl A),
end

structure left_homotopic {A B : M.C} (P : precylinder A) (f g : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f) (h₁ : P.d₁ ≫ h = g)

def symm {A : M.C} (P : precylinder A) : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀,
  Wσ := P.Wσ, }

end precylinder

namespace cylinder

def cof_d₀ {A : M.C} (C : cylinder A) (hA : is_cofibrant A) :
  arrow.mk C.d₀ ∈ M.cof :=
begin
  have h := M.cof_co_bc_stable.for_coprod_inl A A hA,
  convert M.cof_comp_stable _ _ _ _ _ h C.cof,
  simp only [coprod.inl_desc],
end

def cof_d₁ {A : M.C} (C : cylinder A) (hA : is_cofibrant A) :
  arrow.mk C.d₁ ∈ M.cof :=
begin
  have h := M.cof_co_bc_stable.for_coprod_inr A A hA,
  convert M.cof_comp_stable _ _ _ _ _ h C.cof,
  erw coprod.inr_desc,
end

def trans {A : M.C} (C : cylinder A) (C' : cylinder A) (hA : is_cofibrant A) : cylinder A :=
{ I := pushout C.d₁ C'.d₀,
  d₀ := C.d₀ ≫ pushout.inl,
  d₁ := C'.d₁ ≫ pushout.inr,
  σ := pushout.desc C.σ C'.σ (by rw [C.σd₁, C'.σd₀]),
  σd₀ := by { rw [category.assoc, pushout.inl_desc], exact C.σd₀, },
  σd₁ := by { rw [category.assoc, pushout.inr_desc], exact C'.σd₁, },
  cof := begin
    dsimp,
    sorry,
  end,
  Wσ := begin
    apply M.CM2.of_comp_left (C.d₀ ≫ pushout.inl ),
    { apply M.triv_cof_contains_W,
      apply M.triv_cof_comp_stable,
      { exact ⟨C.cof_d₀ hA, C.to_precylinder.Wd₀⟩, },
      { apply M.triv_cof_co_bc_stable.for_pushout_inl,
        exact ⟨C'.cof_d₀ hA, C'.to_precylinder.Wd₀⟩, } },
    { rw [assoc, pushout.inl_desc, C.σd₀],
      apply W_contains_iso,
      exact is_iso.of_iso (iso.refl A), },
  end, }

end cylinder

namespace left_homotopic

def refl {A B : M.C} {P : precylinder A} (f : A ⟶ B) : P.left_homotopic f f :=
{ h := P.σ ≫ f,
  h₀ := by rw [← assoc, P.σd₀, id_comp],
  h₁ := by rw [← assoc, P.σd₁, id_comp], }

def symm {A B : M.C} (P : precylinder A) {f g : A ⟶ B} (H : P.left_homotopic f g) :
  P.symm.left_homotopic g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

def trans {A B : M.C} (P P' : cylinder A) (hA : is_cofibrant A) {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : P.to_precylinder.left_homotopic f₁ f₂) (H₂ : P'.to_precylinder.left_homotopic f₂ f₃) :
    (P.trans P' hA).to_precylinder.left_homotopic f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by rw [H₁.h₁, H₂.h₀]),
  h₀ := by erw [category.assoc, pushout.inl_desc, H₁.h₀],
  h₁ := by erw [category.assoc, pushout.inr_desc, H₂.h₁], }

end left_homotopic

namespace path_object

structure right_homotopic {A B : M.C} (P : path_object B) (f g : A ⟶ B) :=
(h : A ⟶ P.I') (h₀ : h ≫ P.d₀' = f) (h₁ : h ≫ P.d₁' = g)

end path_object

end model_category

end algebraic_topology