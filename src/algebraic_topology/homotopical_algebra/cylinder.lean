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

namespace precylinder

@[simp]
def ι {A : M.C} (P : precylinder A) := coprod.desc P.d₀ P.d₁

@[simp]
def cof_ι {A : M.C} (P : precylinder A) := arrow.mk P.ι ∈ M.cof

end precylinder

structure cylinder (A : M.C) extends precylinder A :=
(cof_ι : to_precylinder.cof_ι)

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
    cof_ι := begin
      dsimp only [precylinder.cof_ι],
      convert hi,
      ext,
      { simp only [precylinder.ι, coprod.inl_desc], },
      { simp only [precylinder.ι, coprod.inr_desc], },
     end },
  use [C, hp.1],
end

def pre_path_object (A : M.C) := @precylinder M.op (opposite.op A)
def path_object (A : M.C) := @cylinder M.op (opposite.op A)

namespace pre_path_object

variables {B : M.C} (P : pre_path_object B)
def I' : M.C := opposite.unop P.I
def d₀' : P.I' ⟶ B := P.d₀.unop
def d₁' : P.I' ⟶ B := P.d₁.unop
def σ' : B ⟶ P.I' := P.σ.unop
def σd₀' : P.σ' ≫ P.d₀' = 𝟙 B := by { apply quiver.hom.op_inj, exact P.σd₀, }
def σd₁' : P.σ' ≫ P.d₁' = 𝟙 B := by { apply quiver.hom.op_inj, exact P.σd₁, }
def Wσ' : arrow.mk P.σ' ∈ M.W := P.Wσ
@[simp]
def π := prod.lift P.d₀' P.d₁'

def fib_π := arrow.mk P.π ∈ M.fib

lemma fib_π_iff_cof_ι_op {B : M.C} (P : pre_path_object B) :
  P.fib_π ↔ P.cof_ι := sorry

end pre_path_object

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

structure left_homotopy {A B : M.C} (P : precylinder A) (f₀ f₁ : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f₀) (h₁ : P.d₁ ≫ h = f₁)

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

def cof_d₀ {A : M.C} [hA : is_cofibrant A] (C : cylinder A) :
  arrow.mk C.d₀ ∈ M.cof :=
begin
  have h := M.cof_co_bc_stable.for_coprod_inl A A hA.cof,
  convert M.cof_comp_stable _ _ _ _ _ h C.cof_ι,
  simp only [precylinder.ι, coprod.inl_desc],
end

def cof_d₁ {A : M.C} [hA : is_cofibrant A] (C : cylinder A) :
  arrow.mk C.d₁ ∈ M.cof :=
begin
  have h := M.cof_co_bc_stable.for_coprod_inr A A hA.cof,
  convert M.cof_comp_stable _ _ _ _ _ h C.cof_ι,
  erw coprod.inr_desc,
end

def trans {A : M.C} [is_cofibrant A] (C : cylinder A) (C' : cylinder A) : cylinder A :=
{ I := pushout C.d₁ C'.d₀,
  d₀ := C.d₀ ≫ pushout.inl,
  d₁ := C'.d₁ ≫ pushout.inr,
  σ := pushout.desc C.σ C'.σ (by rw [C.σd₁, C'.σd₀]),
  σd₀ := by { rw [category.assoc, pushout.inl_desc], exact C.σd₀, },
  σd₁ := by { rw [category.assoc, pushout.inr_desc], exact C'.σd₁, },
  cof_ι := begin
    dsimp only [precylinder.cof_ι],
    convert M.cof_comp_stable _ _ _ (coprod.map C.d₀ (𝟙 A)) (coprod.desc pushout.inl (C'.d₁ ≫ pushout.inr)) _ _,
    { simp only [precylinder.ι, coprod.map_desc, id_comp], },
    { rw cof_equals_llp_triv_fib,
      apply M.triv_fib.is_stable_by_binary_coproduct_of_llp_with (arrow.mk _) (arrow.mk _),
      { rw ← cof_equals_llp_triv_fib,
        exact C.cof_d₀, },
      { apply arrow_class.contains_isomorphisms_of_llp_with,
        exact is_iso.of_iso (iso.refl A), }, },
    { let φ : _ ⟶ pushout C.d₁ C'.d₀ :=
        coprod.desc pushout.inl (C'.d₁ ≫ pushout.inr),
      let Sq₂ := square.mk'' C'.to_precylinder.ι φ (coprod.map C.d₁ (𝟙 A)) pushout.inr begin
        ext,
        { simp only [precylinder.ι, coprod.map_desc, coprod.inl_desc, coprod.desc_comp, pushout.condition], },
        { simp only [precylinder.ι, coprod.map_desc, coprod.inr_desc, coprod.desc_comp, id_comp], },
      end,
      refine M.cof_co_bc_stable Sq₂ _ C'.cof_ι,
      let hSq₁ := (coprod_inl_with_identity_is_cocartesian (arrow.mk C.d₁) A).flip,
      apply Sq₂.is_cocartesian_of_top_comp _ (eq_to_iso (by tidy))  hSq₁,
      { convert pushout_square_is_cocartesian C.to_precylinder.d₁ C'.to_precylinder.d₀,
        dsimp [φ, arrow.binary_coproduct_cofan],
        tidy, }, }
  end,
  Wσ := begin
    apply M.CM2.of_comp_left (C.d₀ ≫ pushout.inl ),
    { apply M.triv_cof_contains_W,
      apply M.triv_cof_comp_stable,
      { exact ⟨C.cof_d₀, C.to_precylinder.Wd₀⟩, },
      { apply M.triv_cof_co_bc_stable.for_pushout_inl,
        exact ⟨C'.cof_d₀, C'.to_precylinder.Wd₀⟩, } },
    { rw [assoc, pushout.inl_desc, C.σd₀],
      apply W_contains_iso,
      exact is_iso.of_iso (iso.refl A), },
  end, }

end cylinder

namespace left_homotopy

def refl {A B : M.C} {P : precylinder A} (f : A ⟶ B) : P.left_homotopy f f :=
{ h := P.σ ≫ f,
  h₀ := by rw [← assoc, P.σd₀, id_comp],
  h₁ := by rw [← assoc, P.σd₁, id_comp], }

def symm {A B : M.C} (P : precylinder A) {f g : A ⟶ B} (H : P.left_homotopy f g) :
  P.symm.left_homotopy g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

def trans {A B : M.C} [is_cofibrant A] (P P' : cylinder A) {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : P.to_precylinder.left_homotopy f₁ f₂) (H₂ : P'.to_precylinder.left_homotopy f₂ f₃) :
    (P.trans P').to_precylinder.left_homotopy f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by rw [H₁.h₁, H₂.h₀]),
  h₀ := by erw [category.assoc, pushout.inl_desc, H₁.h₀],
  h₁ := by erw [category.assoc, pushout.inr_desc, H₂.h₁], }

end left_homotopy

namespace pre_path_object

structure right_homotopy {A B : M.C} (P : pre_path_object B) (f₀ f₁ : A ⟶ B) :=
(h : A ⟶ P.I') (h₀ : h ≫ P.d₀' = f₀) (h₁ : h ≫ P.d₁' = f₁)

end pre_path_object

namespace path_object

abbreviation pre {B : M.C} (P : path_object B) : pre_path_object B := P.to_precylinder

@[protected]
def op {B : M.C} (P : path_object B) : cylinder _ := P

def fib_π {B : M.C} (P : path_object B) : arrow.mk P.pre.π ∈ M.fib :=
P.pre.fib_π_iff_cof_ι_op.mpr P.cof_ι

def right_homotopy_of_left_homotopy {A B : M.C} [is_cofibrant A] (P : path_object B) (C : cylinder A)
  (f₀ f₁ : A ⟶ B) (Hl : C.to_precylinder.left_homotopy f₀ f₁) : P.pre.right_homotopy f₀ f₁ :=
begin
  have foo := Hl.h,
  let sq : arrow.mk C.d₀ ⟶ arrow.mk P.pre.π :=
  { left := f₀ ≫ P.pre.σ',
    right := prod.lift (C.σ ≫ f₀) Hl.h,
    w' := begin
      dsimp [pre_path_object.π],
      ext,
      { erw [assoc, prod.lift_fst, assoc, P.pre.σd₀', comp_id, assoc,
          prod.lift_fst, ← assoc, C.σd₀, id_comp], },
      { simp only [assoc, prod.lift_snd, P.pre.σd₁', comp_id, Hl.h₀], },
    end },
  have h := (M.CM4b _ _ ⟨C.cof_d₀, C.to_precylinder.Wd₀⟩ P.fib_π).sq_has_lift,
  let l := (h sq).exists_lift.some,
  have hr₀ := congr_arg (λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.fst) l.fac_right,
  have hr₁ := congr_arg (λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.snd) l.fac_right,
  dsimp at hr₀ hr₁,
  simp only [prod.comp_lift, prod.lift_snd, prod.lift_fst] at hr₀ hr₁,
  exact
  { h := C.d₁ ≫ l.lift,
    h₀ := by erw [assoc, hr₀, ← assoc, C.σd₁, id_comp],
    h₁ := by { erw [assoc, hr₁, Hl.h₁], }, },
end

end path_object

namespace precylinder

@[protected]
def op {A : M.C} (C : precylinder A) : @pre_path_object M.op (opposite.op A) :=
{ I := opposite.op (opposite.op C.I),
  d₀ := C.d₀.op.op,
  d₁ := C.d₁.op.op,
  σ := C.σ.op.op,
  σd₀ := by simpa only [← op_comp, C.σd₀],
  σd₁ := by simpa only [← op_comp, C.σd₁],
  Wσ := C.Wσ, }

end precylinder

namespace cylinder

@[protected]
def op {A : M.C} (C : cylinder A) : @path_object M.op (opposite.op A) :=
{ to_precylinder := C.to_precylinder.op,
  cof_ι := sorry, }

def left_homotopy_of_right_homotopy {A B : M.C} [hB : is_fibrant B] (C : cylinder A) (P : path_object B)
  (f₀ f₁ : A ⟶ B) (Hr : P.pre.right_homotopy f₀ f₁) :
  C.to_precylinder.left_homotopy f₀ f₁ :=
begin
  let C' := P.op,
  let P' := C.op,
  let Hl' : C'.to_precylinder.left_homotopy f₀.op f₁.op :=
  { h := Hr.h.op,
    h₀ := quiver.hom.unop_inj Hr.h₀,
    h₁ := quiver.hom.unop_inj Hr.h₁, },
  haveI : @is_cofibrant M.op (opposite.op B) := sorry,
  let Hr' := P'.right_homotopy_of_left_homotopy C' f₀.op f₁.op Hl',
  exact
  { h := Hr'.h.unop,
    h₀ := quiver.hom.op_inj Hr'.h₀,
    h₁ := quiver.hom.op_inj Hr'.h₁, },
end

end cylinder

end model_category

end algebraic_topology