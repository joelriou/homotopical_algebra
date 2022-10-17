/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.split_simplicial_object
import for_mathlib.dold_kan.functor_gamma
import for_mathlib.inclusions_mono

noncomputable theory

open category_theory category_theory.limits opposite
open_locale simplicial

namespace simplicial_object

namespace splitting

namespace index_set

@[simp]
def truncated (d : ℕ) (Δ : simplex_categoryᵒᵖ) :=
{ A : splitting.index_set Δ // A.1.unop.len ≤ d }

def truncated.id (Δ : simplex_categoryᵒᵖ) : truncated Δ.unop.len Δ := ⟨index_set.id Δ, by refl⟩

def truncated.pull {d : ℕ} {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (B : truncated d Δ₁)
  (θ : Δ₁ ⟶ Δ₂) : truncated d Δ₂ :=
⟨B.1.pull θ, (simplex_category.len_le_of_mono
  (infer_instance : mono (image.ι (θ.unop ≫ B.val.e)))).trans B.2⟩

def truncated.fac_pull {d : ℕ} {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (B : truncated d Δ₁)
  (θ : Δ₁ ⟶ Δ₂) : (B.pull θ).1.e ≫ image.ι (θ.unop ≫ B.1.e) = θ.unop ≫ B.1.e :=
B.1.fac_pull θ

instance (d : ℕ) (Δ : simplex_categoryᵒᵖ) : fintype (truncated d Δ ) :=
by { dsimp, apply_instance, }

end index_set

variables {C : Type*} [category C] [has_finite_coproducts C]
  {X : simplicial_object C} (s : splitting X)

def sk_obj (d : ℕ) (Δ : simplex_categoryᵒᵖ) : C :=
sigma_obj (λ (B : index_set.truncated d Δ), summand (s.N) Δ B.1)

def sk_ι_app (d : ℕ) (Δ : simplex_categoryᵒᵖ) : (s.sk_obj d Δ) ⟶ X.obj Δ :=
sigma.desc (λ B, s.ι_summand B.1)

def ι_summand_sk (d : ℕ) {Δ : simplex_categoryᵒᵖ} (B : index_set.truncated d Δ) :
  s.N B.1.1.unop.len ⟶ s.sk_obj d Δ := sigma.ι _ B

def sk_desc (d : ℕ) (Δ : simplex_categoryᵒᵖ) {Z : C}
  (F : Π (B : index_set.truncated d Δ), s.N B.1.1.unop.len ⟶ Z) :
  s.sk_obj d Δ ⟶ Z := sigma.desc F

@[simp, reassoc]
lemma ι_summand_sk_desc (d : ℕ) (Δ : simplex_categoryᵒᵖ) {Z : C}
  (F : Π (B : index_set.truncated d Δ), s.N B.1.1.unop.len ⟶ Z) (B : index_set.truncated d Δ) :
  s.ι_summand_sk d B ≫ s.sk_desc d Δ F = F B :=
begin
  dsimp only [ι_summand_sk, sk_desc],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

def sk_obj_hom_ext (d : ℕ) (Δ : simplex_categoryᵒᵖ) {Z : C} (f₁ f₂ : s.sk_obj d Δ ⟶ Z)
  (h : ∀ (B : index_set.truncated d Δ), s.ι_summand_sk d B ≫ f₁ =
    s.ι_summand_sk d B ≫ f₂) : f₁ = f₂ :=
begin
  ext B,
  discrete_cases,
  exact h B,
end

@[simp, reassoc]
lemma ι_summand_sk_ι (d : ℕ) {Δ : simplex_categoryᵒᵖ} (B : index_set.truncated d Δ) :
  s.ι_summand_sk d B ≫ s.sk_ι_app d Δ = s.ι_summand B.1 :=
begin
  dsimp only [ι_summand_sk],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

instance (d : ℕ) (Δ : simplex_categoryᵒᵖ) [mono_coprod C] : mono (s.sk_ι_app d Δ) :=
begin
  let α : (s.sk_obj d Δ) ⟶ sigma_obj (splitting.summand s.N Δ) :=
    sigma.desc (λ (B : index_set.truncated d Δ), splitting.ι_coprod s.N B.1),
  haveI : mono α,
  { apply mono_coprod.mono_inclusion_sub_coproduct,
    intros B₁ B₂ h,
    ext1,
    exact h, },
  have eq : s.sk_ι_app d Δ = α ≫ (s.iso Δ).hom,
  { ext B,
    simpa only [sk_ι_app, colimit.ι_desc, colimit.ι_desc_assoc], },
  rw eq,
  apply mono_comp,
end

lemma sk_ι_is_iso_of_le (d : ℕ) (Δ : simplex_categoryᵒᵖ) (h : Δ.unop.len ≤ d) :
  is_iso (s.sk_ι_app d Δ) :=
⟨begin
  refine ⟨s.desc Δ (λ A, s.ι_summand_sk d ⟨A, _⟩), _⟩,
  { have he : epi A.e := infer_instance,
    exact (simplex_category.len_le_of_epi he).trans h, },
  { split,
    { apply s.sk_obj_hom_ext,
      rintro ⟨A, hA⟩,
      simp only [ι_summand_sk_ι_assoc, ι_desc, category.comp_id], },
    { apply s.hom_ext',
      intro A,
      simp only [ι_desc_assoc, ι_summand_sk_ι, category.comp_id], }, }
end⟩

@[simp]
def sk_ι_inv_of_le (d : ℕ) (Δ : simplex_categoryᵒᵖ) (h : Δ.unop.len ≤ d) :
  X.obj Δ ⟶ (s.sk_obj d Δ) :=
begin
  haveI := s.sk_ι_is_iso_of_le d Δ h,
  exact inv (s.sk_ι_app d Δ),
end

@[reassoc]
lemma ι_summand_sk_ι_inv_of_le (d : ℕ) {Δ : simplex_categoryᵒᵖ} (B : index_set.truncated d Δ)
  (h : Δ.unop.len ≤ d) :
  s.ι_summand_sk d B = s.ι_summand B.1 ≫ s.sk_ι_inv_of_le d Δ h :=
by rw [← s.ι_summand_sk_ι d B, sk_ι_inv_of_le, is_iso.eq_comp_inv]


@[simp, reassoc]
lemma ι_sk_ι_inv_of_le (d : ℕ) (Δ : simplex_categoryᵒᵖ) (h : Δ.unop.len ≤ d) :
  s.ι Δ.unop.len ≫ s.sk_ι_inv_of_le d Δ h = s.ι_summand_sk d ⟨index_set.id Δ, h⟩ :=
by simpa only [s.ι_summand_sk_ι_inv_of_le d ⟨index_set.id Δ, h⟩ h, ← s.ι_summand_id]

@[simp]
def sk_map_epi (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) [epi θ.unop] :
  s.sk_obj d Δ₁ ⟶ s.sk_obj d Δ₂ := s.sk_desc d Δ₁ (λ B,
  s.ι_summand_sk d ⟨⟨B.1.1, ⟨θ.unop ≫ B.1.e, epi_comp θ.unop B.1.e⟩⟩, B.2⟩)

@[simp, reassoc]
lemma sk_ι_app_epi_naturality (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) [epi θ.unop] :
  s.sk_map_epi d θ ≫ s.sk_ι_app d Δ₂ = s.sk_ι_app d Δ₁ ≫ X.map θ :=
begin
  apply s.sk_obj_hom_ext,
  intro B,
  simpa only [sk_map_epi, ι_summand_sk_desc_assoc, ι_summand_sk_ι, ι_summand_sk_ι_assoc,
    s.ι_summand_epi_naturality B.1 θ],
end

@[simp, reassoc]
lemma sk_ι_app_inv_epi_naturality (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) [epi θ.unop]
  (h : Δ₂.unop.len ≤ d) :
  s.sk_ι_inv_of_le d Δ₁ ((simplex_category.len_le_of_epi
    (infer_instance : epi θ.unop)).trans h) ≫
    s.sk_map_epi d θ = X.map θ ≫ s.sk_ι_inv_of_le d Δ₂ h :=
begin
  haveI := s.sk_ι_is_iso_of_le d Δ₂ h,
  simp only [← cancel_mono (s.sk_ι_app d Δ₂), category.assoc, s.sk_ι_app_epi_naturality d θ,
    sk_ι_inv_of_le, is_iso.inv_hom_id_assoc, is_iso.inv_hom_id, category.comp_id],
end

def sk_map (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) :
  s.sk_obj d Δ₁ ⟶ s.sk_obj d Δ₂ :=
s.sk_desc d Δ₁ (λ B, begin
  refine s.ι B.1.1.unop.len ≫ X.map (image.ι (θ.unop ≫ B.1.e)).op ≫
    s.sk_ι_inv_of_le d (op (image (θ.unop ≫ B.1.e))) _ ≫
    s.sk_map_epi d (factor_thru_image (θ.unop ≫ B.1.e)).op,
  have h : mono (image.ι (θ.unop ≫ B.val.e)) := infer_instance,
  exact (simplex_category.len_le_of_mono h).trans B.2,
end)

@[reassoc]
def sk_map_on_summand (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂)
  (B : index_set.truncated d Δ₁) {Δ₃ : simplex_category} {e : Δ₂.unop ⟶ Δ₃}
    {i : Δ₃ ⟶ B.1.1.unop} [epi e] [hi : mono i] (fac : e ≫ i = θ.unop ≫ B.1.e) :
  s.ι_summand_sk d B ≫ s.sk_map d θ =
    s.ι B.1.1.unop.len ≫ X.map i.op ≫ s.sk_ι_inv_of_le d (op Δ₃)
      ((simplex_category.len_le_of_mono hi).trans B.2) ≫ s.sk_map_epi d e.op :=
begin
  dsimp only [sk_map],
  have h := simplex_category.image_eq fac,
  unfreezingI { subst h, },
  simp only [ι_summand_sk_desc, simplex_category.image_ι_eq fac,
    simplex_category.factor_thru_image_eq fac],
end

@[simp, reassoc]
lemma sk_ι_app_naturality (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) :
  s.sk_map d θ ≫ s.sk_ι_app d Δ₂ = s.sk_ι_app d Δ₁ ≫ X.map θ :=
begin
  apply s.sk_obj_hom_ext,
  intro B,
  dsimp only [sk_map],
  simp only [sk_ι_inv_of_le, ι_summand_sk_desc_assoc, category.assoc, ι_summand_sk_ι_assoc,
    sk_ι_app_epi_naturality, is_iso.inv_hom_id_assoc],
  rw [← X.map_comp, ← op_comp, image.fac, op_comp, X.map_comp, quiver.hom.op_unop,
    ← category.assoc, ι_summand_eq],
end

@[simp, reassoc]
lemma sk_ι_inv_of_le_naturality (d : ℕ) {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂)
  (h₁ : Δ₁.unop.len ≤ d) (h₂ : Δ₂.unop.len ≤ d) :
  s.sk_ι_inv_of_le d Δ₁ h₁ ≫ s.sk_map d θ = X.map θ ≫ s.sk_ι_inv_of_le d Δ₂ h₂ :=
begin
  haveI := s.sk_ι_is_iso_of_le d Δ₂ h₂,
  simp only [← cancel_mono (s.sk_ι_app d Δ₂), sk_ι_inv_of_le, category.assoc,
    sk_ι_app_naturality, is_iso.inv_hom_id_assoc, is_iso.inv_hom_id, category.comp_id],
end

@[simps]
def sk (d : ℕ) [mono_coprod C] : simplicial_object C :=
{ obj := s.sk_obj d,
  map := λ Δ₁ Δ₂ θ, s.sk_map d θ,
  map_id' := λ Δ, by simp only [← cancel_mono (s.sk_ι_app d Δ), sk_ι_app_naturality,
    category_theory.functor.map_id, category.comp_id, category.id_comp],
  map_comp' := λ Δ₁ Δ₂ Δ₃ θ θ', by simp only [← cancel_mono (s.sk_ι_app d Δ₃),
    sk_ι_app_naturality, functor.map_comp, category.assoc, sk_ι_app_naturality_assoc], }

@[simps]
def sk_ι (d : ℕ) [mono_coprod C] : s.sk d ⟶ X :=
{ app := s.sk_ι_app d, }

instance (d : ℕ) (Δ : simplex_categoryᵒᵖ) [mono_coprod C] : mono ((s.sk_ι d).app Δ) :=
by { dsimp only [sk_ι], apply_instance, }

instance (d : ℕ) [mono_coprod C] : mono (s.sk_ι d) := nat_trans.mono_of_mono_app _

@[simp]
def sk_φ {d : ℕ} [mono_coprod C] {Y : simplicial_object C} (f : s.sk d ⟶ Y) {n : ℕ} (hn : n ≤ d) :
  s.N n ⟶ Y _[n] := s.ι_summand_sk d ⟨index_set.id (op [n]), hn⟩ ≫ f.app (op [n])

lemma ι_summand_sk_eq (d : ℕ) {Δ : simplex_categoryᵒᵖ} (B : index_set.truncated d Δ) [mono_coprod C]:
  s.ι_summand_sk d ⟨index_set.id B.1.1, B.2⟩ ≫ (s.sk d).map B.1.e.op = s.ι_summand_sk d B :=
begin
  simp only [sk_map_2, s.sk_map_on_summand d B.1.e.op ⟨index_set.id B.1.1, B.2⟩
    (show B.1.e ≫ 𝟙 _ = _, by refl)],
  dsimp only [sk_map_epi],
  erw [X.map_id, category.id_comp, ι_sk_ι_inv_of_le_assoc, s.ι_summand_sk_desc],
  congr,
  ext1,
  refine index_set.ext _ _ rfl _,
  change B.1.e ≫ 𝟙 _ ≫ 𝟙 _ = B.1.e,
  simp only [category.comp_id],
end

lemma sk_hom_ext (d : ℕ) [mono_coprod C] {Y : simplicial_object C}
  {f₁ f₂ : s.sk d ⟶ Y}
  (h : ∀ (n : ℕ) (hn : n ≤ d), s.sk_φ f₁ hn = s.sk_φ f₂ hn) : f₁ = f₂ :=
begin
  ext Δ : 2,
  induction Δ using opposite.rec,
  induction Δ using simplex_category.rec with n,
  apply s.sk_obj_hom_ext,
  intro B,
  erw [← ι_summand_sk_eq, category.assoc, category.assoc, f₁.naturality, f₂.naturality,
    ← category.assoc, ← category.assoc],
  congr' 1,
  apply h _ B.2,
end

@[simps]
def sk_hom_extension (d : ℕ) [mono_coprod C] {Y : simplicial_object C}
  (f : ((simplicial_object.sk d).obj X ⟶ (simplicial_object.sk d).obj Y)) :
  s.sk d ⟶ Y :=
{ app := λ Δ, s.sk_desc d Δ (λ B, s.ι B.1.1.unop.len ≫ f.app (op ⟨B.1.1.unop, B.2⟩) ≫
    Y.map B.1.e.op),
  naturality' := λ Δ₁ Δ₂ θ, begin
    apply s.sk_obj_hom_ext,
    intro B,
    dsimp only [sk, sk_map],
    simp only [ι_summand_sk_desc_assoc, category.assoc, ← Y.map_comp],
    change _ = _ ≫ _ ≫ Y.map (θ.unop ≫ B.1.e).op,
    rw [← congr_arg quiver.hom.op (image.fac (θ.unop ≫ B.1.e)), op_comp, Y.map_comp],
    have h := (simplex_category.len_le_of_mono
      (infer_instance : mono (image.ι (θ.unop ≫ B.1.e)))).trans B.2,
    let α : (⟨image (θ.unop ≫ B.1.e), h⟩ : simplex_category.truncated d) ⟶ ⟨B.1.1.unop, B.2⟩ :=
      image.ι (θ.unop ≫ B.1.e),
    slice_rhs 2 3 { erw ← f.naturality α.op, },
    simp only [category.assoc],
    congr' 2,
    haveI := s.sk_ι_is_iso_of_le d (op (image (θ.unop ≫ B.val.e))) h,
    rw ← cancel_epi (s.sk_ι_app d (op (image (θ.unop ≫ B.val.e)))),
    simp only [sk_ι_inv_of_le, sk_map_epi, is_iso.hom_inv_id_assoc],
    apply s.sk_obj_hom_ext,
    intro B',
    simp only [ι_summand_sk_desc_assoc, ι_summand_sk_desc, ι_summand_sk_ι_assoc, ι_summand_eq,
      category.assoc],
    dsimp only [index_set.e],
    rw [op_comp, Y.map_comp],
    let Δ₃ : (simplex_category.truncated d)ᵒᵖ := op ⟨B'.1.1.unop, B'.2⟩,
    let β : Δ₃ ⟶ op ⟨_, h⟩ := quiver.hom.op B'.1.e,
    slice_rhs 2 3 { erw (f.naturality β), },
    simpa only [category.assoc],
  end}

instance (d : ℕ) [mono_coprod C] (Δ : (simplex_category.truncated d)ᵒᵖ) :
  is_iso (((simplicial_object.sk d).map (s.sk_ι d)).app Δ) :=
s.sk_ι_is_iso_of_le d (op Δ.unop.1) Δ.unop.2

instance (d : ℕ) [mono_coprod C] : is_iso ((simplicial_object.sk d).map (s.sk_ι d)) :=
nat_iso.is_iso_of_is_iso_app _

include s
def hom_equiv (d : ℕ) [mono_coprod C] (Y : simplicial_object C) : (s.sk d ⟶ Y) ≃
  ((simplicial_object.sk d).obj X ⟶ (simplicial_object.sk d).obj Y) :=
{ to_fun := λ f, inv ((simplicial_object.sk d).map (s.sk_ι d)) ≫
      (simplicial_object.sk d).map f,
  inv_fun := s.sk_hom_extension d,
  left_inv := λ f, begin
    apply s.sk_hom_ext,
    intros n hn,
    dsimp only [sk_φ, sk_hom_extension],
    rw [ι_summand_sk_desc],
    simp only [nat_trans.comp_app, nat_iso.is_iso_inv_app, category.assoc, ι_summand_sk_desc],
    erw [s.ι_sk_ι_inv_of_le_assoc d (op [n]) hn, Y.map_id, category.comp_id],
    refl,
  end,
  right_inv := λ g, begin
    ext Δ : 2,
    induction Δ using opposite.rec,
    apply s.hom_ext',
    intro A,
    dsimp [simplex_category.truncated.inclusion] at A,
    simp only [nat_trans.comp_app, nat_iso.is_iso_inv_app],
    change _ ≫ _ ≫ (s.sk_hom_extension d g).app (op Δ.1) = _,
    dsimp only [sk_hom_extension],
    have hA := (simplex_category.len_le_of_epi A.2.2).trans Δ.2,
    erw [← s.ι_summand_sk_ι_inv_of_le_assoc d ⟨A, hA⟩ Δ.2, ι_summand_sk_desc,
      s.ι_summand_eq, category.assoc],
    congr' 1,
    let ψ : Δ ⟶ ⟨A.1.unop, hA⟩ := A.e,
    exact (g.naturality ψ.op).symm,
  end, }

@[simp]
def sk_inclusion_app {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) [mono_coprod C] (Δ : simplex_categoryᵒᵖ) :
  (s.sk d₁).obj Δ ⟶ (s.sk d₂).obj Δ :=
s.sk_desc d₁ Δ (λ B, s.ι_summand_sk d₂ ⟨B.1, B.2.trans h⟩)

@[reassoc]
lemma sk_inclusion_app_comp_sk_ι_app {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) [mono_coprod C]
  (Δ : simplex_categoryᵒᵖ) : s.sk_inclusion_app h Δ ≫ s.sk_ι_app d₂ Δ = s.sk_ι_app d₁ Δ :=
begin
  apply s.sk_obj_hom_ext,
  intro B,
  simp only [sk_inclusion_app, ι_summand_sk_desc_assoc, ι_summand_sk_ι],
end

@[simps]
def sk_inclusion {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) [mono_coprod C] :
  s.sk d₁ ⟶ s.sk d₂ :=
{ app := λ Δ, s.sk_inclusion_app h Δ,
  naturality' := λ Δ₁ Δ₂ θ, by begin
    simp only [← cancel_mono (s.sk_ι_app d₂ Δ₂), category.assoc, sk_map_2,
      sk_ι_app_naturality, s.sk_inclusion_app_comp_sk_ι_app h,
      s.sk_inclusion_app_comp_sk_ι_app_assoc h],
    end }

@[simp, reassoc]
lemma sk_inclusion_comp_sk_ι {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) [mono_coprod C] :
  s.sk_inclusion h ≫ s.sk_ι d₂ = s.sk_ι d₁ :=
begin
  apply s.sk_hom_ext,
  intros n hn,
  dsimp only [sk_φ],
  simp only [nat_trans.comp_app, sk_inclusion_app, sk_inclusion_app_2, sk_ι_app_2,
    ι_summand_sk_desc_assoc, ι_summand_sk_ι],
end

@[simp, reassoc]
lemma sk_inclusion_comp_sk_inclusion {d₁ d₂ d₃ : ℕ} (h₁₂ : d₁ ≤ d₂) (h₂₃ : d₂ ≤ d₃) [mono_coprod C] :
  s.sk_inclusion h₁₂ ≫ s.sk_inclusion h₂₃ = s.sk_inclusion (h₁₂.trans h₂₃) :=
by simp only [← cancel_mono (s.sk_ι d₃), category.assoc, sk_inclusion_comp_sk_ι]

end splitting

end simplicial_object
