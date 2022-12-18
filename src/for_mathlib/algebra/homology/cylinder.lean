import for_mathlib.algebra.homology.mapping_cone
import for_mathlib.algebra.homology.homological_complex_biprod
import category_theory.morphism_property

noncomputable theory

open category_theory category_theory.limits category_theory.category

variables {C : Type*} [category C] [preadditive C] [has_binary_biproducts C]

namespace cochain_complex

open hom_complex

variables {K L : cochain_complex C ℤ}

variable (K)

def cylinder : cochain_complex C ℤ :=
mapping_cone (homological_complex.biprod.lift (𝟙 K) (-𝟙 K))

namespace cylinder

variable {K}

def inl : K ⟶ cylinder K :=
homological_complex.biprod.inl ≫ ι_mapping_cone _

def inr : K ⟶ cylinder K :=
homological_complex.biprod.inr ≫ ι_mapping_cone _

variable (K)

def homotopy_inl_inr : homotopy (inl : K ⟶ _) inr :=
begin
  refine mapping_cone.lift_homotopy _ _ _ (cochain.of_hom (𝟙 K)) 0 _ _,
  { ext p q hpq,
    simp only [cocycle.δ_cochain_of_hom, neg_zero, zero_add,
      cochain.zero_cochain_comp, cochain.of_hom_v, inl, inr,
      homological_complex.comp_f, homological_complex.biprod.inl_f, assoc,
      homological_complex.biprod.inr_f, ι_mapping_cone,
      mapping_cone_inr_fst, comp_zero], },
  { ext1 p,
    simp only [cochain.comp_zero_cochain, cochain.of_hom_v, δ_zero, cochain.id_comp,
      zero_add, cochain.add_v, homological_complex.biprod.lift_f, homological_complex.id_f,
      homological_complex.neg_f_apply, inl, inr, ι_mapping_cone, homological_complex.comp_f,
      homological_complex.biprod.inl_f, assoc, mapping_cone_inr_snd, comp_id, homological_complex.biprod.inr_f],
    ext,
    { simp only [add_zero, biprod.inl_fst, preadditive.add_comp,
        biprod.lift_fst, biprod.inr_fst], },
    { simp only [biprod.inl_snd, preadditive.add_comp, biprod.lift_snd,
        biprod.inr_snd, add_left_neg], }, },
end

variable {K}

def desc (f₁ f₂ : K ⟶ L) (h : homotopy f₁ f₂) : cylinder K ⟶ L :=
mapping_cone.desc _ (cochain.of_homotopy h) (homological_complex.biprod.desc f₁ f₂) begin
  simp only [δ_cochain_of_homotopy, homological_complex.biprod.lift_desc, id_comp,
    preadditive.neg_comp],
  ext,
  simp only [cochain.sub_v, cochain.of_hom_v, homological_complex.add_f_apply,
    homological_complex.neg_f_apply],
  abel,
end

@[simp, reassoc]
lemma inl_desc (f₁ f₂ : K ⟶ L) (h : homotopy f₁ f₂) :
  inl ≫ desc f₁ f₂ h = f₁ :=
by simp only [desc, inl, assoc, mapping_cone.ι_desc, homological_complex.biprod.inl_desc]

@[simp, reassoc]
lemma inr_desc (f₁ f₂ : K ⟶ L) (h : homotopy f₁ f₂) :
  inr ≫ desc f₁ f₂ h = f₂ :=
by simp only [desc, inr, assoc, mapping_cone.ι_desc, homological_complex.biprod.inr_desc]

@[simp]
def π : cylinder K ⟶ K :=
desc _ _ (homotopy.refl (𝟙 K))

variable (K)

@[protected]
def homotopy_equiv : homotopy_equiv (cylinder K) K :=
{ hom := π,
  inv := inl,
  homotopy_hom_inv_id := begin
    refine mapping_cone.desc_homotopy _ _ _ 0
      ((cochain.of_hom homological_complex.biprod.snd).comp
        (mapping_cone_inl _) (zero_add _).symm) _ _,
    { ext1,
      dsimp [desc],
      simp only [zero_add, cochain.of_hom_comp, cochain.comp_zero_cochain, cochain.of_hom_v,
        mapping_cone.inl_desc_v_assoc, cochain.mk_v, zero_comp, δ_zero, cochain.zero_v,
        cochain.zero_cochain_comp, homological_complex.biprod.lift_f, homological_complex.id_f,
        homological_complex.neg_f_apply, homological_complex.biprod.snd_f, biprod.lift_snd_assoc,
        preadditive.neg_comp, id_comp],
      erw [homological_complex.id_f, comp_id, add_left_neg], },
    { erw [comp_id, mapping_cone_cochain_ext' _ _ (zero_add 1).symm],
      dsimp [desc, inl, ι_mapping_cone],
      split,
      { simp only [cochain.of_hom_comp, cochain.comp_assoc_of_second_is_zero_cochain,
          add_zero, mapping_cone_inr_comp_fst, cochain.comp_zero, add_left_neg,
          δ_comp_of_first_is_zero_cochain, mapping_cone_δ_inl, cocycle.δ_cochain_of_hom,
          cochain.zero_comp, smul_zero, cochain.add_comp], },
      { ext1,
        simp only [add_zero, cochain.of_hom_comp, cochain.comp_assoc_of_third_is_zero_cochain,
          mapping_cone_inr_comp_snd, cochain.comp_id, cochain.comp_zero_cochain,
          cochain.of_hom_v, homological_complex.biprod.inl_f, mapping_cone.inr_desc_f_assoc,
          homological_complex.biprod.desc_f, homological_complex.id_f, add_left_neg,
          δ_comp_of_first_is_zero_cochain, mapping_cone_δ_inl, cocycle.δ_cochain_of_hom,
          cochain.zero_comp, smul_zero, cochain.add_comp, cochain.add_v,
          homological_complex.biprod.snd_f, homological_complex.biprod.lift_f,
          homological_complex.neg_f_apply],
        ext1,
        { dsimp,
          simp only [biprod.inl_desc_assoc, id_comp, preadditive.comp_add,
            biprod.inl_snd_assoc, zero_comp, comp_id, zero_add], },
        { dsimp,
          ext1,
          { simp only [biprod.inr_desc_assoc, id_comp, biprod.inl_fst, preadditive.comp_add,
              biprod.inr_snd_assoc, comp_id, preadditive.add_comp, biprod.lift_fst,
              biprod.inr_fst, add_zero], },
          { simp only [biprod.inr_desc_assoc, id_comp, biprod.inl_snd, preadditive.comp_add,
              biprod.inr_snd_assoc, comp_id, preadditive.add_comp, biprod.lift_snd,
              biprod.inr_snd, add_left_neg], }, }, }, },
  end,
  homotopy_inv_hom_id := homotopy.of_eq (by rw [π, inl_desc]), }

end cylinder

variable (C)

def homotopy_equivalences : morphism_property (cochain_complex C ℤ) :=
λ K L φ, ∃ (h : homotopy_equiv K L), φ = h.hom

variable {C}

lemma homotopy_equivalences_is_inverted_by_iff {D : Type*} [category D]
  (F : cochain_complex C ℤ ⥤ D) :
  (homotopy_equivalences C).is_inverted_by F ↔
    ∀ (K L : cochain_complex C ℤ) (f₁ f₂ : K ⟶ L)
      (h : homotopy f₁ f₂), F.map f₁ = F.map f₂ :=
begin
  split,
  { intros hF K L f₁ f₂ h,
    haveI : is_iso (F.map cylinder.π) := hF _ ⟨cylinder.homotopy_equiv K, rfl⟩,
    have eq : F.map (cylinder.inl : K ⟶ _) = F.map cylinder.inr,
    { simp only [← cancel_mono (F.map (cylinder.π : _ ⟶ K)),
        ← F.map_comp, cylinder.π, cylinder.inl_desc, cylinder.inr_desc], },
    simpa only [← F.map_comp, cylinder.inl_desc, cylinder.inr_desc]
      using eq =≫ F.map (cylinder.desc _ _ h), },
  { rintros hF K L _ ⟨e, rfl⟩,
    exact ⟨⟨F.map e.inv,
      by simpa only [← F.map_comp, ← F.map_id]  using hF _ _ _ _ e.homotopy_hom_inv_id,
      by simpa only [← F.map_comp, ← F.map_id]  using hF _ _ _ _ e.homotopy_inv_hom_id⟩⟩, },
end

end cochain_complex
