import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.algebra.homology.pretriangulated

open category_theory category_theory.pretriangulated category_theory.triangulated
  category_theory.limits category_theory.category

noncomputable theory

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]
  [has_binary_biproducts C]

namespace cochain_complex

open hom_complex

variables {X₁ X₂ X₃ : cochain_complex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

@[simps mor₁ mor₂ mor₃]
def mapping_cone_comp_triangle : triangle (cochain_complex C ℤ) :=
triangle.mk (mapping_cone_map f (f ≫ g) (𝟙 X₁) g (by rw id_comp))
  (mapping_cone_map (f ≫ g) g f (𝟙 X₃) (by rw comp_id))
    (mapping_cone_δ g ≫ (ι_mapping_cone f)⟦1⟧')

@[simp]
def mapping_cone_comp_homotopy_equiv.hom :
  mapping_cone g ⟶ mapping_cone (mapping_cone_comp_triangle f g).mor₁ :=
mapping_cone.lift _
  (mapping_cone.desc_cocycle g (cochain.of_hom (ι_mapping_cone f)) 0 (zero_add 1)
    (by simp only [cocycle.δ_cochain_of_hom, subtype.val_eq_coe, add_subgroup.coe_zero,
  cochain.comp_zero, smul_zero]))
    (mapping_cone.desc_cochain _ 0 (cochain.of_hom (ι_mapping_cone (f ≫ g))) (neg_add_self 1))
  begin
    simp only [mapping_cone.δ_desc_cochain _ _ _ _ (zero_add 1),
      zero_add, cocycle.δ_cochain_of_hom, cochain.comp_zero, δ_zero, ε_1, neg_smul,
      one_zsmul, cochain.comp_neg, add_zero, mapping_cone_comp_triangle_mor₁, neg_add_eq_zero],
    rw mapping_cone_cochain_ext _ _ (zero_add 1).symm,
    split,
    { simp only [← hom_complex.cochain.comp_assoc_of_third_is_zero_cochain,
        mapping_cone_inl_comp_fst, cochain.id_comp, mapping_cone.desc_cocycle_coe,
        mapping_cone.inl_desc_cochain],
      simp only [← cochain.of_hom_comp, ι_comp_mapping_cone_map], },
    { simp only [← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
        add_subgroup.coe_zero, mapping_cone_inr_comp_fst, cochain.zero_comp, mapping_cone.desc_cocycle_coe,
        mapping_cone.inr_desc_cochain], },
  end

@[simp]
def mapping_cone_comp_homotopy_equiv.inv :
  mapping_cone (mapping_cone_comp_triangle f g).mor₁ ⟶ mapping_cone g :=
mapping_cone.desc _ ((mapping_cone_snd f).comp (mapping_cone_inl g) (zero_add _).symm)
  (mapping_cone.desc _ ((cochain.of_hom f).comp (mapping_cone_inl g)
    (zero_add _).symm) (ι_mapping_cone g)
    (by simpa only [add_zero, add_left_neg, δ_comp_of_first_is_zero_cochain,
      mapping_cone_δ_inl, cochain.of_hom_comp,
      cocycle.δ_cochain_of_hom, cochain.zero_comp, smul_zero, assoc]))
begin
  dsimp,
  simp only [add_left_neg, δ_comp_of_first_is_zero_cochain, mapping_cone_δ_inl,
    cochain.of_hom_comp, eq_self_iff_true, mapping_cone_δ_snd, cochain.neg_comp, one_smul,
    cochain.comp_assoc_of_second_is_zero_cochain, zsmul_neg', neg_smul, ε_neg, ε_1, neg_neg,
    mapping_cone_cochain_ext _ _ (neg_add_self 1).symm, mapping_cone_map,
    cochain.comp_add],
  split,
  { simpa only [← hom_complex.cochain.comp_assoc_of_second_is_zero_cochain,
      ← hom_complex.cochain.comp_assoc_of_third_is_zero_cochain,
      ← hom_complex.cochain.comp_assoc _ _ _ (neg_add_self 1).symm (add_neg_self 1).symm
      (show (-1 : ℤ) = _, by linarith), mapping_cone_inl_comp_fst,
      mapping_cone_inl_comp_snd, cochain.zero_comp, zero_add, cochain.id_comp,
      mapping_cone.inl_desc], },
  { simpa only [← hom_complex.cochain.comp_assoc_of_second_is_zero_cochain,
      ← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      mapping_cone_inr_comp_fst, mapping_cone_inr_comp_snd, cochain.zero_comp, add_zero,
      cochain.id_comp, ← cochain.of_hom_comp, mapping_cone.inr_desc_assoc, assoc,
      mapping_cone.ι_desc, id_comp], },
end

@[simps hom inv]
def mapping_cone_comp_homotopy_equiv :
  homotopy_equiv (mapping_cone g) (mapping_cone (mapping_cone_comp_triangle f g).mor₁) :=
{ hom := mapping_cone_comp_homotopy_equiv.hom f g,
  inv := mapping_cone_comp_homotopy_equiv.inv f g,
  homotopy_hom_inv_id := homotopy.of_eq begin
    simp only [mapping_cone_comp_homotopy_equiv.hom, mapping_cone_comp_homotopy_equiv.inv],
    ext n : 2,
    simp only [homological_complex.comp_f, homological_complex.id_f,
      mapping_cone.lift_desc_f _ _ _ _ _ _ _ _ _ rfl,
      mapping_cone.desc_cocycle_coe, add_subgroup.coe_zero, cochain.zero_cochain_comp,
      from_mapping_cone_ext_iff _ _ _ rfl, preadditive.comp_add,
      mapping_cone.inl_desc_cochain_v_assoc, mapping_cone.inr_desc_cochain_v_assoc,
      cochain.zero_v, zero_comp, zero_add, ι_mapping_cone, cochain.of_hom_v,
      mapping_cone_inr_snd_assoc, add_zero, comp_id, mapping_cone.inr_desc_f,
      eq_self_iff_true, and_self],
  end,
  homotopy_inv_hom_id := (equiv_homotopy _ _).symm begin
    refine ⟨-(mapping_cone_snd _).comp
      (((mapping_cone_fst (f ≫ g)).1.comp (mapping_cone_inl f) (add_neg_self 1).symm).comp
        (mapping_cone_inl _) (zero_add _).symm) (zero_add (-1)).symm, _⟩,
    ext1 n,
    dsimp,
    simp only [from_mapping_cone_ext_iff _ _ (n+1) rfl,
      to_mapping_cone_ext_iff _ _ (n+1) rfl,
      from_mapping_cone_ext_iff _ _ (n+2) (show n+2=n+1+1, by linarith),
      from_mapping_cone_ext_iff _ _ (n+1) rfl,
      preadditive.comp_add, preadditive.add_comp,
      neg_neg, δ_neg, preadditive.comp_neg, preadditive.neg_comp,
      δ_comp_of_first_is_zero_cochain _ _ _ (neg_add_self 1), mapping_cone_δ_inl,
      mapping_cone_δ_snd, cochain.of_hom_v, homological_complex.comp_f, assoc,
      mapping_cone.inl_desc_v_assoc, cochain.zero_cochain_comp,
      homological_complex.id_f, cochain.add_v, cochain.zsmul_v, ε_neg, ε_1, neg_smul,
      one_smul, cochain.neg_comp, cochain.neg_v, mapping_cone_inl_snd_assoc,
      zero_comp, zero_add, comp_id, cochain.comp_assoc_of_second_is_zero_cochain,
      cochain.comp_v _ _ (add_neg_self 1).symm n (n+1) n rfl (by linarith),
      mapping_cone_inl_fst_assoc, mapping_cone_inr_snd_assoc,
      mapping_cone_inr_fst_assoc, add_zero, mapping_cone.inr_desc_f_assoc,
      δ_comp _ _ (add_neg_self 1).symm 2 0 1 (zero_add 1) (by linarith) (neg_add_self 1),
      cocycle.δ_eq_zero, cochain.zero_comp, cochain.zero_v, neg_zero,
      mapping_cone_map, mapping_cone_inl_fst, mapping_cone.lift_fst_f,
      mapping_cone.desc_cocycle_coe, mapping_cone.inl_desc_cochain_v,
      cochain.comp_v _ _ (add_neg_self 1).symm (n+1) (n+2) (n+1) (by linarith) (by linarith),
      mapping_cone.lift_snd_f, comp_zero, mapping_cone_inl_snd, id_comp,
      ι_mapping_cone, mapping_cone_inr_fst, mapping_cone.inr_desc_cochain_v,
      neg_add_self, mapping_cone.inl_desc_cochain_v_assoc,
      mapping_cone.inr_desc_cochain_v_assoc, eq_self_iff_true,
      add_subgroup.coe_zero, cochain.zero_v],
    dsimp,
    erw comp_id,
    simp only [eq_self_iff_true, and_self],
  end, }

lemma mapping_cone_comp_homotopy_equiv_comm₁ :
  ι_mapping_cone (mapping_cone_comp_triangle f g).mor₁ ≫
    (mapping_cone_comp_homotopy_equiv f g).inv = (mapping_cone_comp_triangle f g).mor₂ :=
begin
  ext n : 2,
  dsimp [ι_mapping_cone],
  simp only [mapping_cone.inr_desc_f, mapping_cone_map, from_mapping_cone_ext_iff _ _ _ rfl,
    mapping_cone.inl_desc_v, id_comp, ι_mapping_cone],
  tauto,
end

lemma mapping_cone_comp_homotopy_equiv_comm₂ :
  (mapping_cone_comp_homotopy_equiv f g).hom ≫
    mapping_cone_δ (mapping_cone_comp_triangle f g).mor₁ =
      (mapping_cone_comp_triangle f g).mor₃ :=
begin
  ext n : 2,
  simp only [mapping_cone_comp_homotopy_equiv_hom,
    mapping_cone_comp_homotopy_equiv.hom, mapping_cone_comp_triangle_mor₃,
    homological_complex.comp_f, shift_functor_map_f', mapping_cone_δ,
    ι_mapping_cone, mapping_cone.lift_f _ _ _ _ _ _ rfl, assoc,
    cocycle.hom_of_f, cocycle.right_shift_coe, mapping_cone_δ_as_cocycle_coe,
    preadditive.add_comp, preadditive.neg_comp, preadditive.comp_neg, cochain.neg_v,
    cochain.right_shift_v  _ _ _ (zero_add 1).symm _ _ (add_zero n).symm _ rfl,
    mapping_cone_inl_fst_assoc, mapping_cone_inr_fst_assoc, zero_comp, comp_zero, add_zero,
    neg_inj, mapping_cone.desc_cocycle_coe, add_subgroup.coe_zero, shift_functor_obj_X_iso,
    homological_complex.X_iso_of_eq_refl],
  dsimp [iso.refl],
  rw [comp_id, id_comp, from_mapping_cone_ext_iff _ _ (n+1) rfl],
  split,
  { simp only [mapping_cone_inl_fst_assoc, mapping_cone.inl_desc_cochain_v,
      cochain.of_hom_v], },
  { simp only [mapping_cone_inr_fst_assoc, mapping_cone.inr_desc_cochain_v, zero_comp,
      cochain.zero_v], },
end

end cochain_complex

namespace homotopy_category

instance {C ι : Type*} [category C] [preadditive C] (c : complex_shape ι) :
  full (homotopy_category.quotient C c) :=
by { dsimp [quotient], apply_instance, }

lemma mapping_cone_comp_triangle_distinguished {X₁ X₂ X₃ : cochain_complex C ℤ}
  (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
  quotient_triangulated_functor_struct.map_triangle.obj
    (cochain_complex.mapping_cone_comp_triangle f g) ∈ dist_triang (homotopy_category C (complex_shape.up ℤ)) :=
begin
  refine ⟨_,_, (cochain_complex.mapping_cone_comp_triangle f g).mor₁,
    ⟨triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
    (iso_of_homotopy_equiv (cochain_complex.mapping_cone_comp_homotopy_equiv f g))
    (by { dsimp, rw [id_comp, comp_id], refl, }) _ _⟩⟩,
  { simp only [iso.refl_hom, id_comp, ← cancel_mono (iso_of_homotopy_equiv
      (cochain_complex.mapping_cone_comp_homotopy_equiv f g)).inv, assoc, iso.hom_inv_id, comp_id],
    dsimp [mapping_cone_triangle'],
    erw [← functor.map_comp, cochain_complex.mapping_cone_comp_homotopy_equiv_comm₁],
    refl, },
  { dsimp [mapping_cone_triangle', cochain_complex.mapping_cone_δ'],
    erw [(shift_functor (homotopy_category C (complex_shape.up ℤ)) (1 : ℤ)).map_id,
      comp_id, comp_id, ← functor.map_comp, cochain_complex.mapping_cone_comp_homotopy_equiv_comm₂],
    refl, },
end

instance : is_triangulated (homotopy_category C (complex_shape.up ℤ)) :=
is_triangulated.mk' (begin
  rintro ⟨X₁ : cochain_complex C ℤ⟩ ⟨X₂ : cochain_complex C ℤ⟩ ⟨X₃ : cochain_complex C ℤ⟩
    u₁₂' u₂₃',
  obtain ⟨u₁₂, rfl⟩ := (homotopy_category.quotient _ _).map_surjective u₁₂',
  obtain ⟨u₂₃, rfl⟩ := (homotopy_category.quotient _ _).map_surjective u₂₃',
  refine ⟨_, _, _, _, _, _, _, _,
    iso.refl _, iso.refl _, iso.refl _,
    by { dsimp, rw [comp_id, id_comp], }, by { dsimp, rw [comp_id, id_comp], },
     _, _, mapping_cone_triangle'_distinguished u₁₂,
     _, _, mapping_cone_triangle'_distinguished u₂₃,
     _, _, mapping_cone_triangle'_distinguished (u₁₂ ≫ u₂₃), ⟨_⟩⟩,
  let α := cochain_complex.mapping_cone_triangle_map u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw id_comp),
  let β := cochain_complex.mapping_cone_triangle_map (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw comp_id),
  refine octahedron.mk ((homotopy_category.quotient _ _).map α.hom₃)
    ((homotopy_category.quotient _ _).map β.hom₃)
    (quotient_triangulated_functor_struct.map_triangle.map α).comm₂
    begin
      have eq := (quotient_triangulated_functor_struct.map_triangle.map α).comm₃,
      dsimp at eq,
      erw [comp_id, comp_id, comp_id] at eq,
      exact eq.symm,
    end
    (trans (quotient_triangulated_functor_struct.map_triangle.map β).comm₂ (id_comp _))
    begin
      have eq := (quotient_triangulated_functor_struct.map_triangle.map β).comm₃,
      dsimp at eq,
      erw comp_id at eq,
      conv_rhs at eq { congr, skip, erw comp_id, },
      exact eq,
    end _,
  exact pretriangulated.isomorphic_distinguished _
    (mapping_cone_comp_triangle_distinguished u₁₂ u₂₃) _
    (triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)
    (by { dsimp, erw [comp_id, id_comp], })),
end)

end homotopy_category
