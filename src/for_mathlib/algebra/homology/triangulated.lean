import for_mathlib.algebra.homology.mapping_cone
import algebra.homology.additive
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.triangulated.shift_triangle

open category_theory category_theory.pretriangulated category_theory.triangulated
  category_theory.limits category_theory.category

noncomputable theory

section

variables {C ι : Type*} [category C] [preadditive C] {c : complex_shape ι}

def homotopy_category.lift {K L : homological_complex C c}
  (φ : (homotopy_category.quotient _ _).obj K ⟶ (homotopy_category.quotient _ _).obj L) :
  K ⟶ L := quot.out φ

instance [has_zero_object C] : has_zero_object (homotopy_category C c) :=
by { change has_zero_object (category_theory.quotient _), apply_instance, }

instance : preadditive (homotopy_category C c) :=
begin
  apply quotient.preadditive,
  { rintros X Y f₁ g₁ f₂ g₂ ⟨h₁⟩ ⟨h₂⟩,
    refine ⟨homotopy.add h₁ h₂⟩, },
  { rintros X Y f g ⟨h⟩,
    exact ⟨homotopy.equiv_sub_zero.symm
      (by simpa only [neg_sub_neg] using homotopy.equiv_sub_zero h.symm)⟩, },
end

instance homotopy_category.quotient_additive :
  (homotopy_category.quotient C c).additive := quotient.functor_additive _ _ _

lemma is_zero_of_homotopy_id_zero [has_zero_object C] (X : homological_complex C c)
  (h : homotopy (𝟙 X) 0) :
  is_zero ((homotopy_category.quotient C c).obj X) :=
begin
  have eq := homotopy_category.eq_of_homotopy _ _ h,
  simp only [category_theory.functor.map_id] at eq,
  simp only [is_zero.iff_id_eq_zero, eq, functor.map_zero],
end

end

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]
  [has_binary_biproducts C]
  {K L : cochain_complex C ℤ} (φ : K ⟶ L)

namespace cochain_complex


@[simps mor₁ mor₂ mor₃]
def mapping_cone_triangle : triangle (cochain_complex C ℤ) :=
triangle.mk φ (ι_mapping_cone φ) (mapping_cone_δ φ)

end cochain_complex

open cochain_complex

namespace homotopy_category

def mapping_cone_triangle' : triangle (homotopy_category C (complex_shape.up ℤ)) :=
triangle.mk ((homotopy_category.quotient _ _).map φ) (ι_mapping_cone' φ) (mapping_cone_δ' φ)

variable (C)

def distinguished_triangles : set (triangle (homotopy_category C (complex_shape.up ℤ))) :=
λ T, ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L),
  nonempty (T ≅ mapping_cone_triangle' φ)

variable {C}

lemma mapping_cone_triangle'_distinguished :
  mapping_cone_triangle' φ ∈ distinguished_triangles C :=
⟨_, _, φ, nonempty.intro (iso.refl _)⟩

instance shift_functor_additive (n : ℤ) :
  (category_theory.shift_functor (homotopy_category C (complex_shape.up ℤ)) n).additive := { }

lemma isomorphic_distinguished
  (T₁ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (h₁ : T₁ ∈ distinguished_triangles C)
  (T₂ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (e : T₂ ≅ T₁) : T₂ ∈ distinguished_triangles C :=
begin
  obtain ⟨K, L, φ, ⟨e'⟩⟩ := h₁,
  exact ⟨K, L, φ, ⟨e ≪≫ e'⟩⟩,
end

lemma contractible_distinguished
  (X : homotopy_category C (complex_shape.up ℤ)) :
  contractible_triangle X ∈ distinguished_triangles C :=
begin
  cases X,
  refine ⟨_, _, 𝟙 X, ⟨_⟩⟩,
  have h : is_zero ((homotopy_category.quotient _ _).obj (mapping_cone (𝟙 X))),
  { refine is_zero_of_homotopy_id_zero _ _,
    exact mapping_cone.desc_homotopy _ _ _ 0 (mapping_cone_inl (𝟙 X)) (by simp) (by simp), },
  exact triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (is_zero.iso_zero h).symm
    (by tidy) (is_zero.eq_of_tgt h _ _) (by simp only [is_zero.eq_of_src h
      ((mapping_cone_triangle' (𝟙 X)).mor₃) 0, contractible_triangle_mor₃, zero_comp, comp_zero]),
end

lemma distinguished_cocone_triangle
  (X Y : homotopy_category C (complex_shape.up ℤ)) (f : X ⟶ Y) :
  ∃ (Z : homotopy_category C (complex_shape.up ℤ)) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧), triangle.mk f g h ∈ distinguished_triangles C :=
begin
  cases X,
  cases Y,
  obtain ⟨φ, rfl⟩ := quotient.functor_map_surjective _ _ f,
  exact ⟨_ ,_ ,_ , mapping_cone_triangle'_distinguished φ⟩,
end

open cochain_complex.hom_complex

lemma complete_distinguished_triangle_morphism'
  {K₁ L₁ K₂ L₂ : cochain_complex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (hab : homotopy (φ₁ ≫ b) (a ≫ φ₂)) :
  ∃ (c : mapping_cone φ₁ ⟶ mapping_cone φ₂),
    nonempty (homotopy (ι_mapping_cone φ₁ ≫ c) (b ≫ ι_mapping_cone φ₂)) ∧
      nonempty (homotopy (mapping_cone_δ φ₁ ≫ a⟦1⟧') (c ≫ mapping_cone_δ φ₂)) :=
begin
  obtain ⟨z, hz⟩ := (equiv_homotopy _ _) hab, clear hab,
  refine ⟨_, _, _⟩,
  refine mapping_cone.desc _
    (z.comp (cochain.of_hom (mapping_cone_inr φ₂)) (add_zero _).symm +
      (cochain.of_hom a).comp (mapping_cone_inl φ₂) (zero_add _).symm)
    (b ≫ ι_mapping_cone φ₂) _,
  { simp only [δ_comp_of_second_is_zero_cochain _ _ _ (neg_add_self 1),
      cocycle.δ_cochain_of_hom, cochain.comp_zero, zero_add, ← assoc,
      cochain.of_hom_comp (φ₁ ≫ b), hz, cochain.add_comp, δ_add, ← cochain.of_hom_comp],
    simpa only [add_zero, add_left_neg, δ_comp_of_first_is_zero_cochain, mapping_cone_δ_inl,
      cochain.of_hom_comp, cocycle.δ_cochain_of_hom, cochain.zero_comp, smul_zero, assoc], },
  { exact nonempty.intro (homotopy.of_eq (by simp)), },
  { refine nonempty.intro (homotopy.of_eq ((cocycle.equiv_hom _ _).injective _)),
    ext1,
    simp only [mapping_cone_δ, cochain.of_hom_comp, cocycle.equiv_hom_apply, cocycle.of_hom_coe,
      cocycle.cochain_of_hom_hom_of_eq_coe, cocycle.right_shift_coe,
      mapping_cone_δ_as_cocycle_coe],
    ext1,
    simp only [cochain.comp_zero_cochain, cochain.of_hom_v,
      cochain.right_shift_v _ 1 0 (zero_add 1).symm p p (add_zero p).symm _ rfl,
      shift_functor_obj_X_iso, assoc, cochain.neg_v,
      homological_complex.X_iso_of_eq_refl, preadditive.neg_comp, preadditive.comp_neg, neg_inj],
    dsimp [iso.refl],
    simp only [comp_id, id_comp, from_mapping_cone_ext_iff _ _ _ rfl],
    split,
    { simp only [zero_add, assoc, mapping_cone.inl_desc_v_assoc, cochain.add_v,
        cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_cochain_comp,
        preadditive.add_comp, mapping_cone_inr_fst, comp_zero, mapping_cone_inl_fst, comp_id,
        mapping_cone_inl_fst_assoc], },
    { simp only [mapping_cone_inr_fst_assoc, mapping_cone_inr_fst, zero_comp, comp_zero,
        assoc, mapping_cone.inr_desc_f_assoc, homological_complex.comp_f, ι_mapping_cone], }, },
end

lemma complete_distinguished_triangle_morphism
  (T₁ T₂ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (h₁ : T₁ ∈ distinguished_triangles C) (h₂ : T₂ ∈ distinguished_triangles C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
  (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
    T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ :=
begin
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := h₁,
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := h₂,
  obtain ⟨c, ⟨h₁⟩, ⟨h₂⟩⟩ := complete_distinguished_triangle_morphism' φ₁ φ₂
    (quot.out (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)) (quot.out (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂))
    (homotopy_of_eq _ _ begin
      simp only [functor.map_comp, quotient_map_out, category.assoc],
      erw [reassoc_of e₁.inv.comm₁, reassoc_of comm₁, e₂.hom.comm₁],
      refl,
    end),
  replace h₁ := eq_of_homotopy _ _ h₁,
  replace h₂ := eq_of_homotopy _ _ h₂,
  refine ⟨e₁.hom.hom₃ ≫ (homotopy_category.quotient _ _).map c ≫ e₂.inv.hom₃, _, _⟩,
  { simp only [functor.map_comp, quotient_map_out, category.assoc] at h₁,
    erw [reassoc_of e₁.hom.comm₂, reassoc_of h₁, e₂.inv.comm₂],
    simp only [triangle.hom_inv_id_hom₂_assoc], },
  { erw [functor.map_comp, quotient_map_shift] at h₂,
    simp only [quotient_map_out, functor.map_comp] at h₂,
    simp only [category.assoc, ← e₂.inv.comm₃],
    erw [← reassoc_of h₂, ← reassoc_of e₁.hom.comm₃],
    simp only [← functor.map_comp, triangle.hom_inv_id_hom₁, category.comp_id,
      triangle.hom_inv_id_hom₁_assoc], },
end

lemma rotate_distinguished_triangle₁ (T : triangle (homotopy_category C (complex_shape.up ℤ)))
  (hT : T ∈ distinguished_triangles C) : T.rotate ∈ distinguished_triangles C :=
begin
  obtain ⟨K, L, φ, ⟨e⟩⟩:= hT,
  suffices : (mapping_cone_triangle' φ).rotate ∈ distinguished_triangles C,
  { exact isomorphic_distinguished _ this _ ((rotate _).map_iso e), },
  let α : homotopy_equiv (K⟦(1 : ℤ)⟧) (mapping_cone (ι_mapping_cone φ)) :=
  { hom := mapping_cone.lift _
      (-cocycle.left_shift (cocycle.of_hom φ) 1 1 (zero_add 1).symm)
      (-(mapping_cone_inl φ).left_shift 1 0 (neg_add_self 1).symm)
      begin
        simp only [δ_neg, mapping_cone_δ_inl, cochain.δ_left_shift
          (mapping_cone_inl φ) 1 _ 0 _ (neg_add_self 1).symm (zero_add 1).symm,
          ε_1, neg_smul, neg_neg, one_smul],
        ext1 p q hpq,
        simp only [ι_mapping_cone, cochain.add_v,
          cochain.left_shift_v _ 1 1 (zero_add 1).symm p _ hpq _ hpq,
          cochain.comp_zero_cochain, shift_functor_obj_X_iso, add_zero,
          mul_one, sub_self, mul_zero, euclidean_domain.zero_div, ε_1, neg_smul,
          homological_complex.X_iso_of_eq_refl, cochain.of_hom_comp, cochain.of_hom_v,
          one_zsmul, add_subgroup.coe_neg, cocycle.left_shift_coe, cocycle.of_hom_coe,
          cochain.neg_v, preadditive.neg_comp, cochain.zero_v, neg_neg, assoc,
          neg_add_self],
      end,
    inv := mapping_cone.desc _ 0 (mapping_cone_δ φ)
      (by simp only [δ_zero, mapping_cone_ι_δ, cochain.of_hom_zero]),
    homotopy_hom_inv_id := homotopy.of_eq begin
      ext n : 2,
      simp only [homological_complex.comp_f, homological_complex.id_f,
        mapping_cone.lift_desc_f _ _ _ _ _ _ _ _ _ rfl,
        mapping_cone_δ, mapping_cone_δ_as_cocycle, zero_add, add_subgroup.coe_neg,
        cochain.neg_v, cochain.zero_v, preadditive.neg_comp, comp_zero,
        cocycle.hom_of_f, cocycle.right_shift_coe,
        cochain.left_shift_v _ _ _ (neg_add_self 1).symm n n (by linarith) _ rfl,
        cochain.right_shift_v _ _ _ (zero_add 1).symm n n (by linarith) _ rfl,
        zero_add, mul_zero, sub_self, euclidean_domain.zero_div, ε_0, one_zsmul,
        preadditive.comp_neg, assoc, mapping_cone_inl_fst_assoc, iso.hom_inv_id, neg_neg],
    end,
    homotopy_inv_hom_id := begin
      sorry,
    end, },
  refine ⟨_,_, ι_mapping_cone φ, ⟨triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
    (iso_of_homotopy_equiv α) (by tidy) (eq_of_homotopy _ _ _)
    (eq_of_homotopy _ _ (homotopy.of_eq _))⟩⟩,
  { rw id_comp,
    symmetry,
    equiv_rw equiv_homotopy  _ _,
    refine ⟨(mapping_cone_snd φ).comp (mapping_cone_inl (ι_mapping_cone φ)) (zero_add _).symm,
      _⟩,
    simp only [δ_comp_of_first_is_zero_cochain _ _ _ (neg_add_self 1),
      mapping_cone_δ_inl, cochain.of_hom_comp, mapping_cone_δ_snd,
      subtype.val_eq_coe, mapping_cone_cochain_ext _ _ (neg_add_self 1).symm,
      cochain.comp_add],
    split,
    { simp only [← cochain.comp_assoc_of_first_is_zero_cochain,
        ← cochain.comp_assoc_of_second_is_zero_cochain,
        ← cochain.comp_assoc_of_third_is_zero_cochain, cochain.comp_zsmul,
        mapping_cone_inl_comp_snd, cochain.zero_comp, zero_add, cochain.neg_comp,
        cochain.comp_neg, smul_neg, ε_neg, ε_1, neg_smul, neg_neg, one_smul,
        ← cochain.comp_assoc _ _ _ (neg_add_self 1).symm (add_neg_self 1).symm
        (show (-1 : ℤ) =-1+1+(-1), by linarith), mapping_cone_inl_comp_fst,
        cochain.id_comp],
      rw mapping_cone_cochain_ext' _ _ (neg_add_self 1).symm,
      split,
      { simp only [cochain.add_comp, cochain.comp_assoc_of_first_is_zero_cochain,
          cochain.comp_assoc_of_second_is_zero_cochain, mapping_cone_inr_comp_fst,
          mapping_cone_inl_comp_fst, cochain.comp_id, ι_mapping_cone, cochain.comp_zero,
          mapping_cone.lift_fst, add_subgroup.coe_neg, cocycle.left_shift_coe,
          cocycle.of_hom_coe, cochain.comp_neg, mapping_cone_δ, mapping_cone_δ_as_cocycle,
          cocycle.cochain_of_hom_hom_of_eq_coe, cocycle.right_shift_coe, add_subgroup.coe_neg],
        ext n,
        simp only [cochain.zero_v, cochain.add_v, cochain.of_hom_v, cochain.neg_v,
          cochain.comp_v _ _ (neg_add_self 1).symm n (n-1) n (by linarith) (by linarith),
          cochain.comp_v _ _ (zero_add 1).symm (n-1) (n-1) n (by linarith) (by linarith),
          cochain.right_shift_v _ _ _ (zero_add 1).symm (n-1) (n-1) (by linarith) n (by linarith),
          cochain.left_shift_v _ _ _ (zero_add 1).symm (n-1) n (by linarith) n (by linarith),
          add_zero, neg_neg, shift_functor_obj_X_iso, preadditive.neg_comp, mul_one, sub_self,
          mul_zero, euclidean_domain.zero_div, ε_1, neg_smul, one_zsmul, preadditive.comp_neg,
          preadditive.neg_comp_assoc, assoc, homological_complex.X_iso_of_eq_inv_hom,
          homological_complex.X_iso_of_eq_refl, iso.refl_hom, comp_id,
          mapping_cone_inl_fst_assoc, add_right_neg], },
      { simp only [cochain.add_comp, cochain.comp_assoc_of_first_is_zero_cochain,
          cochain.comp_assoc_of_third_is_zero_cochain, mapping_cone.lift_snd,
          mapping_cone_inl_comp_snd, cochain.comp_zero, zero_add, ι_mapping_cone,
          mapping_cone_inr_comp_snd, cochain.comp_id, mapping_cone_δ,
          cocycle.cochain_of_hom_hom_of_eq_coe, cocycle.right_shift_coe,
          mapping_cone_δ_as_cocycle_coe, cochain.comp_neg],
        ext1 p q hpq,
        simp only [cochain.neg_v, cochain.comp_zero_cochain,
          cochain.left_shift_v _ _ _ (neg_add_self 1).symm q q (by linarith) p (by linarith),
          cochain.right_shift_v _ _ _ (zero_add 1).symm q q (by linarith) p (by linarith),
          zero_add, neg_neg, shift_functor_obj_X_iso, preadditive.neg_comp, mul_zero, sub_self,
          euclidean_domain.zero_div, ε_0, one_zsmul, preadditive.neg_comp_assoc, assoc,
          homological_complex.X_iso_of_eq_inv_hom, homological_complex.X_iso_of_eq_refl,
          iso.refl_hom, comp_id, preadditive.comp_neg, mapping_cone_inl_fst_assoc], }, },
    { simp only [← cochain.comp_assoc_of_first_is_zero_cochain, mapping_cone_inr_comp_snd,
        cochain.id_comp, ι_mapping_cone, cochain.comp_zsmul, mapping_cone_δ,
        ← cochain.comp_assoc_of_third_is_zero_cochain, cochain.comp_neg,
        mapping_cone_inr_comp_fst, cochain.zero_comp, neg_zero, smul_zero, add_zero,
        mapping_cone_δ_as_cocycle, self_eq_add_right, cocycle.right_shift_coe,
        cocycle.cochain_of_hom_hom_of_eq_coe],
      ext1 n,
      simp only [add_subgroup.coe_neg, cochain.comp_assoc_of_third_is_zero_cochain,
        cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_v,
        cochain.right_shift_v _ _ _ (zero_add 1).symm n n (by linarith) _ rfl, assoc,
        cochain.neg_v, preadditive.neg_comp, preadditive.comp_neg,
        mapping_cone_inr_fst_assoc, zero_comp, neg_zero], }, },
  { ext n,
    simp only [category_theory.functor.map_id, preadditive.neg_comp,
      homological_complex.neg_f_apply, homological_complex.comp_f,
      cocycle.hom_of_f, cocycle.right_shift_coe, mapping_cone_δ_as_cocycle_coe,
      shift_functor_map_f', mapping_cone_δ,
      cochain.right_shift_v _ _ _ (zero_add 1).symm n n (by linarith) _ rfl,
      shift_functor_obj_X_iso, cochain.neg_v, homological_complex.X_iso_of_eq_refl,
      preadditive.comp_neg, neg_inj,
      mapping_cone.lift_fst_f_assoc, add_subgroup.coe_neg,
      cocycle.left_shift_coe, cocycle.of_hom_coe, cochain.neg_v,
      cochain.left_shift_v _ _ _ (zero_add 1).symm _ _ rfl _ rfl,
      mul_one, sub_self, mul_zero, euclidean_domain.zero_div, add_zero, ε_1,
      homological_complex.X_iso_of_eq_refl, cochain.of_hom_v, neg_smul, one_zsmul, neg_neg],
    erw [iso.refl_hom, iso.refl_inv, id_comp, comp_id], },
end

@[simps]
def triangle_shift (T : triangle (homotopy_category C (complex_shape.up ℤ))) (n : ℤ) :
  triangle (homotopy_category C (complex_shape.up ℤ)) :=
triangle.mk (ε n • T.mor₁⟦n⟧') (ε n • T.mor₂⟦n⟧') (ε n • T.mor₃⟦n⟧' ≫ (shift_comm T.obj₁ 1 n).hom)

instance cochain_complex_shift_functor_additive (n : ℤ) :
  (category_theory.shift_functor (cochain_complex C ℤ) n).additive := { }

@[simps, reducible]
def quotient_triangulated_functor_struct :
  triangulated_functor_struct (cochain_complex C ℤ) (homotopy_category C (complex_shape.up ℤ)) :=
{ to_functor := homotopy_category.quotient _ _,
  comm_shift := quotient.comm_shift _ _, }

def induced_triangle (T : triangle (cochain_complex C ℤ)) :
  triangle (homotopy_category C (complex_shape.up ℤ)) :=
quotient_triangulated_functor_struct.map_triangle.obj T

def mapping_cone_induced_triangle_iso :
  induced_triangle (mapping_cone_triangle φ) ≅ mapping_cone_triangle' φ :=
triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) begin
  simp only [iso.refl_hom, category_theory.functor.map_id, comp_id, id_comp],
  apply eq_of_homotopy,
  apply homotopy.of_eq,
  apply comp_id,
end

lemma shift_distinguished_triangles (T : triangle (homotopy_category C (complex_shape.up ℤ)))
  (hT : T ∈ distinguished_triangles C) (n : ℤ) :
  (triangle.shift_functor _ n).obj T ∈ distinguished_triangles C :=
begin
  obtain ⟨K, L, φ, ⟨e⟩⟩:= hT,
  suffices : (triangle.shift_functor _ n).obj (mapping_cone_triangle' φ)
    ∈ distinguished_triangles C,
  { exact isomorphic_distinguished _ this _ (functor.map_iso _ e), },
  refine ⟨K⟦n⟧, L⟦n⟧, ε n • φ⟦n⟧', nonempty.intro _⟩,
  have e : (triangle.shift_functor (cochain_complex C ℤ) n).obj (mapping_cone_triangle φ) ≅
    mapping_cone_triangle (ε n • φ⟦n⟧'),
  { refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) _ (by tidy) _ _,
    { sorry, },
    { sorry, },
    { sorry, }, },
  let h : (homotopy_category.quotient C (complex_shape.up ℤ)).comm_shift ℤ :=
  { iso := quotient.comm_shift _,
    iso_zero := sorry,
    iso_add := sorry, },
  refine (triangle.shift_functor (homotopy_category C (complex_shape.up ℤ)) n).map_iso
    (mapping_cone_induced_triangle_iso φ).symm ≪≫
    ((triangle.shift_functor_comm h n).app (mapping_cone_triangle φ)).symm ≪≫
    quotient_triangulated_functor_struct.map_triangle.map_iso e ≪≫
    (mapping_cone_induced_triangle_iso _),
end

lemma rotate_distinguished_triangle (T : triangle (homotopy_category C (complex_shape.up ℤ))) :
  T ∈ distinguished_triangles C ↔ T.rotate ∈ distinguished_triangles C :=
begin
  split,
  { exact rotate_distinguished_triangle₁ T, },
  { intro h,
    replace h := rotate_distinguished_triangle₁ _ (rotate_distinguished_triangle₁ _ h),
    replace h := shift_distinguished_triangles _ h (-1),
    refine isomorphic_distinguished _ h _ _,
    exact (triangle.shift_functor_zero _).symm.app T ≪≫
      (triangle.shift_functor_iso_of_eq _ (by linarith)).app T ≪≫
      (triangle.shift_functor_add _ 1 (-1)).app T ≪≫
      (triangle.shift_functor _ (-1)).map_iso ((triangle.shift_functor_one_iso _).app T), },
end

instance : pretriangulated (homotopy_category C (complex_shape.up ℤ)) :=
{ distinguished_triangles := distinguished_triangles C,
  isomorphic_distinguished := isomorphic_distinguished,
  contractible_distinguished := contractible_distinguished,
  distinguished_cocone_triangle := distinguished_cocone_triangle,
  rotate_distinguished_triangle := rotate_distinguished_triangle,
  complete_distinguished_triangle_morphism :=
    complete_distinguished_triangle_morphism, }


lemma triangle_distinguished_iff (T : triangle (homotopy_category C (complex_shape.up ℤ))) :
  (T ∈ dist_triang (homotopy_category C (complex_shape.up ℤ)))
  ↔ ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L),
    nonempty (T ≅
      quotient_triangulated_functor_struct.map_triangle.obj (mapping_cone_triangle φ)) :=
begin
  split,
  { rintros ⟨K, L, φ, ⟨e⟩⟩,
    exact ⟨K, L, φ, ⟨e ≪≫ (mapping_cone_induced_triangle_iso φ).symm⟩⟩, },
  { rintro ⟨K, L, φ, ⟨e⟩⟩,
    exact ⟨K, L, φ, ⟨e ≪≫ (mapping_cone_induced_triangle_iso φ)⟩⟩, },
end

lemma triangle_distinguished_iff' (T : triangle (homotopy_category C (complex_shape.up ℤ))) :
  (T ∈ dist_triang (homotopy_category C (complex_shape.up ℤ))) ↔
  ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L), nonempty (T ≅
      quotient_triangulated_functor_struct.map_triangle.obj (mapping_cone_triangle φ).rotate) :=
begin
  split,
  { intro hT,
    replace hT := inv_rot_of_dist_triangle _ _ hT,
    rw triangle_distinguished_iff at hT,
    obtain ⟨K, L, φ, ⟨e⟩⟩ := hT,
    exact ⟨K, L, φ, ⟨(triangle_rotation _).counit_iso.symm.app T ≪≫
      (pretriangulated.rotate _).map_iso e ≪≫
      (map_triangle_rotate quotient_triangulated_functor_struct).app _⟩⟩, },
  { rintro ⟨K, L, φ, ⟨e⟩⟩,
    suffices : T.inv_rotate ∈ dist_triang _,
    { exact pretriangulated.isomorphic_distinguished _ (rot_of_dist_triangle _ _ this) _
        ((triangle_rotation _).counit_iso.symm.app T), },
    refine ⟨K, L, φ, ⟨(pretriangulated.inv_rotate _).map_iso e ≪≫ (inv_rotate _).map_iso
        ((map_triangle_rotate quotient_triangulated_functor_struct).symm.app _ ≪≫
        (rotate _).map_iso (mapping_cone_induced_triangle_iso φ)) ≪≫
      (triangle_rotation _).unit_iso.symm.app _⟩⟩, },
end

instance : is_triangulated (homotopy_category C (complex_shape.up ℤ)) := sorry

end homotopy_category
