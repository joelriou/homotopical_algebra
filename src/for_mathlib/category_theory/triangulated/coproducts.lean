import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.finite_products
import category_theory.limits.preserves.limits

noncomputable theory

namespace category_theory

open limits preadditive category

namespace triangulated

open pretriangulated

variables {C : Type*} [category C] [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

lemma kernel_cone_of_dist_triang₁ (T : triangle C) (hT : T ∈ dist_triang C) (zero : T.mor₃ = 0) :
  is_limit (kernel_fork.of_ι T.mor₁ (T.comp_zero₁₂ hT)) :=
is_limit_aux _ (λ s, (covariant_yoneda_exact₂ T hT s.ι s.condition).some)
    (λ s, (covariant_yoneda_exact₂ T hT s.ι s.condition).some_spec.symm)
(λ s m hm, begin
  dsimp at hm,
  rw ← sub_eq_zero,
  let f := m - (covariant_yoneda_exact₂ T hT s.ι s.condition).some,
  change f = 0,
  have hf₀ : f ≫ T.mor₁ = 0,
  { dsimp [f],
    rw [sub_comp, hm, (covariant_yoneda_exact₂ T hT s.ι s.condition).some_spec.symm, sub_self], },
  obtain ⟨g, hg⟩ := covariant_yoneda_exact₂ _ (inv_rot_of_dist_triangle _ _ hT) f hf₀,
  rw hg,
  simp only [zero, triangle.inv_rotate_mor₁, functor.map_zero, zero_comp, neg_zero, comp_zero],
end)

lemma mono_of_dist_triang₁ (T : triangle C) (hT : T ∈ dist_triang C) (zero : T.mor₃ = 0) :
  mono T.mor₁ :=
⟨λ Z f₁ f₂ hf, (kernel_cone_of_dist_triang₁ T hT zero).hom_ext begin
  rintro (_|_),
  { exact hf, },
  { dsimp,
    simp only [T.comp_zero₁₂ hT, comp_zero], },
end⟩

lemma mono_of_dist_triang₂ (T : triangle C) (hT : T ∈ dist_triang C) (zero : T.mor₁ = 0) :
  mono T.mor₂ :=
mono_of_dist_triang₁ _ (rot_of_dist_triangle _ _ hT)
  (by simp only [zero, triangle.rotate_mor₃, functor.map_zero, neg_zero])

lemma mono_of_dist_triang₃ (T : triangle C) (hT : T ∈ dist_triang C) (zero : T.mor₂ = 0) :
  mono T.mor₃ :=
mono_of_dist_triang₁ _ (rot_of_dist_triangle _ _ (rot_of_dist_triangle _ _ hT))
    (by { dsimp, rw [zero, functor.map_zero, neg_zero], })

lemma has_binary_biproduct_of_dist_triang (T : triangle C) (hT : T ∈ dist_triang C)
  (zero : T.mor₃ = 0) : has_binary_biproduct T.obj₁ T.obj₃ :=
begin
  haveI : mono T.mor₁ := mono_of_dist_triang₁ T hT zero,
  obtain ⟨i₂, hi₂⟩ := covariant_yoneda_exact₃ T hT (𝟙 T.obj₃) (by rw [zero, comp_zero]),
  obtain ⟨p₁, hp₁⟩ := covariant_yoneda_exact₂ T hT (𝟙 T.obj₂ - T.mor₂ ≫ i₂)
    (by rw [sub_comp, id_comp, assoc, ← hi₂, comp_id, sub_self]),
  let B : binary_bicone T.obj₁ T.obj₃ :=
  { X := T.obj₂,
    fst := p₁,
    snd := T.mor₂,
    inl := T.mor₁,
    inr := i₂,
    inl_fst' := by rw [← cancel_mono T.mor₁, assoc, ← hp₁, comp_sub, id_comp,
      comp_id, T.comp_zero₁₂_assoc hT, zero_comp, sub_zero],
    inl_snd' := T.comp_zero₁₂ hT,
    inr_fst' := by rw [← cancel_mono T.mor₁, assoc, zero_comp, ← hp₁, comp_sub,
      ← reassoc_of hi₂, comp_id, sub_self],
    inr_snd' := hi₂.symm, },
  exact has_binary_biproduct_of_total B (by rw [← hp₁, sub_add_cancel]),
end

instance : has_binary_biproducts C :=
⟨λ X₁ X₂, begin
  obtain ⟨Y, i₁, p₂, mem⟩ := pretriangulated.distinguished_cocone_triangle₂ (0 : X₂ ⟶ X₁⟦1⟧),
  exact has_binary_biproduct_of_dist_triang _ mem rfl,
end⟩

instance : has_finite_products C := by apply has_finite_products_of_has_binary_products

instance : has_finite_coproducts C := by apply has_finite_coproducts_of_has_binary_coproducts

lemma exists_iso_binary_product_of_dist_triang (T : triangle C) (hT : T ∈ dist_triang C)
  (zero : T.mor₃ = 0) :
  ∃ (e : T.obj₂ ≅ T.obj₁ ⨯ T.obj₃), T.mor₁ ≫ e.hom = prod.lift (𝟙 _) 0 ∧
    T.mor₂ = e.hom ≫ limits.prod.snd :=
begin
  haveI : mono T.mor₁ := mono_of_dist_triang₁ T hT zero,
  obtain ⟨i₂, hi₂⟩ := covariant_yoneda_exact₃ T hT (𝟙 T.obj₃) (by rw [zero, comp_zero]),
  obtain ⟨p₁, hp₁⟩ := covariant_yoneda_exact₂ T hT (𝟙 T.obj₂ - T.mor₂ ≫ i₂)
    (by rw [sub_comp, id_comp, assoc, ← hi₂, comp_id, sub_self]),
  let e : T.obj₂ ≅ T.obj₁ ⨯ T.obj₃ :=
  { hom := prod.lift p₁ T.mor₂,
    inv := limits.prod.fst ≫ T.mor₁ + limits.prod.snd ≫ i₂,
    hom_inv_id' :=  by simp only [comp_add, prod.lift_fst_assoc, prod.lift_snd_assoc,
      ← hp₁, ← hi₂, sub_add_cancel],
    inv_hom_id' := begin
      ext,
      { simp only [← cancel_mono T.mor₁, add_comp, assoc, prod.lift_fst, id_comp, ← hp₁,
          comp_sub, comp_id, T.comp_zero₁₂_assoc hT, zero_comp, comp_zero, sub_zero],
        rw [← reassoc_of hi₂, sub_self, add_zero], },
      { simp only [add_comp, assoc, prod.lift_snd, id_comp, T.comp_zero₁₂ hT, comp_zero,
          zero_add, ← hi₂, comp_id], },
    end, },
  refine ⟨e, _, by simp only [prod.lift_snd]⟩,
  { rw [← cancel_mono e.inv, assoc, e.hom_inv_id, comp_id],
    simp only [comp_add, prod.lift_fst_assoc, id_comp, prod.lift_snd_assoc, zero_comp, add_zero], },
end

lemma binary_product_triangle_distinguished (X₁ X₂ : C) :
  triangle.mk C (prod.lift (𝟙 X₁) (0 : X₁ ⟶ X₂)) limits.prod.snd 0 ∈ dist_triang C :=
begin
  obtain ⟨Y, g, h, mem⟩ := pretriangulated.distinguished_cocone_triangle₂ (0 : X₂ ⟶ X₁⟦(1 : ℤ)⟧),
  obtain ⟨e, ⟨he₁, he₂⟩⟩ := exists_iso_binary_product_of_dist_triang _ mem rfl,
  refine pretriangulated.isomorphic_distinguished _ mem _ _,
  symmetry,
  dsimp at he₁ he₂,
  refine triangle.mk_iso _ _ (iso.refl _) e (iso.refl _) _ _ _,
  { dsimp,
    simp only [prod.comp_lift, comp_id, comp_zero, id_comp, he₁], },
  { dsimp,
    rw [comp_id, he₂], },
  { simp only [triangle.mk_mor₃, zero_comp, comp_zero], },
end

@[simps]
def triangle.coproduct {I : Type*} (T : I → triangle C) [has_coproduct (λ i, (T i).obj₁)]
  [has_coproduct (λ i, (T i).obj₂)] [has_coproduct (λ i, (T i).obj₃)]
  [has_coproduct (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)] : triangle C :=
{ obj₁ := ∐ (λ i, (T i).obj₁),
  obj₂ := ∐ (λ i, (T i).obj₂),
  obj₃ := ∐ (λ i, (T i).obj₃),
  mor₁ := limits.sigma.map (λ i, (T i).mor₁),
  mor₂ := limits.sigma.map (λ i, (T i).mor₂),
  mor₃ := limits.sigma.map (λ i, (T i).mor₃) ≫ sigma_comparison _ _, }

/-lemma triangle.coproduct_distinghished {I : Type*} (T : I → triangle C)
  [has_coproduct (λ i, (T i).obj₁)]
  [has_coproduct (λ i, (T i).obj₂)] [has_coproduct (λ i, (T i).obj₃)]
  [has_coproduct (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)]
  (hT : ∀ i, (T i) ∈ dist_triang C) : triangle.coproduct T ∈ dist_triang C := sorry-/

@[simps]
def triangle.product {I : Type*} (T : I → triangle C) [has_product (λ i, (T i).obj₁)]
  [has_product (λ i, (T i).obj₂)] [has_product (λ i, (T i).obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)] : triangle C :=
{ obj₁ := ∏ (λ i, (T i).obj₁),
  obj₂ := ∏ (λ i, (T i).obj₂),
  obj₃ := ∏ (λ i, (T i).obj₃),
  mor₁ := limits.pi.map (λ i, (T i).mor₁),
  mor₂ := limits.pi.map (λ i, (T i).mor₂),
  mor₃ := limits.pi.map (λ i, (T i).mor₃) ≫ inv (pi_comparison _ _), }

lemma triangle.product_distinghished {I : Type*} (T : I → triangle C)
  [has_product (λ i, (T i).obj₁)]
  [has_product (λ i, (T i).obj₂)] [has_product (λ i, (T i).obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)]
  (hT : ∀ i, (T i) ∈ dist_triang C) : triangle.product T ∈ dist_triang C :=
begin
  sorry,
end

@[simps]
def triangle.coprod (T₁ T₂ : triangle C) [has_binary_product T₁.obj₁ T₂.obj₁]
  [has_binary_product T₁.obj₂ T₂.obj₂] [has_binary_product T₁.obj₃ T₂.obj₃]
  [has_binary_product ((shift_functor C (1 : ℤ)).obj T₁.obj₃)
    ((shift_functor C (1 : ℤ)).obj T₁.obj₃)] : triangle C :=
{ obj₁ := T₁.obj₁ ⨿ T₂.obj₁,
  obj₂ := T₁.obj₂ ⨿ T₂.obj₂,
  obj₃ := T₁.obj₃ ⨿ T₂.obj₃,
  mor₁ := coprod.map T₁.mor₁ T₂.mor₁,
  mor₂ := coprod.map T₁.mor₂ T₂.mor₂,
  mor₃ := coprod.map T₁.mor₃ T₂.mor₃ ≫ coprod_comparison _ _ _, }

@[simps]
def coprod_iso_coproduct {D : Type*} [category D] (X : walking_pair → D)
  [has_coproduct (λ i, X i)] [has_binary_coproduct (X walking_pair.left) (X walking_pair.right)] :
  X walking_pair.left ⨿ X walking_pair.right ≅ ∐ X :=
{ hom := coprod.desc (sigma.ι _ _) (sigma.ι _ _),
  inv := sigma.desc (by { rintro (_|_), exacts [coprod.inl, coprod.inr], }),
  hom_inv_id' := by tidy,
  inv_hom_id' := by { ext j, discrete_cases, cases j, tidy, }, }

/-
lemma triangle.coprod_distinguished {I : Type*} (T₁ T₂ : triangle C)
  (hT₁ : T₁ ∈ dist_triang C) (hT₂ : T₂ ∈ dist_triang C) :
  triangle.coprod T₁ T₂ ∈ dist_triang C :=
begin
  let T' : walking_pair → triangle C := by { rintro (_|_), exacts [T₁, T₂], },
  have hT' := triangle.coproduct_distinghished T' (by { rintro (_|_), exacts [hT₁, hT₂], }),
  refine isomorphic_distinguished _ hT' _ _,
  refine triangle.mk_iso _ _ (coprod_iso_coproduct (λ i, (T' i).obj₁))
    (coprod_iso_coproduct (λ i, (T' i).obj₂)) (coprod_iso_coproduct (λ i, (T' i).obj₃))
    (by tidy) (by tidy) _,
  ext,
  { dsimp [T'],
    simp only [assoc, coprod.inl_map_assoc, coprod_comparison_inl_assoc, coprod.desc_comp_assoc,
      ι_colim_map, discrete.nat_trans_app, coprod.desc_comp, ι_comp_sigma_comparison,
      coprod.inl_desc, ι_colim_map_assoc, ← functor.map_comp], },
  { dsimp [T'],
    simp only [assoc, coprod.inr_map_assoc, coprod_comparison_inr_assoc, coprod.desc_comp_assoc,
      ι_colim_map, discrete.nat_trans_app, coprod.desc_comp, ι_comp_sigma_comparison,
      coprod.inr_desc, ι_colim_map_assoc, ← functor.map_comp], },
end-/

end triangulated

end category_theory
