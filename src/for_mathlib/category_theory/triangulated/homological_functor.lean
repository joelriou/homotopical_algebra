import for_mathlib.category_theory.triangulated.pretriangulated_misc
import algebra.homology.short_complex.exact
import for_mathlib.category_theory.localization.triangulated_subcategory
import for_mathlib.category_theory.shift_misc
import for_mathlib.category_theory.preadditive.misc
import category_theory.limits.preserves.shapes.zero
import for_mathlib.category_theory.shift_compatibility_minus

noncomputable theory

namespace category_theory

open limits category pretriangulated
open_locale zero_object

lemma limits.exists_discrete_walking_pair_exists_iso_pair
  {C : Type*} [category C] (F : discrete walking_pair ⥤ C) :
  ∃ (X₁ X₂ : C), nonempty (F ≅ pair X₁ X₂) :=
⟨F.obj (discrete.mk walking_pair.left), F.obj (discrete.mk walking_pair.right),
  ⟨discrete.nat_iso_functor ≪≫ eq_to_iso (by { congr' 1, ext j, cases j, tidy, })⟩⟩

section

variables {C D : Type*} [category C] [category D] [has_zero_morphisms C] [has_zero_morphisms D]

instance preserves_limit_functor_empty (F : C ⥤ D) [F.preserves_zero_morphisms]
  [has_zero_object C] : preserves_limit (functor.empty.{0} C) F :=
begin
  let c : cone (functor.empty.{0} C) := cone.mk 0 { app := λ X, 0, },
  have hc : is_limit c :=
  { lift := λ s, 0,
    fac' := by rintro s ⟨⟨⟩⟩,
    uniq' := λ s m hm, subsingleton.elim _ _, },
  refine preserves_limit_of_preserves_limit_cone hc
  { lift := λ s, 0,
    fac' := by rintro s ⟨⟨⟩⟩,
    uniq' := λ s m hm, begin
      refine is_zero.eq_of_tgt _ _ _,
      dsimp [functor.map_cone],
      rw [limits.is_zero.iff_id_eq_zero, ← F.map_id,
        subsingleton.elim (𝟙 (0 : C)) 0, F.map_zero],
    end, },
end

end

section
/-- should be moved to short_complex.exact -/

variables {C : Type*} [category C]

lemma short_complex.exact.is_zero_of_both_zeros [has_zero_morphisms C]
  {S : short_complex C} (ex : S.exact)
  (h₁ : S.f = 0) (h₂ : S.g = 0) : is_zero S.X₂ :=
(short_complex.homology_data.of_zeros S h₁ h₂).exact_iff.1 ex

lemma short_complex.exact.epi_f_iff_g_eq_zero [preadditive C] {S : short_complex C}
  (ex : S.exact) : epi S.f ↔ S.g = 0 :=
begin
  split,
  { introI,
    simp only [← cancel_epi S.f, S.zero, comp_zero], },
  { intro hg,
    haveI := ex.has_homology,
    haveI := S.is_iso_cycles_i_of hg,
    rw preadditive.epi_iff_cancel_zero,
    intros Z h eq,
    rw [← S.p_desc_cycles_co _ eq, ← cancel_epi (S.cycles_i),
      reassoc_of (S.exact_iff_cycles_i_p_cycles_co_zero.1 ex), comp_zero, zero_comp], },
end

lemma short_complex.exact.mono_g_iff_f_eq_zero [preadditive C] {S : short_complex C}
  (ex : S.exact) : mono S.g ↔ S.f = 0 :=
begin
  split,
  { introI,
    simp only [← cancel_mono S.g, S.zero, zero_comp], },
  { intro hf,
    haveI := ex.has_homology,
    haveI := S.is_iso_p_cycles_co_of hf,
    rw preadditive.mono_iff_cancel_zero,
    intros Z h eq,
    rw [← S.lift_cycles_i _ eq, ← cancel_mono (S.p_cycles_co), assoc,
      S.exact_iff_cycles_i_p_cycles_co_zero.1 ex, comp_zero, zero_comp], },
end

end

variables {C D A : Type*} [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), (shift_functor C n).additive] [pretriangulated C]
  [category D] [has_zero_object D] [has_shift D ℤ]
  [preadditive D] [∀ (n : ℤ), (shift_functor D n).additive] [pretriangulated D]
  [category A] [abelian A] (F : C ⥤ A) [functor.preserves_zero_morphisms F]

@[simps]
def pretriangulated.triangle.short_complex (T : pretriangulated.triangle C)
  (hT : T ∈ dist_triang C) : short_complex C :=
  (candidate_triangle.of_distinguished T hT).short_complex

namespace functor

@[protected]
class is_homological : Prop :=
(map_distinguished [] : ∀ (T : pretriangulated.triangle C) (hT : T ∈ dist_triang C),
  ((T.short_complex hT).map F).exact)

namespace is_homological

lemma mk' (hF : ∀ (T : pretriangulated.triangle C) (hT : T ∈ dist_triang C),
  ∃ (T' : pretriangulated.triangle C) (hT' : T' ∈ dist_triang C) (e : T ≅ T'),
    ((T'.short_complex hT').map F).exact) :
  F.is_homological :=
⟨λ T hT, begin
  obtain ⟨T', hT', e, ex'⟩ := hF T hT,
  refine (short_complex.exact_iff_of_iso (F.map_short_complex.map_iso
    ((candidate_triangle.to_short_complex_functor C).map_iso _))).2 ex',
  exact preimage_iso (full_subcategory_inclusion _ : candidate_triangle C ⥤ _) e,
end⟩

variable {F}

lemma of_iso {G : C ⥤ A} [G.preserves_zero_morphisms] (e : G ≅ F) [F.is_homological] :
  G.is_homological :=
is_homological.mk (λ T hT, (short_complex.exact_iff_of_iso
  (short_complex.map_nat_iso _ e)).2 (is_homological.map_distinguished F T hT))

end is_homological

section

open triangulated

variable [F.is_homological]

def kernel_of_is_homological : set C :=
λ K, ∀ (n : ℤ), limits.is_zero (F.obj (K⟦n⟧))

instance : is_triangulated_subcategory F.kernel_of_is_homological :=
{ zero := λ n, limits.is_zero.of_iso (is_zero_zero A)
    (F.map_iso (shift_functor C n).map_zero_object ≪≫ F.map_zero_object),
  shift := λ K m hK n, limits.is_zero.of_iso (hK (m+n))
    (F.map_iso ((shift_functor_add C m n).app K).symm),
  ext₂ := λ T hT h₁ h₃ n, (is_homological.map_distinguished F _
    (triangle.shift_distinguished _ T hT n)).is_zero_of_both_zeros
    (is_zero.eq_of_src (h₁ _) _ _) (is_zero.eq_of_tgt (h₃ _) _ _), }

instance kernel_of_is_homological_saturated :
  saturated F.kernel_of_is_homological :=
⟨λ L K i, begin
  introI,
  intros hL n,
  replace hL := hL n,
  rw limits.is_zero.iff_id_eq_zero at ⊢ hL,
  have eq : 𝟙 _ = i ≫ 𝟙 _ ≫ retraction i := by simp only [id_comp, is_split_mono.id],
  replace eq := (shift_functor C n ⋙ F).congr_map eq,
  dsimp only [functor.comp_map] at eq,
  simpa only [functor.map_comp, functor.map_id, hL, zero_comp, comp_zero] using eq,
end⟩

def W_of_is_homological : morphism_property C :=
λ X Y f, ∀ (n : ℤ), is_iso (F.map (f⟦n⟧'))

instance : preserves_limits_of_shape (discrete walking_pair) F :=
begin
  suffices : ∀ (X₁ X₂ : C), preserves_limit (pair X₁ X₂) F,
  { haveI := this,
    exact ⟨λ X, preserves_limit_of_iso_diagram F
      (category_theory.limits.exists_discrete_walking_pair_exists_iso_pair X)
      .some_spec.some_spec.some.symm⟩, },
  intros X₁ X₂,
  haveI : mono (F.biprod_comparison X₁ X₂),
  { rw preadditive.mono_iff_cancel_zero,
    intros Z f hf,
    have h₂ : f ≫ F.map biprod.snd = 0,
    { simpa only [assoc, biprod_comparison_snd, zero_comp] using hf =≫ biprod.snd, },
    have ex := is_homological.map_distinguished F _
      (binary_biproduct_triangle_distinguished X₁ X₂),
    let S := short_complex.mk (F.map (biprod.inl : X₁ ⟶ _)) (F.map (biprod.snd : _ ⟶ X₂))
      (by { rw ← F.map_comp, simp only [biprod.inl_snd, functor.map_zero]}),
    have ex : S.short_exact := short_complex.short_exact.mk
      (is_homological.map_distinguished F _ (binary_biproduct_triangle_distinguished X₁ X₂)),
    have hf' : ∃ (f₁ : Z ⟶ F.obj X₁), f₁ ≫ F.map biprod.inl = f := ⟨_, ex.lift_f f h₂⟩,
    obtain ⟨f₁, rfl⟩ := hf',
    replace hf := hf =≫ biprod.fst,
    simp only [assoc, biprod_comparison_fst, zero_comp, ← F.map_comp,
      biprod.inl_fst, F.map_id, comp_id] at hf,
    rw [hf, zero_comp], },
  haveI : preserves_binary_biproduct X₁ X₂ F :=
    limits.preserves_binary_biproduct_of_mono_biprod_comparison F,
  apply limits.preserves_binary_product_of_preserves_binary_biproduct,
end


@[priority 100]
instance is_homological.additive : F.additive :=
functor.additive_of_preserves_binary_products _

lemma kernel_of_is_homological_W :
  triangulated.subcategory.W F.kernel_of_is_homological = F.W_of_is_homological :=
begin
  ext X Y f,
  split,
  { intros hf n,
    let f' := f⟦n⟧',
    change is_iso (F.map f'),
    have hf' : triangulated.subcategory.W F.kernel_of_is_homological f' :=
      (morphism_property.compatible_with_shift.iff _ f n).2 hf,
    obtain ⟨Z, g', h', dist, mem⟩ := hf',
    rw is_iso_iff_mono_and_epi,
    split,
    { exact (functor.is_homological.map_distinguished F _
        (inv_rot_of_dist_triangle _ _ dist)).mono_g_iff_f_eq_zero.2
        (limits.is_zero.eq_of_src (mem (-1)) _ _), },
    { exact (functor.is_homological.map_distinguished F _ dist).epi_f_iff_g_eq_zero.2
        (limits.is_zero.eq_of_tgt
          (limits.is_zero.of_iso (mem 0) (F.map_iso ((shift_functor_zero C ℤ).symm.app _))) _ _), }, },
  { intro hf,
    obtain ⟨Z, g, h, mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ f,
    have w : f ≫ g = 0 := pretriangulated.triangle.comp_zero₁₂ _ mem,
    refine ⟨Z, g, h, mem, λ n, _⟩,
    refine short_complex.exact.is_zero_of_both_zeros
      (functor.is_homological.map_distinguished F _
        (rot_of_dist_triangle _ _ (triangle.shift_distinguished _ _ mem n))) _ _,
    { dsimp [pretriangulated.triangle.short_complex],
      haveI := hf n,
      rw ← cancel_epi (F.map (f⟦n⟧')),
      simp only [F.map_zsmul, comp_zero, preadditive.comp_zsmul, ← functor.map_comp, w,
        functor.map_zero, zsmul_zero], },
    { haveI : is_iso (F.map (f⟦n⟧'⟦(1 : ℤ)⟧')) :=
        (nat_iso.is_iso_map_iff (iso_whisker_right (shift_functor_add _ n 1) F) f).1 (hf (n+1)),
      rw ← cancel_mono (F.map (f⟦n⟧'⟦(1 : ℤ)⟧')),
      have w' := F.congr_map (pretriangulated.triangle.comp_zero₂₃ _
        (rot_of_dist_triangle _ _ (triangle.shift_distinguished _ _ mem n))),
      dsimp [pretriangulated.triangle.short_complex] at ⊢ w',
      simp only [preadditive.comp_neg, functor.map_zsmul, assoc, preadditive.comp_zsmul,
        preadditive.zsmul_comp, functor.map_neg, F.map_zero, smul_neg, neg_eq_zero,
        smul_smul, ← units.coe_mul, ← mul_zpow, mul_neg, neg_mul, neg_neg, one_mul, one_smul,
        one_zpow, units.coe_one] at w',
      simp only [← F.map_comp, zero_comp, assoc, preadditive.zsmul_comp, F.map_zsmul, w',
        smul_zero], }, },
end

instance shift_is_homological (n : ℤ) :
  (shift_functor C n ⋙ F).is_homological :=
⟨λ T hT, begin
  refine (short_complex.exact_iff_of_iso _).1
    (functor.is_homological.map_distinguished F _ (triangle.shift_distinguished _ _ hT n)),
  refine short_complex.mk_iso (preadditive.mul_iso ((-1 : units ℤ)^n) (iso.refl _))
    (iso.refl _) (preadditive.mul_iso ((-1 : units ℤ)^n) (iso.refl _)) _ _,
  { dsimp, simp only [preadditive.zsmul_comp, id_comp, comp_id, F.map_zsmul], },
  { dsimp, simp only [preadditive.comp_zsmul, id_comp, comp_id, F.map_zsmul, smul_smul,
      ← units.coe_mul, ← mul_zpow, mul_neg, neg_mul, neg_neg, one_mul, one_smul, one_zpow,
      units.coe_one], },
end⟩

end

@[priority 100]
instance triangulated_functor_preserves_zero_morphisms
  (F : C ⥤ D) [F.has_comm_shift ℤ] [F.is_triangulated] :
  F.preserves_zero_morphisms :=
⟨λ X₁ X₂, begin
  have h := triangle.comp_zero₁₂ _ (F.map_distinguished _
    (binary_product_triangle_distinguished X₁ X₂)),
  dsimp at h,
  simpa only [← F.map_comp, prod.lift_snd] using h,
end⟩

instance triangulated_functor_preserves_binary_products
  (F : C ⥤ D) [F.has_comm_shift ℤ] [F.is_triangulated] :
  preserves_limits_of_shape (discrete walking_pair) F :=
begin
  suffices : ∀ (X₁ X₂ : C), preserves_limit (pair X₁ X₂) F,
  { haveI := this,
    exact ⟨λ X, preserves_limit_of_iso_diagram F
      (category_theory.limits.exists_discrete_walking_pair_exists_iso_pair X)
      .some_spec.some_spec.some.symm⟩, },
  intros X₁ X₂,
  haveI : mono (F.biprod_comparison X₁ X₂),
  { rw preadditive.mono_iff_cancel_zero,
    intros Z f hf,
    have h₂ : f ≫ F.map biprod.snd = 0,
    { simpa only [assoc, biprod_comparison_snd, zero_comp] using hf =≫ biprod.snd, },
    obtain ⟨f₁, rfl⟩ := covariant_yoneda_exact₂ _
      (F.map_distinguished _ (binary_biproduct_triangle_distinguished X₁ X₂)) f h₂,
    replace hf := hf =≫ biprod.fst,
    dsimp [triangulated_functor.map_triangle] at hf,
    simp only [assoc, biprod_comparison_fst, zero_comp, ← F.map_comp, biprod.inl_fst,
      F.map_id, comp_id] at hf,
    rw [hf, zero_comp], },
  haveI : preserves_binary_biproduct X₁ X₂ F :=
    limits.preserves_binary_biproduct_of_mono_biprod_comparison _,
  apply limits.preserves_binary_product_of_preserves_binary_biproduct,
end

@[priority 100]
instance triangulated_functor_additive (F : C ⥤ D) [F.has_comm_shift ℤ] [F.is_triangulated ] :
  F.additive :=
functor.additive_of_preserves_binary_products _

@[priority 100]
instance is_homological.of_comp (F : C ⥤ D) (G : D ⥤ A) [F.has_comm_shift ℤ]
  [F.is_triangulated] [G.preserves_zero_morphisms]
  [G.is_homological] : (F ⋙ G).is_homological :=
⟨λ T hT, begin
  have h := is_homological.map_distinguished G _ (F.map_distinguished _ hT),
  exact h,
end⟩

namespace is_homological

variables (F) (T : pretriangulated.triangle C) (hT : T ∈ dist_triang C)
  (n₀ n₁ : ℤ) (h : n₁ = n₀+1)

include h

def δ : F.obj (T.obj₃⟦n₀⟧) ⟶ F.obj (T.obj₁⟦n₁⟧) :=
F.map (T.mor₃⟦n₀⟧' ≫ (shift_functor_add' C (1 : ℤ) n₀ n₁ (by rw [h, add_comm])).inv.app T.obj₁)

omit h

include hT

lemma δ_comp : δ F T n₀ n₁ h ≫ F.map (T.mor₁⟦n₁⟧') = 0 :=
begin
  dsimp only [δ],
  rw [← F.map_comp, assoc, ← nat_trans.naturality],
  erw [← functor.map_comp_assoc, pretriangulated.triangle.comp_zero₃₁ _ hT],
  simp only [functor.map_zero, zero_comp],
end

lemma comp_δ : F.map (T.mor₂⟦n₀⟧') ≫ δ F T n₀ n₁ h  = 0 :=
begin
  dsimp only [δ],
  rw [← F.map_comp, ← functor.map_comp_assoc, pretriangulated.triangle.comp_zero₂₃ _ hT],
  simp only [functor.map_zero, zero_comp],
end

variable [hF : F.is_homological]

include hF

lemma ex₂ (n : ℤ) :
  (short_complex.mk (F.map (T.mor₁⟦n⟧')) (F.map (T.mor₂⟦n⟧'))
    (by rw [← F.map_comp, ← functor.map_comp, pretriangulated.triangle.comp_zero₁₂ _ hT,
      functor.map_zero, F.map_zero])).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (is_homological.map_distinguished F _ (pretriangulated.triangle.shift_distinguished C T hT n)),
  refine short_complex.mk_iso (iso.refl _) (preadditive.mul_iso ((-1 : units ℤ)^n) (iso.refl _))
    (iso.refl _) _ _,
  { dsimp,
    simp only [id_comp, linear.comp_smul, comp_id, F.map_zsmul, smul_smul,
      int.units_coe_mul_self, one_zsmul], },
  { dsimp,
    simp only [linear.smul_comp, id_comp, comp_id, F.map_zsmul], },
end

lemma ex₃ :
  (short_complex.mk (F.map (T.mor₂⟦n₀⟧')) (δ F T n₀ n₁ h) (comp_δ F T hT n₀ n₁ h)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (is_homological.map_distinguished F _ ((rotate_distinguished_triangle _).1
      (pretriangulated.triangle.shift_distinguished C T hT n₀))),
  refine short_complex.mk_iso (iso.refl _) (preadditive.mul_iso ((-1 : units ℤ)^n₀) (iso.refl _))
    (F.map_iso ((shift_functor_add' C n₀ (1 : ℤ) n₁ h).symm.app T.obj₁)) _ _,
  { dsimp,
    simp only [id_comp, comp_id, F.map_zsmul, preadditive.comp_zsmul, smul_smul,
      int.units_coe_mul_self, one_zsmul], },
  { dsimp [δ],
    simp only [preadditive.zsmul_comp, id_comp, F.map_zsmul, ← F.map_comp, assoc],
    congr' 3,
    simp only [shift_functor_add_comm_hom_app],
    dsimp only [shift_functor_add', eq_to_iso, iso.trans],
    simp only [nat_trans.comp_app, eq_to_hom_app, assoc,
      iso.hom_inv_id_app_assoc, eq_to_hom_trans], },
end

lemma ex₁ :
  (short_complex.mk (δ F T n₀ n₁ h) (F.map (T.mor₁⟦n₁⟧')) (δ_comp F T hT n₀ n₁ h)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (is_homological.map_distinguished F _ ((inv_rotate_distinguished_triangle _).2
      (pretriangulated.triangle.shift_distinguished C T hT n₁))),
  refine short_complex.mk_iso
    (F.map_iso ((shift_functor_add' C n₁ (-1) n₀
      (by rw [h, int.add_neg_one, add_tsub_cancel_right])).symm.app T.obj₃))
    (preadditive.mul_iso ((-1 : units ℤ)^n₀) (iso.refl _))
    (preadditive.mul_iso ((-1 : units ℤ)) (iso.refl _)) _ _,
  { change F.map ((shift_functor_add' C n₁ (-1 : ℤ) n₀ _).inv.app T.obj₃) ≫
      F.map (T.mor₃⟦n₀⟧' ≫ (shift_functor_add' C 1 n₀ n₁ _).inv.app T.obj₁) =
      F.map (-(shift_functor C (-1 : ℤ)).map (((-1 : units ℤ)^n₁ • T.mor₃⟦n₁⟧') ≫ (shift_functor_add_comm C 1 n₁).hom.app _) ≫
      (shift_shift_neg (T.obj₁⟦n₁⟧) (1 : ℤ)).hom) ≫ ((-1 : units ℤ)^n₀ • 𝟙 _),
    rw functor.map_neg,
    erw preadditive.zsmul_comp,
    erw preadditive.comp_zsmul,
    rw functor.map_zsmul,
    rw preadditive.zsmul_comp,
    rw functor.map_zsmul,
    rw comp_id,
    rw smul_neg,
    rw smul_smul,
    simp only [h, zpow_add, zpow_one, mul_neg, units.coe_neg, neg_smul, neg_neg, mul_one,
      int.units_coe_mul_self, one_smul, ← F.map_comp],
    erw ← nat_trans.naturality_assoc,
    rw [(shift_functor C (-1 : ℤ)).map_comp, assoc],
    dsimp only [functor.comp_map],
    congr' 2,
    apply shift_compatibility_add_comm, },
  { dsimp,
    simp only [id_comp, comp_id, F.map_zsmul, preadditive.comp_zsmul, smul_smul, id_comp,
      preadditive.zsmul_comp, h, zpow_add, zpow_one, mul_neg, mul_one, units.coe_neg, neg_neg], },
end

end is_homological

end functor

end category_theory
