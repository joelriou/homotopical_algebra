import for_mathlib.category_theory.triangulated.pretriangulated_misc
import algebra.homology.short_complex.exact
import for_mathlib.category_theory.localization.triangulated_subcategory
import for_mathlib.category_theory.shift_misc

namespace category_theory

namespace preadditive

variables {C : Type*} [category C] [preadditive C] {X Y : C}

@[simps]
def mul_iso (a : units ℤ) (e : X ≅ Y) : X ≅ Y :=
{ hom := (a : ℤ) • e.hom,
  inv := ((a⁻¹ : units ℤ) : ℤ) • e.inv,
  hom_inv_id' := by rw [preadditive.comp_zsmul, preadditive.zsmul_comp, smul_smul,
    units.inv_mul, one_smul, e.hom_inv_id],
  inv_hom_id' := by rw [preadditive.comp_zsmul, preadditive.zsmul_comp, smul_smul,
    units.mul_inv, one_smul, e.inv_hom_id], }

end preadditive

open limits category pretriangulated

section
/-- should be moved to short_complex.exact -/

variables {C : Type*} [category C]

def short_complex.exact.is_zero_of_both_zeros [has_zero_morphisms C]
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
  [category A] [abelian A] (F : C ⥤ A) [functor.additive F]

@[simps]
def pretriangulated.triangle.short_complex (T : pretriangulated.triangle C)
  (hT : T ∈ dist_triang C) : short_complex C :=
  short_complex.mk T.mor₁ T.mor₂ (pretriangulated.triangle.comp_zero₁₂ _ hT)

namespace functor

@[protected]
class is_homological : Prop :=
(map_distinguished [] : ∀ (T : pretriangulated.triangle C) (hT : T ∈ dist_triang C),
    ((T.short_complex hT).map F).exact)

namespace is_homological

variable {F}

lemma of_iso {G : C ⥤ A} [additive G] (e : G ≅ F) [F.is_homological] :
  G.is_homological :=
is_homological.mk (λ T hT, (short_complex.exact_iff_of_iso
  (short_complex.map_nat_iso _ e)).2 (is_homological.map_distinguished F T hT))

end is_homological

def kernel_of_is_homological [F.is_homological] : triangulated.subcategory C :=
{ set := λ K, ∀ (n : ℤ), limits.is_zero (F.obj (K⟦n⟧)),
  zero := λ n, limits.is_zero.of_iso (is_zero_zero A)
    (F.map_iso (shift_functor C n).map_zero_object ≪≫ F.map_zero_object),
  shift := λ K m hK n, limits.is_zero.of_iso (hK (m+n))
    (F.map_iso ((shift_functor_add C m n).app K).symm),
  ext₂ := λ T hT h₁ h₃ n, (is_homological.map_distinguished F _
    (triangle.shift_distinguished _ T hT n)).is_zero_of_both_zeros
    (is_zero.eq_of_src (h₁ _) _ _) (is_zero.eq_of_tgt (h₃ _) _ _), }

instance kernel_of_is_homological_saturated [F.is_homological] : F.kernel_of_is_homological.saturated :=
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

def W_of_is_homological [F.is_homological] : morphism_property C :=
λ X Y f, ∀ (n : ℤ), is_iso (F.map (f⟦n⟧'))

lemma kernel_of_is_homological_W [F.is_homological] :
  F.kernel_of_is_homological.W = F.W_of_is_homological :=
begin
  ext X Y f,
  split,
  { intros hf n,
    let f' := f⟦n⟧',
    change is_iso (F.map f'),
    have hf' : F.kernel_of_is_homological.W f' :=
      (morphism_property.compatible_with_shift.iff F.kernel_of_is_homological.W f n).2 hf,
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

instance shift_is_homological [F.is_homological] (n : ℤ) :
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

instance triangulated_functor_additive (F : triangulated_functor C D) : F.to_functor.additive := sorry

lemma is_homological.of_comp (F : triangulated_functor C D) (G : D ⥤ A) [G.additive]
  [G.is_homological] : (F.to_functor ⋙ G).is_homological :=
⟨λ T hT, by convert is_homological.map_distinguished G _ (F.map_distinguished _ hT)⟩

end functor

end category_theory

/- todo : localize homological_functor -/
