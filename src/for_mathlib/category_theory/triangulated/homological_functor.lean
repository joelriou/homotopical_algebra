import for_mathlib.category_theory.triangulated.pretriangulated_misc
import algebra.homology.exact
import for_mathlib.category_theory.localization.triangulated_subcategory

namespace category_theory

open limits category pretriangulated

/-- should be moved to algebra.homology.exact -/
def short_complex.exact.is_zero_of_both_zeros {C : Type*} [category C] [has_zero_morphisms C]
  {S : short_complex C} (ex : S.exact) (h₁ : S.f = 0) (h₂ : S.g = 0) : is_zero S.X₂ :=
(short_complex.homology_data.of_zeros S h₁ h₂).exact_iff.1 ex

variables {C D : Type*} [category C] [category D] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), (shift_functor C n).additive] [pretriangulated C]
  [abelian D] (F : C ⥤ D) [functor.additive F]

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

lemma of_iso {G : C ⥤ D} [additive G] (e : G ≅ F) [F.is_homological] :
  G.is_homological :=
is_homological.mk (λ T hT, (short_complex.exact_iff_of_iso
  (short_complex.map_nat_iso _ e)).2 (is_homological.map_distinguished F T hT))

end is_homological

def kernel_of_is_homological [F.is_homological] : triangulated.subcategory C :=
{ set := λ K, ∀ (n : ℤ), limits.is_zero (F.obj (K⟦n⟧)),
  zero := λ n, limits.is_zero.of_iso (is_zero_zero D)
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
  { sorry, },
  { sorry, },
end

end functor

end category_theory
