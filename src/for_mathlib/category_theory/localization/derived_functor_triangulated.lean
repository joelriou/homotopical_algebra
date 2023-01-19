import for_mathlib.category_theory.localization.derived_functor_shift
import for_mathlib.category_theory.triangulated.is_triangulated_subcategory

open category_theory category_theory.category category_theory.limits

noncomputable theory

namespace category_theory

namespace functor

variables {C H D : Type*} [category C] [category H] [category D]
  [has_shift C ℤ] [has_shift H ℤ] [has_shift D ℤ]
  [has_zero_object C] [has_zero_object H] [has_zero_object D]
  [preadditive C] [preadditive H] [preadditive D]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [∀ (n : ℤ), (shift_functor H n).additive]
  [∀ (n : ℤ), (shift_functor D n).additive]
  [pretriangulated C] [pretriangulated H] [pretriangulated D]
  (F : C ⥤ D) (L : C ⥤ H) [F.has_comm_shift ℤ] [L.has_comm_shift ℤ]
  [functor.is_triangulated F] [functor.is_triangulated L]
  [ess_surj_on_dist_triang L]
  (W : morphism_property C) [L.is_localization W]
  [F.has_right_derived_functor W]

/-- not sure it is necessary -/
lemma right_derived_functor_is_triangulated
  (hF : ∀ (f : arrow C), ∃ (g : arrow C) (τ : f ⟶ g)
  (hg₁ : is_iso ((F.right_derived_functor_α L W).app g.left))
  (hg₂ : is_iso ((F.right_derived_functor_α L W).app g.right)), by exact W τ.left ∧ W τ.right)
  (hF' : triangulated.is_triangulated_subcategory (λ (X : C), nonempty (is_iso ((F.right_derived_functor_α L W).app X)))) :
  (F.right_derived_functor L W).is_triangulated :=
⟨λ T hT, begin
  have pif := triangulated.is_triangulated_subcategory (λ (X : C), nonempty (is_iso ((F.right_derived_functor_α L W).app X))),
  obtain ⟨T', hT', ⟨e⟩⟩ := ess_surj_on_dist_triang.condition L T hT,
  obtain ⟨g, τ, hg₁, hg₂, ⟨w₁, w₂⟩⟩ := hF (arrow.mk T'.mor₁),
  obtain ⟨Z, γ, γ', hT''⟩ := pretriangulated.distinguished_cocone_triangle _ _ g.hom,
  obtain ⟨t, ht₁, ht₂⟩ := pretriangulated.complete_distinguished_triangle_morphism _ _
    hT' hT'' τ.left τ.right τ.w.symm,
  let φ : T' ⟶ pretriangulated.triangle.mk g.hom γ γ' :=
  { hom₁ := τ.left,
    hom₂ := τ.right,
    hom₃ := t,
    comm₁' := τ.w.symm,
    comm₂' := ht₁,
    comm₃' := ht₂, },
  haveI : is_iso (L.map_triangle.map φ),
  { haveI : is_iso (L.map_triangle.map φ).hom₁ := localization.inverts L W _ w₁,
    haveI : is_iso (L.map_triangle.map φ).hom₂ := localization.inverts L W _ w₂,
    exact pretriangulated.triangle.is_iso_of_is_iso_homs _
      infer_instance infer_instance (pretriangulated.is_iso_hom₃_of_distinguished _
        (L.map_distinguished _ hT') (L.map_distinguished _ hT'')), },
  let ψ := (map_triangle_nat_trans (F.right_derived_functor_α L W)).app (pretriangulated.triangle.mk g.hom γ γ'),
  haveI : is_iso ψ := pretriangulated.triangle.is_iso_of_is_iso_homs _ hg₁ hg₂
      (@triangulated.is_triangulated_subcategory.ext₃ _ _ _ _ _ _ _ _ hF' _ hT'' ⟨hg₁⟩ ⟨hg₂⟩).some,
  exact pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ hT'') _
    ((F.right_derived_functor L W).map_triangle.map_iso (e.symm ≪≫ as_iso (L.map_triangle.map φ)) ≪≫
    (map_triangle_comp L (F.right_derived_functor L W)).symm.app _ ≪≫ (as_iso ψ).symm),
end⟩

end functor

end category_theory
