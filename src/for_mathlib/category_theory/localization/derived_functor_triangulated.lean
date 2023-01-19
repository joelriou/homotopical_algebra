import for_mathlib.category_theory.localization.derived_functor_shift
import for_mathlib.category_theory.triangulated.is_triangulated_subcategory

open category_theory category_theory.category category_theory.limits

noncomputable theory

namespace category_theory

namespace right_derivability_structure

variables {C₀ C H D : Type*} [category C₀] [category C] [category D] [category H]
  {W₀ : morphism_property C₀} {W : morphism_property C} {Φ : localizor_morphism W₀ W}
  [localizor_morphism.is_localization_equivalence Φ]
  [morphism_property.multiplicative W₀] [morphism_property.multiplicative W]
  (β : right_derivability_structure.basic Φ)
  (F : C ⥤ D) (L : C ⥤ H)
  (hF : W₀.is_inverted_by (Φ.functor ⋙ F))
  [has_shift C₀ ℤ] [has_shift C ℤ] [has_shift H ℤ] [has_shift D ℤ]
  [F.has_comm_shift ℤ] [L.has_comm_shift ℤ] [Φ.functor.has_comm_shift ℤ]
  [preadditive C₀] [preadditive C] [preadditive H] [preadditive D]
  [has_zero_object C₀] [has_zero_object C] [has_zero_object H] [has_zero_object D]
  [∀ (n : ℤ ), (shift_functor C₀ n).additive]
  [∀ (n : ℤ ), (shift_functor C n).additive]
  [∀ (n : ℤ ), (shift_functor H n).additive]
  [∀ (n : ℤ ), (shift_functor D n).additive]
  [L.is_localization W]
  [pretriangulated C₀] [pretriangulated C] [pretriangulated H] [pretriangulated D]
  [functor.ess_surj_on_dist_triang (Φ.functor ⋙ L)]
  [functor.is_triangulated F] [functor.is_triangulated Φ.functor]

namespace basic

include β hF

lemma derived_functor_is_triangulated [F.has_right_derived_functor W] :
  (F.right_derived_functor L W).is_triangulated :=
⟨λ T hT, begin
  obtain ⟨T', hT', ⟨e⟩⟩ := functor.ess_surj_on_dist_triang.condition (Φ.functor ⋙ L) T hT,
  have E' := (functor.map_triangle_comp (Φ.functor ⋙ L) (F.right_derived_functor L W)).symm.app T',
  let τ : Φ.functor ⋙ F ⟶ (Φ.functor ⋙ L) ⋙ F.right_derived_functor L W :=
    whisker_left Φ.functor (F.right_derived_functor_α L W) ≫ (functor.associator _ _ _).inv,
  haveI : ∀ (X₀ : C₀), is_iso (τ.app X₀) := λ X₀, begin
    dsimp [τ],
    rw [comp_id],
    apply β.is_iso_app L F hF,
  end,
  haveI := nat_iso.is_iso_of_is_iso_app τ,
  haveI : (as_iso τ).hom.respects_comm_shift ℤ := by { dsimp [as_iso], apply_instance, },
  exact pretriangulated.isomorphic_distinguished _ (functor.map_distinguished _ _ hT') _
    ((F.right_derived_functor L W).map_triangle.map_iso e.symm ≪≫
    (functor.map_triangle_comp (Φ.functor ⋙ L) (F.right_derived_functor L W)).symm.app T' ≪≫
    (functor.map_triangle_nat_iso (as_iso τ)).symm.app T'),
end⟩

end basic

end right_derivability_structure

end category_theory
