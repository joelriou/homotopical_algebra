import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.algebra.homology.pretriangulated

open category_theory category_theory.pretriangulated category_theory.triangulated
  category_theory.limits category_theory.category

noncomputable theory

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]
  [has_binary_biproducts C]

namespace cochain_complex

variables {X₁ X₂ X₃ : cochain_complex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

@[simps mor₁ mor₂ mor₃]
def mapping_cone_comp_triangle {X₁ X₂ X₃ : cochain_complex C ℤ}
  (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) : triangle (cochain_complex C ℤ) :=
triangle.mk (mapping_cone_map f (f ≫ g) (𝟙 X₁) g (by rw id_comp))
  (mapping_cone_map (f ≫ g) g f (𝟙 X₃) (by rw comp_id))
    (mapping_cone_δ g ≫ (ι_mapping_cone f)⟦1⟧')

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
  sorry,
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
  refine pretriangulated.isomorphic_distinguished _
    (mapping_cone_comp_triangle_distinguished u₁₂ u₂₃) _
    (triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _),
  { dsimp,
    erw [comp_id, id_comp], },
end)

end homotopy_category
