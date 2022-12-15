import for_mathlib.category_theory.triangulated.yoneda
import for_mathlib.category_theory.triangulated.triangles
import category_theory.triangulated.triangulated

noncomputable theory

namespace category_theory

open limits category preadditive triangulated
open_locale zero_object

variables {C : Type*} [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

namespace triangulated

open pretriangulated

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) (u₁₃ : X₁ ⟶ X₃)
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

lemma octahedron.of_iso {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' : C} (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃')
  (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂')(e₃ : X₃ ≅ X₃')
  (comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂') (comm₂₃ : u₂₃ ≫ e₃.hom = e₂.hom ≫ u₂₃')
  (v₁₂' : X₂' ⟶ Z₁₂') (w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : ℤ)⟧)
  (h₁₂' : triangle.mk u₁₂' v₁₂' w₁₂' ∈ dist_triang C)
  (v₂₃' : X₃' ⟶ Z₂₃') (w₂₃' : Z₂₃' ⟶ X₂'⟦(1 : ℤ)⟧)
  (h₂₃' : triangle.mk u₂₃' v₂₃' w₂₃' ∈ dist_triang C)
  (v₁₃' : X₃' ⟶ Z₁₃') (w₁₃' : Z₁₃' ⟶ X₁'⟦(1 : ℤ)⟧)
  (h₁₃' : triangle.mk (u₁₂' ≫ u₂₃') v₁₃' w₁₃' ∈ dist_triang C)
  (H : octahedron rfl h₁₂' h₂₃' h₁₃') : octahedron comm h₁₂ h₂₃ h₁₃ :=
begin
  let iso₁₂ := iso_triangle_of_distinguished_of_is_iso₁₂ _ _ h₁₂ h₁₂' e₁ e₂ comm₁₂,
  let iso₂₃ := iso_triangle_of_distinguished_of_is_iso₁₂ _ _ h₂₃ h₂₃' e₂ e₃ comm₂₃,
  let iso₁₃ := iso_triangle_of_distinguished_of_is_iso₁₂ _ _ h₁₃ h₁₃' e₁ e₃
    (by { dsimp, simp only [← comm, assoc, comm₂₃, reassoc_of comm₁₂], }),
  have eq₁₂ := iso₁₂.hom.comm₂,
  have eq₁₂' := iso₁₂.hom.comm₃,
  have eq₁₃ := iso₁₃.hom.comm₂,
  have eq₁₃' := iso₁₃.hom.comm₃,
  have eq₂₃ := iso₂₃.hom.comm₂,
  have eq₂₃' := iso₂₃.hom.comm₃,
  have rel₁₂ := H.triangle_morphism₁.comm₂,
  have rel₁₃ := H.triangle_morphism₁.comm₃,
  have rel₂₂ := H.triangle_morphism₂.comm₂,
  have rel₂₃ := H.triangle_morphism₂.comm₃,
  dsimp at eq₁₂ eq₁₂' eq₁₃ eq₁₃' eq₂₃ eq₂₃' rel₁₂ rel₁₃ rel₂₂ rel₂₃,
  rw [functor.map_id, comp_id] at rel₁₃,
  rw id_comp at rel₂₂,
  refine ⟨iso₁₂.hom.hom₃ ≫ H.m₁ ≫ iso₁₃.inv.hom₃,
    iso₁₃.hom.hom₃ ≫ H.m₃ ≫ iso₂₃.inv.hom₃, _, _, _, _, _⟩,
  { simp only [reassoc_of eq₁₂, ← cancel_mono iso₁₃.hom.hom₃, assoc,
      iso₁₃.triangle_inv_hom_id₃, eq₁₃, reassoc_of comm₂₃, ← rel₁₂],
    dsimp,
    rw comp_id, },
  { rw [← cancel_mono ((shift_functor C (1 : ℤ)).map e₁.hom), eq₁₂', assoc, assoc, assoc, eq₁₃',
      iso₁₃.triangle_inv_hom_id₃_assoc, ← rel₁₃], },
  { rw [reassoc_of eq₁₃, reassoc_of rel₂₂, ← cancel_mono iso₂₃.hom.hom₃, assoc, assoc,
      iso₂₃.triangle_inv_hom_id₃, eq₂₃],
    dsimp,
    rw comp_id, },
  { rw [← cancel_mono ((shift_functor C (1 : ℤ)).map e₂.hom), assoc, assoc, assoc, assoc, eq₂₃',
      iso₂₃.triangle_inv_hom_id₃_assoc, ← rel₂₃, ← functor.map_comp, comm₁₂, functor.map_comp,
      reassoc_of eq₁₃'], },
  { refine pretriangulated.isomorphic_distinguished _ H.mem _ _,
    refine triangle.mk_iso _ _ iso₁₂.triangle_eval₃ iso₁₃.triangle_eval₃ iso₂₃.triangle_eval₃
      _ _ _ ,
    { dsimp, erw [assoc, assoc, iso.triangle_inv_hom_id₃, comp_id], },
    { dsimp, erw [assoc, assoc, iso.triangle_inv_hom_id₃, comp_id], },
    { dsimp, erw [assoc, ← functor.map_comp, eq₁₂, functor.map_comp, reassoc_of eq₂₃'], }, },
end


end triangulated

open pretriangulated triangulated

lemma is_triangulated.mk' (h : ∀ ⦃X₁' X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃'),
  ∃ (X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C) (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) (e₁ : X₁' ≅ X₁) (e₂ : X₂' ≅ X₂)
    (e₃ : X₃' ≅ X₃) (comm₁₂ : u₁₂' ≫ e₂.hom = e₁.hom ≫ u₁₂)
    (comm₂₃ : u₂₃' ≫ e₃.hom = e₂.hom ≫ u₂₃)
    (v₁₂ : X₂ ⟶ Z₁₂) (w₁₂ : Z₁₂ ⟶ X₁⟦1⟧) (h₁₂ : triangle.mk u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
    (v₂₃ : X₃ ⟶ Z₂₃) (w₂₃ : Z₂₃ ⟶ X₂⟦1⟧) (h₂₃ : triangle.mk u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
    (v₁₃ : X₃ ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ X₁⟦1⟧)
      (h₁₃ : triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ dist_triang C),
        nonempty (octahedron rfl h₁₂ h₂₃ h₁₃)) : is_triangulated C :=
⟨λ X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' u₁₂' u₂₃' u₁₃' comm' v₁₂' w₁₂' h₁₂' v₂₃' w₂₃' h₂₃'
  v₁₃' w₁₃' h₁₃', begin
  obtain ⟨X₁, X₂, X₃, Z₁₂, Z₂₃, Z₁₃, u₁₂, u₂₃, e₁, e₂, e₃, comm₁₂, comm₂₃,
    v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, H⟩ := h u₁₂' u₂₃',
  exact ⟨octahedron.of_iso _ _ _ _ _ _ _ u₁₂ u₂₃ e₁ e₂ e₃ comm₁₂ comm₂₃ v₁₂ w₁₂ h₁₂
    v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃ H.some⟩
end⟩

end category_theory
