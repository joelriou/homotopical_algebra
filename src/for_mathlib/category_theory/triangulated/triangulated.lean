import category_theory.triangulated.pretriangulated

noncomputable theory

namespace category_theory

open limits category preadditive triangulated
open_locale zero_object

variables (C : Type*) [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

class triangulated :=
(octahedron' : ∀ ⦃X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C⦄ ⦃u₁₂ : X₁ ⟶ X₂⦄ ⦃u₂₃ : X₂ ⟶ X₃⦄ ⦃u₁₃ : X₁ ⟶ X₃⦄
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  ⦃v₁₂ : X₂ ⟶ Z₁₂⦄ ⦃w₁₂ : Z₁₂ ⟶ X₁⟦1⟧⦄ (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  ⦃v₂₃ : X₃ ⟶ Z₂₃⦄ ⦃w₂₃ : Z₂₃ ⟶ X₂⟦1⟧⦄ (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  ⦃v₁₃ : X₃ ⟶ Z₁₃⦄ ⦃w₁₃ : Z₁₃ ⟶ X₁⟦1⟧⦄ (h₁₃ : triangle.mk C u₁₃ v₁₃ w₁₃ ∈ dist_triang C),
  ∃ (m₁ : Z₁₂ ⟶ Z₁₃) (m₃ : Z₁₃ ⟶ Z₂₃) (comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃)
    (comm₂ : w₁₂ = m₁ ≫ w₁₃) (comm₃ : v₁₃ ≫ m₃ = v₂₃) (comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃),
    triangle.mk C m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ dist_triang C)

variable {C}

namespace triangulated

variable [triangulated C]

restate_axiom octahedron'

namespace octahedron

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk C u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

include comm h₁₂ h₂₃ h₁₃

def m₁ : Z₁₂ ⟶ Z₁₃ := (octahedron comm h₁₂ h₂₃ h₁₃).some
def m₃ : Z₁₃ ⟶ Z₂₃ := (octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some

@[simps]
def triangle : triangle C :=
triangle.mk C (m₁ comm h₁₂ h₂₃ h₁₃) (m₃ comm h₁₂ h₂₃ h₁₃) (w₂₃ ≫ v₁₂⟦1⟧')

lemma triangle_distinguished : triangle comm h₁₂ h₂₃ h₁₃ ∈ dist_triang C :=
(octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some_spec.some_spec.some_spec.some_spec.some_spec

@[simps]
def triangle_morphism₁ : triangle.mk C u₁₂ v₁₂ w₁₂ ⟶ triangle.mk C u₁₃ v₁₃ w₁₃ :=
{ hom₁ := 𝟙 X₁,
  hom₂ := u₂₃,
  hom₃ := m₁ comm h₁₂ h₂₃ h₁₃,
  comm₁' := by { dsimp, rw [id_comp, comm], },
  comm₂' := (octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some_spec.some,
  comm₃' := begin
    dsimp,
    simpa only [functor.map_id, comp_id]
      using (octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some_spec.some_spec.some,
  end }

@[simps]
def triangle_morphism₂ : triangle.mk C u₁₃ v₁₃ w₁₃ ⟶ triangle.mk C u₂₃ v₂₃ w₂₃ :=
{ hom₁ := u₁₂,
  hom₂ := 𝟙 X₃,
  hom₃ := m₃ comm h₁₂ h₂₃ h₁₃,
  comm₁' := by { dsimp, rw [comp_id, comm], },
  comm₂' := begin
    dsimp,
    simpa only [id_comp] using
      (octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some_spec.some_spec.some_spec.some,
  end,
  comm₃' := (octahedron comm h₁₂ h₂₃ h₁₃).some_spec.some_spec.some_spec.some_spec.some_spec.some, }


end octahedron

end triangulated

end category_theory