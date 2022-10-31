import for_mathlib.category_theory.triangulated.yoneda
import for_mathlib.category_theory.triangulated.triangles

noncomputable theory

namespace category_theory

open limits category preadditive triangulated
open_locale zero_object

variables {C : Type*} [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

namespace triangulated

section

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk C u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

include comm h₁₂ h₂₃ h₁₃

def octahedron_exists : Prop :=
∃ (m₁ : Z₁₂ ⟶ Z₁₃) (m₃ : Z₁₃ ⟶ Z₂₃) (comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃)
    (comm₂ : w₁₂ = m₁ ≫ w₁₃) (comm₃ : v₁₃ ≫ m₃ = v₂₃) (comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃),
    triangle.mk C m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ dist_triang C

namespace octahedron_exists

variables {comm h₁₂ h₂₃ h₁₃} (h : octahedron_exists comm h₁₂ h₂₃ h₁₃)

def m₁ : Z₁₂ ⟶ Z₁₃ := h.some
def m₃ : Z₁₃ ⟶ Z₂₃ := h.some_spec.some

@[simps]
def triangle : triangle C :=
triangle.mk C h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')

lemma triangle_distinguished : h.triangle ∈ dist_triang C :=
h.some_spec.some_spec.some_spec.some_spec.some_spec.some_spec

@[simps]
def triangle_morphism₁ : triangle.mk C u₁₂ v₁₂ w₁₂ ⟶ triangle.mk C u₁₃ v₁₃ w₁₃ :=
{ hom₁ := 𝟙 X₁,
  hom₂ := u₂₃,
  hom₃ := h.m₁,
  comm₁' := by { dsimp, rw [id_comp, comm], },
  comm₂' := h.some_spec.some_spec.some,
  comm₃' := begin
    dsimp,
    simpa only [functor.map_id, comp_id]
      using h.some_spec.some_spec.some_spec.some,
  end }

@[simps]
def triangle_morphism₂ : triangle.mk C u₁₃ v₁₃ w₁₃ ⟶ triangle.mk C u₂₃ v₂₃ w₂₃ :=
{ hom₁ := u₁₂,
  hom₂ := 𝟙 X₃,
  hom₃ := h.m₃,
  comm₁' := by { dsimp, rw [comp_id, comm], },
  comm₂' := begin
    dsimp,
    simpa only [id_comp] using
      h.some_spec.some_spec.some_spec.some_spec.some,
  end,
  comm₃' := h.some_spec.some_spec.some_spec.some_spec.some_spec.some, }

variables (u₁₂ u₂₃ u₁₃ comm)

lemma mk {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' : C} (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃')
  (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂')(e₃ : X₃ ≅ X₃')
  (comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂') (comm₂₃ : u₂₃ ≫ e₃.hom = e₂.hom ≫ u₂₃')
  (v₁₂' : X₂' ⟶ Z₁₂') (w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : ℤ)⟧)
  (h₁₂' : triangle.mk C u₁₂' v₁₂' w₁₂' ∈ dist_triang C)
  (v₂₃' : X₃' ⟶ Z₂₃') (w₂₃' : Z₂₃' ⟶ X₂'⟦(1 : ℤ)⟧)
  (h₂₃' : triangle.mk C u₂₃' v₂₃' w₂₃' ∈ dist_triang C)
  (v₁₃' : X₃' ⟶ Z₁₃') (w₁₃' : Z₁₃' ⟶ X₁'⟦(1 : ℤ)⟧)
  (h₁₃' : triangle.mk C (u₁₂' ≫ u₂₃') v₁₃' w₁₃' ∈ dist_triang C)
  (H : octahedron_exists rfl h₁₂' h₂₃' h₁₃') : octahedron_exists comm h₁₂ h₂₃ h₁₃ :=
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
  { refine pretriangulated.isomorphic_distinguished _ H.triangle_distinguished _ _,
    refine triangle.mk_iso _ _ iso₁₂.triangle_eval₃ iso₁₃.triangle_eval₃ iso₂₃.triangle_eval₃
      _ _ _ ,
    { dsimp, erw [assoc, assoc, iso.triangle_inv_hom_id₃, comp_id], },
    { dsimp, erw [assoc, assoc, iso.triangle_inv_hom_id₃, comp_id], },
    { dsimp, erw [assoc, ← functor.map_comp, eq₁₂, functor.map_comp, reassoc_of eq₂₃'], }, },
end

end octahedron_exists

end

end triangulated

variable (C)

class triangulated :=
(octahedron' : ∀ ⦃X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C⦄ ⦃u₁₂ : X₁ ⟶ X₂⦄ ⦃u₂₃ : X₂ ⟶ X₃⦄ ⦃u₁₃ : X₁ ⟶ X₃⦄
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  ⦃v₁₂ : X₂ ⟶ Z₁₂⦄ ⦃w₁₂ : Z₁₂ ⟶ X₁⟦1⟧⦄ (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  ⦃v₂₃ : X₃ ⟶ Z₂₃⦄ ⦃w₂₃ : Z₂₃ ⟶ X₂⟦1⟧⦄ (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  ⦃v₁₃ : X₃ ⟶ Z₁₃⦄ ⦃w₁₃ : Z₁₃ ⟶ X₁⟦1⟧⦄ (h₁₃ : triangle.mk C u₁₃ v₁₃ w₁₃ ∈ dist_triang C),
  triangulated.octahedron_exists comm h₁₂ h₂₃ h₁₃)

variable {C}

namespace triangulated

lemma mk' (h : ∀ ⦃X₁' X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃'),
  ∃ (X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C) (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) (e₁ : X₁' ≅ X₁) (e₂ : X₂' ≅ X₂)
    (e₃ : X₃' ≅ X₃) (comm₁₂ : u₁₂' ≫ e₂.hom = e₁.hom ≫ u₁₂)
    (comm₂₃ : u₂₃' ≫ e₃.hom = e₂.hom ≫ u₂₃)
    (v₁₂ : X₂ ⟶ Z₁₂) (w₁₂ : Z₁₂ ⟶ X₁⟦1⟧) (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
    (v₂₃ : X₃ ⟶ Z₂₃) (w₂₃ : Z₂₃ ⟶ X₂⟦1⟧) (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
    (v₁₃ : X₃ ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ X₁⟦1⟧)
      (h₁₃ : triangle.mk C (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ dist_triang C),
      octahedron_exists rfl h₁₂ h₂₃ h₁₃) : triangulated C :=
⟨λ X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' u₁₂' u₂₃' u₁₃' comm' v₁₂' w₁₂' h₁₂' v₂₃' w₂₃' h₂₃'
  v₁₃' w₁₃' h₁₃', begin
  obtain ⟨X₁, X₂, X₃, Z₁₂, Z₂₃, Z₁₃, u₁₂, u₂₃, e₁, e₂, e₃, comm₁₂, comm₂₃,
    v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, H⟩ := h u₁₂' u₂₃',
  exact octahedron_exists.mk _ _ _ _ u₁₂ u₂₃ e₁ e₂ e₃ comm₁₂ comm₂₃ v₁₂ w₁₂ h₁₂
    v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃ H,
end⟩

variable [triangulated C]

restate_axiom octahedron'

namespace octahedron

variables {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : triangle.mk C u₁₂ v₁₂ w₁₂ ∈ dist_triang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : triangle.mk C u₂₃ v₂₃ w₂₃ ∈ dist_triang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : triangle.mk C u₁₃ v₁₃ w₁₃ ∈ dist_triang C)

include comm h₁₂ h₂₃ h₁₃

def m₁ : Z₁₂ ⟶ Z₁₃ := (octahedron comm h₁₂ h₂₃ h₁₃).m₁
def m₃ : Z₁₃ ⟶ Z₂₃ := (octahedron comm h₁₂ h₂₃ h₁₃).m₃

@[simps]
def triangle : triangle C := (octahedron comm h₁₂ h₂₃ h₁₃).triangle

lemma triangle_distinguished : triangle comm h₁₂ h₂₃ h₁₃ ∈ dist_triang C :=
(octahedron comm h₁₂ h₂₃ h₁₃).triangle_distinguished

@[simps]
def triangle_morphism₁ : triangle.mk C u₁₂ v₁₂ w₁₂ ⟶ triangle.mk C u₁₃ v₁₃ w₁₃ :=
(octahedron comm h₁₂ h₂₃ h₁₃).triangle_morphism₁

@[simps]
def triangle_morphism₂ : triangle.mk C u₁₃ v₁₃ w₁₃ ⟶ triangle.mk C u₂₃ v₂₃ w₂₃ :=
(octahedron comm h₁₂ h₂₃ h₁₃).triangle_morphism₂

end octahedron

end triangulated

end category_theory
