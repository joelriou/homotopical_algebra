import for_mathlib.algebra.homology.mapping_cone
import algebra.homology.additive
import for_mathlib.category_theory.triangulated.pretriangulated_misc

open category_theory category_theory.pretriangulated category_theory.triangulated
  category_theory.limits

noncomputable theory

section

variables {C ι : Type*} [category C] [preadditive C] {c : complex_shape ι}

def homotopy_category.lift {K L : homological_complex C c}
  (φ : (homotopy_category.quotient _ _).obj K ⟶ (homotopy_category.quotient _ _).obj L) :
  K ⟶ L := quot.out φ

instance [has_zero_object C] : has_zero_object (homotopy_category C c) :=
by { change has_zero_object (category_theory.quotient _), apply_instance, }

instance : preadditive (homotopy_category C c) :=
begin
  apply quotient.preadditive,
  { rintros X Y f₁ g₁ f₂ g₂ ⟨h₁⟩ ⟨h₂⟩,
    refine ⟨homotopy.add h₁ h₂⟩, },
  { rintros X Y f g ⟨h⟩,
    exact ⟨homotopy.equiv_sub_zero.symm
      (by simpa only [neg_sub_neg] using homotopy.equiv_sub_zero h.symm)⟩, },
end

instance homotopy_category.quotient_additive :
  (homotopy_category.quotient C c).additive := quotient.functor_additive _ _ _

lemma is_zero_of_homotopy_id_zero [has_zero_object C] (X : homological_complex C c)
  (h : homotopy (𝟙 X) 0) :
  is_zero ((homotopy_category.quotient C c).obj X) :=
begin
  have eq := homotopy_category.eq_of_homotopy _ _ h,
  simp only [category_theory.functor.map_id] at eq,
  simp only [is_zero.iff_id_eq_zero, eq, functor.map_zero],
end

end

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]
  [has_binary_biproducts C]
  {K L : cochain_complex C ℤ} (φ : K ⟶ L)

namespace cochain_complex


@[simps mor₁ mor₂ mor₃]
def mapping_cone_triangle : triangle (cochain_complex C ℤ) :=
triangle.mk φ (ι_mapping_cone φ) (mapping_cone_δ φ)

end cochain_complex

open cochain_complex

namespace homotopy_category

def mapping_cone_triangle' : triangle (homotopy_category C (complex_shape.up ℤ)) :=
triangle.mk ((homotopy_category.quotient _ _).map φ) (ι_mapping_cone' φ) (mapping_cone_δ' φ)

variable (C)

def distinguished_triangles : set (triangle (homotopy_category C (complex_shape.up ℤ))) :=
λ T, ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L),
  nonempty (T ≅ mapping_cone_triangle' φ)

variable {C}

lemma mapping_cone_triangle'_distinguished :
  mapping_cone_triangle' φ ∈ distinguished_triangles C :=
⟨_, _, φ, nonempty.intro (iso.refl _)⟩

instance shift_functor_additive (n : ℤ) :
  (shift_functor (homotopy_category C (complex_shape.up ℤ)) n).additive := sorry

lemma isomorphic_distinguished
  (T₁ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (h₁ : T₁ ∈ distinguished_triangles C)
  (T₂ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (e : T₂ ≅ T₁) : T₂ ∈ distinguished_triangles C :=
begin
  obtain ⟨K, L, φ, ⟨e'⟩⟩ := h₁,
  exact ⟨K, L, φ, ⟨e ≪≫ e'⟩⟩,
end

lemma contractible_distinguished
  (X : homotopy_category C (complex_shape.up ℤ)) :
  contractible_triangle X ∈ distinguished_triangles C :=
begin
  cases X,
  refine ⟨_, _, 𝟙 X, ⟨_⟩⟩,
  have h : is_zero ((homotopy_category.quotient _ _).obj (mapping_cone (𝟙 X))),
  { refine is_zero_of_homotopy_id_zero _ _,
    equiv_rw hom_complex.equiv_homotopy _ _,
    refine ⟨_, sorry⟩,
    sorry, },
  exact triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (is_zero.iso_zero h).symm
    (by tidy) (is_zero.eq_of_tgt h _ _) (by simp only [is_zero.eq_of_src h
      ((mapping_cone_triangle' (𝟙 X)).mor₃) 0, contractible_triangle_mor₃, zero_comp, comp_zero]),
end

lemma distinguished_cocone_triangle
  (X Y : homotopy_category C (complex_shape.up ℤ)) (f : X ⟶ Y) :
  ∃ (Z : homotopy_category C (complex_shape.up ℤ)) (g : Y ⟶ Z)
    (h : Z ⟶ X⟦(1 : ℤ)⟧), triangle.mk f g h ∈ distinguished_triangles C :=
begin
  cases X,
  cases Y,
  obtain ⟨φ, rfl⟩ := quotient.functor_map_surjective _ _ f,
  exact ⟨_ ,_ ,_ , mapping_cone_triangle'_distinguished φ⟩,
end

lemma complete_distinguished_triangle_morphism'
  {K₁ L₁ K₂ L₂ : cochain_complex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (hab : homotopy (φ₁ ≫ b) (a ≫ φ₂)) :
  ∃ (c : mapping_cone φ₁ ⟶ mapping_cone φ₂),
    nonempty (homotopy (ι_mapping_cone φ₁ ≫ c) (b ≫ ι_mapping_cone φ₂)) ∧
      nonempty (homotopy (mapping_cone_δ φ₁ ≫ a⟦1⟧') (c ≫ mapping_cone_δ φ₂)) := sorry

lemma complete_distinguished_triangle_morphism
  (T₁ T₂ : triangle (homotopy_category C (complex_shape.up ℤ)))
  (h₁ : T₁ ∈ distinguished_triangles C) (h₂ : T₂ ∈ distinguished_triangles C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
  (comm₁ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
    T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ :=
begin
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := h₁,
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := h₂,
  obtain ⟨c, ⟨h₁⟩, ⟨h₂⟩⟩ := complete_distinguished_triangle_morphism' φ₁ φ₂
    (quot.out (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)) (quot.out (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂))
    (homotopy_of_eq _ _ begin
      simp only [functor.map_comp, quotient_map_out, category.assoc],
      erw [reassoc_of e₁.inv.comm₁, reassoc_of comm₁, e₂.hom.comm₁],
      refl,
    end),
  replace h₁ := eq_of_homotopy _ _ h₁,
  replace h₂ := eq_of_homotopy _ _ h₂,
  refine ⟨e₁.hom.hom₃ ≫ (homotopy_category.quotient _ _).map c ≫ e₂.inv.hom₃, _, _⟩,
  { simp only [functor.map_comp, quotient_map_out, category.assoc] at h₁,
    erw [reassoc_of e₁.hom.comm₂, reassoc_of h₁, e₂.inv.comm₂],
    simp only [triangle.hom_inv_id_hom₂_assoc], },
  { erw [functor.map_comp, quotient_map_shift] at h₂,
    simp only [quotient_map_out, functor.map_comp] at h₂,
    simp only [category.assoc, ← e₂.inv.comm₃],
    erw [← reassoc_of h₂, ← reassoc_of e₁.hom.comm₃],
    simp only [← functor.map_comp, triangle.hom_inv_id_hom₁, category.comp_id,
      triangle.hom_inv_id_hom₁_assoc], },
end

instance : pretriangulated (homotopy_category C (complex_shape.up ℤ)) :=
{ distinguished_triangles := distinguished_triangles C,
  isomorphic_distinguished := isomorphic_distinguished,
  contractible_distinguished := contractible_distinguished,
  distinguished_cocone_triangle := distinguished_cocone_triangle,
  rotate_distinguished_triangle := sorry,
  complete_distinguished_triangle_morphism :=
    complete_distinguished_triangle_morphism, }

end homotopy_category
