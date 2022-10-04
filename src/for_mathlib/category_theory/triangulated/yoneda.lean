import category_theory.preadditive.yoneda
import category_theory.triangulated.pretriangulated
import for_mathlib.algebra.homology.basic_five_lemma
import for_mathlib.category_theory.triangulated.pretriangulated_misc

namespace category_theory

open limits

lemma is_iso_of_yoneda_bijective {C : Type*} [category C] {X Y : C} (f : X ⟶ Y)
  (hf : ∀ (A : C), function.bijective (λ (x : A ⟶ X), x ≫ f)) : is_iso f :=
begin
  haveI : ∀ (A : Cᵒᵖ), is_iso ((yoneda.map f).app A),
  { intro A,
    induction A using opposite.rec,
    rw is_iso_iff_bijective,
    exact hf A, },
  haveI : is_iso (yoneda.map f) := nat_iso.is_iso_of_is_iso_app _,
  exact yoneda.is_iso f,
end

lemma yoneda_bijective_of_is_iso {C : Type*} [category C] {X Y : C} (f : X ⟶ Y) [is_iso f]
  (A : C) : function.bijective (λ (x : A ⟶ X), x ≫ f) :=
begin
  have h : is_iso ((yoneda.map f).app (opposite.op A)) := infer_instance,
  simpa only [is_iso_iff_bijective] using h,
end

namespace triangulated

open algebra.homology

variables {C : Type*} [category C] [preadditive C] [has_shift C ℤ] [has_zero_object C]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

structure triangle.comp_eq_zero (T : triangle C) : Prop :=
(zero₁₂ : T.mor₁ ≫ T.mor₂ = 0)
(zero₂₃ : T.mor₂ ≫ T.mor₃ = 0)
(zero₃₁ : T.mor₃ ≫ T.mor₁⟦1⟧' = 0)

lemma triangle.comp_eq_zero.of_distinguished (T : triangle C) (hT : T ∈ dist_triang C) :
  T.comp_eq_zero :=
begin
  constructor,
  exact pretriangulated.comp_dist_triangle_mor_zero₁₂ _ T hT,
  exact pretriangulated.comp_dist_triangle_mor_zero₂₃ _ T hT,
  exact pretriangulated.comp_dist_triangle_mor_zero₃₁ _ T hT,
end

variable (C)

@[derive category]
def candidate_triangle := full_subcategory (λ (T : triangle C), T.comp_eq_zero)

variable {C}

def candidate_triangle.of_distinguished (T : triangle C) (hT : T ∈ dist_triang C) :
  candidate_triangle C := ⟨T, triangle.comp_eq_zero.of_distinguished T hT⟩

variable (C)
def candidate_triangle.to_five_complex : candidate_triangle C ⥤ five_complex C :=
{ obj := λ T,
  { X₁ := T.1.obj₁,
    X₂ := T.1.obj₂,
    X₃ := T.1.obj₃,
    X₄ := T.1.obj₁⟦(1 : ℤ)⟧,
    X₅ := T.1.obj₂⟦(1 : ℤ)⟧,
    f₁ := T.1.mor₁,
    f₂ := T.1.mor₂,
    f₃ := T.1.mor₃,
    f₄ := T.1.mor₁⟦1⟧',
    h₁₂ := T.2.zero₁₂,
    h₂₃ := T.2.zero₂₃,
    h₃₄ := T.2.zero₃₁, },
  map := λ T T' φ,
  { τ₁ := φ.hom₁,
    τ₂ := φ.hom₂,
    τ₃ := φ.hom₃,
    τ₄ := φ.hom₁⟦1⟧',
    τ₅ := φ.hom₂⟦1⟧',
    comm₁ := φ.comm₁,
    comm₂ := φ.comm₂,
    comm₃ := φ.comm₃,
    comm₄ := by { dsimp, simp only [← functor.map_comp, φ.comm₁], }, },
  map_id' := λ T, by { ext; try { refl, }; apply functor.map_id, },
  map_comp' := λ T T' T'' φ ψ, by { ext; try { refl, }; apply functor.map_comp, }, }

lemma candidate_triangle.coyoneda_exact_of_distinguished (T : triangle C) (hT : T ∈ dist_triang C)
  (A : C) : five_complex.exact (((candidate_triangle.to_five_complex C) ⋙ (preadditive_coyoneda.obj (opposite.op A)).map_five_complex).obj (candidate_triangle.of_distinguished T hT)) :=
{ ex₂ := λ x₂ hx₂, ⟨_, (covariant_yoneda_exact₂ T hT x₂ hx₂).some_spec.symm⟩,
  ex₃ := λ x₃ hx₃, ⟨_, (covariant_yoneda_exact₃ T hT x₃ hx₃).some_spec.symm⟩,
  ex₄ := λ x₁ hx₁, ⟨_, (covariant_yoneda_exact₁ T hT x₁ hx₁).some_spec.symm⟩, }

end triangulated

end category_theory
