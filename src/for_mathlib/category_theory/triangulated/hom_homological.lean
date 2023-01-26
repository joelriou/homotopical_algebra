import for_mathlib.category_theory.triangulated.homological_functor
import category_theory.preadditive.yoneda
import algebra.category.Group.abelian

open category_theory category_theory.category category_theory.limits

universe u

variables {C : Type*} [category C] [preadditive C]
  [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

namespace category_theory

namespace short_complex

lemma AddCommGroup_exact_iff (S : short_complex AddCommGroup.{u}) :
  S.exact ↔
  ∀ (x₂ : S.X₂) (hx₂ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := sorry

end short_complex

namespace pretriangulated

instance preadditive_coyoneda_is_homological (X : Cᵒᵖ) :
  (preadditive_coyoneda.obj X).is_homological :=
⟨λ T hT, begin
  rw short_complex.AddCommGroup_exact_iff,
  intros x₂ hx₂,
  dsimp at x₂ hx₂ ⊢,
  obtain ⟨x₁, hx₁⟩ := covariant_yoneda_exact₂ T hT x₂ hx₂,
  exact ⟨x₁, hx₁.symm⟩,
end⟩

end pretriangulated

end category_theory
