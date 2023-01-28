import for_mathlib.category_theory.triangulated.homological_functor
import category_theory.preadditive.yoneda
import algebra.category.Group.abelian
import for_mathlib.algebra.homology.short_complex.AddCommGroup
import for_mathlib.category_theory.triangulated.triangulated_op

open category_theory category_theory.category category_theory.limits

variables {C : Type*} [category C] [preadditive C]
  [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

namespace category_theory

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

local attribute [instance] has_shift_op_neg_ℤ

instance preadditive_yoneda_is_homological (X : C) :
  (preadditive_yoneda.obj X).is_homological :=
functor.is_homological.of_unop _ (λ T hT, begin
  rw short_complex.AddCommGroup_exact_iff,
  intros x₂ hx₂,
  dsimp at x₂ hx₂ ⊢,
  obtain ⟨x₃, hx₃⟩ := contravariant_yoneda_exact₂ T hT x₂ hx₂,
  exact ⟨x₃, hx₃.symm⟩,
end)

end pretriangulated

end category_theory
