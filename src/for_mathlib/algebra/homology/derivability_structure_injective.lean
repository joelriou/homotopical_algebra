import for_mathlib.algebra.homology.derived_category_plus
import for_mathlib.algebra.homology.k_injective
import category_theory.preadditive.injective

noncomputable theory

open category_theory category_theory.category
open_locale zero_object

variables {C ι : Type*} [category C] [abelian C] {c : complex_shape ι}

namespace homological_complex

class is_termwise_injective (K : homological_complex C c) : Prop :=
(X_injective [] : ∀ (n : ι), injective (K.X n))

instance zero_is_termwise_injective :
  (0 : homological_complex C c).is_termwise_injective :=
⟨λ n, injective.of_iso (homological_complex.eval C c n).map_zero_object.symm
  infer_instance⟩

end homological_complex

namespace cochain_complex

@[simp]
lemma shift_is_termwise_injective_iff
  (K : cochain_complex C ℤ) (n : ℤ) :
  homological_complex.is_termwise_injective (K⟦n⟧) ↔
  homological_complex.is_termwise_injective K :=
begin
  split,
  { introI,
    refine ⟨λ i, _⟩,
    obtain ⟨m, rfl⟩ : ∃ (m : ℤ), i = m+n := ⟨i-n, by simp⟩,
    have h := homological_complex.is_termwise_injective.X_injective (K⟦n⟧) m,
    exact h, },
  { introI,
    refine ⟨λ i, _⟩,
    apply homological_complex.is_termwise_injective.X_injective K _, },
end

end cochain_complex

namespace homotopy_category

namespace plus


variables (C)

abbreviation termwise_injective :=
  full_subcategory (λ (K : homotopy_category.plus C), K.obj.as.is_termwise_injective)

variable {C}

abbreviation termwise_injective.ι : termwise_injective C ⥤ homotopy_category.plus C :=
full_subcategory_inclusion _

instance is_termwise_injective_is_triangulated_subcategory' :
  triangulated.is_triangulated_subcategory'
    (λ (K : homotopy_category.plus C), K.obj.as.is_termwise_injective) :=
{ zero := begin
    refine ⟨⟨⟨0⟩, ⟨0, infer_instance⟩⟩, _, homological_complex.zero_is_termwise_injective⟩,
    rw limits.is_zero.iff_id_eq_zero,
    change (homotopy_category.quotient C (complex_shape.up ℤ)).map (𝟙 0) = 0,
    simp only [limits.id_zero, functor.map_zero],
  end,
  shift := begin
    rintro ⟨⟨K⟩, hK⟩ n h,
    change K⟦n⟧.is_termwise_injective,
    simpa only [cochain_complex.shift_is_termwise_injective_iff] using h,
  end,
  distinguished_cocone_triangle' := sorry, }

instance test : (termwise_injective.ι : _ ⥤ homotopy_category.plus C).is_triangulated := infer_instance

end plus

end homotopy_category
