import for_mathlib.algebra.homology.trunc

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace derived_category

variables {C : Type*} [category C] [abelian C]

instance zero_is_le (n : ℤ) : (0 : derived_category C).is_le n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

instance zero_is_ge (n : ℤ) : (0 : derived_category C).is_ge n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

variable (C)

lemma subcategory.plus : triangulated.subcategory (derived_category C) :=
{ set := λ K, ∃ (n : ℤ), K.is_ge n,
  zero := ⟨0, infer_instance⟩,
  shift := begin
    rintros K k ⟨n, hn⟩,
    haveI := hn,
    exact ⟨n-k, shift_is_ge K n k (n-k) (by linarith)⟩,
  end,
  ext₂ := begin
    rintros T hT ⟨n₁, hn₁⟩ ⟨n₃, hn₃⟩,
    exact ⟨min n₁ n₃,
      ⟨λ n hn, short_complex.exact.is_zero_of_both_zeros (homology_sequence.ex₂ hT n)
        (is_zero.eq_of_src (hn₁.is_zero' _ (lt_of_lt_of_le hn (min_le_left n₁ n₃))) _ _)
        (is_zero.eq_of_tgt (hn₃.is_zero' _ (lt_of_lt_of_le hn (min_le_right n₁ n₃))) _ _)⟩⟩,
  end, }

lemma subcategory.minus : triangulated.subcategory (derived_category C) :=
{ set := λ K, ∃ (n : ℤ), K.is_le n,
  zero := ⟨0, infer_instance⟩,
  shift := begin
    rintros K k ⟨n, hn⟩,
    haveI := hn,
    exact ⟨n-k, shift_is_le K n k (n-k) (by linarith)⟩,
  end,
  ext₂ := begin
    rintros T hT ⟨n₁, hn₁⟩ ⟨n₃, hn₃⟩,
    exact ⟨max n₁ n₃,
      ⟨λ n hn, short_complex.exact.is_zero_of_both_zeros (homology_sequence.ex₂ hT n)
        (is_zero.eq_of_src (hn₁.is_zero' _ (lt_of_le_of_lt (le_max_left n₁ n₃) hn)) _ _)
        (is_zero.eq_of_tgt (hn₃.is_zero' _ (lt_of_le_of_lt (le_max_right n₁ n₃) hn)) _ _)⟩⟩,
  end, }

abbreviation plus := (subcategory.plus C).category

namespace plus

def ι : plus C ⥤ derived_category C :=
(triangulated.subcategory.category_inclusion' _).to_functor

end plus

end derived_category
