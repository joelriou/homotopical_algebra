/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homological_complex
import for_mathlib.algebra.homology.homological_complex_biprod
import for_mathlib.algebra.homology.trunc_le

open category_theory
open category_theory.category

variables {C : Type*} [category C]

namespace category_theory

namespace limits

lemma is_zero.iff_of_biprod [preadditive C] (A B : C) [has_binary_biproduct A B] :
  is_zero (A ⊞ B) ↔ is_zero A ∧ is_zero B :=
begin
  simp only [is_zero.iff_id_eq_zero],
  split,
  { intro h,
    split,
    { suffices : 𝟙 A = biprod.inl ≫ (𝟙 (A ⊞ B)) ≫ biprod.fst,
      { rw [this, h, zero_comp, comp_zero], },
      rw [id_comp, biprod.inl_fst], },
    { suffices : 𝟙 B = biprod.inr ≫ (𝟙 (A ⊞ B)) ≫ biprod.snd,
      { rw [this, h, zero_comp, comp_zero], },
      rw [id_comp, biprod.inr_snd], }, },
  { intro h,
    ext,
    { simpa only [comp_id, biprod.inl_fst, comp_zero, zero_comp] using h.left, },
    { simp only [comp_id, biprod.inl_snd, comp_zero, zero_comp], },
    { simp only [comp_id, biprod.inr_fst, comp_zero, zero_comp], },
    { simpa only [comp_id, biprod.inr_snd, comp_zero, zero_comp] using h.right, } },
end

end limits

end category_theory

open category_theory.limits

namespace cochain_complex

def is_bounded_above [has_zero_morphisms C] (K : cochain_complex C ℤ) : Prop :=
∃ (r : ℤ), ∀ (i : ℤ) (hi : r < i), is_zero (K.X i)

namespace is_bounded_above

lemma of_biprod [preadditive C] (K L : cochain_complex C ℤ)
  (hK : K.is_bounded_above) (hL : L.is_bounded_above)
  [∀ i, has_binary_biproduct (K.X i) (L.X i)] :
  is_bounded_above (homological_complex.biprod K L) :=
begin
  cases hK with k hk,
  cases hL with l hl,
  use max k l,
  intros i hi,
  dsimp,
  rw is_zero.iff_of_biprod,
  split,
  { apply hk,
    exact lt_of_le_of_lt (le_max_left _ _) hi, },
  { apply hl,
    exact lt_of_le_of_lt (le_max_right _ _) hi, },
end

lemma of_is_strictly_le [abelian C] (K : cochain_complex C ℤ) (n : ℤ)
  [K.is_strictly_le n] : is_bounded_above K :=
⟨n, λ i hi, is_strictly_le.is_zero K n i hi⟩

end is_bounded_above

end cochain_complex
