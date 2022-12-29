/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic
import for_mathlib.algebra.homology.homological_complex_limits
import for_mathlib.algebra.homology.trunc
import category_theory.limits.full_subcategory

open category_theory category_theory.limits
open_locale zero_object

namespace category_theory.limits

variables {J C : Type*} [category J] [category C] {F : J ⥤ C} [has_zero_object C]
  [has_zero_morphisms C]

lemma is_zero_of_is_limit_of_is_zero (c : cone F) (hc : is_limit c)
  (hF : ∀ (j : J), is_zero (F.obj j)) : is_zero c.X :=
is_zero.of_iso (is_zero_zero _)
  (is_limit.cone_point_unique_up_to_iso hc
  (is_limit.of_is_zero F (functor.is_zero _ hF) (cone.mk 0 0) (is_zero_zero _)))

lemma is_zero_of_is_colimit_of_is_zero (c : cocone F) (hc : is_colimit c)
  (hF : ∀ (j : J), is_zero (F.obj j)) : is_zero c.X :=
is_zero.of_iso (is_zero_zero _)
  (is_colimit.cocone_point_unique_up_to_iso hc
  (is_colimit.of_is_zero F (functor.is_zero _ hF) (cocone.mk 0 0) (is_zero_zero _)))

end category_theory.limits

open category_theory.limits

variables {C : Type*} [category C] [abelian C]

namespace bounded_above_cochain_complex

namespace limits

variables {J : Type} [small_category J] [fin_category J]

lemma bound_of_finite (K : J → cochain_complex C ℤ) (hK : ∀ (j : J), (K j).is_bounded_above) :
  ∃ (n : ℤ), ∀ (j : J), (K j).is_strictly_le n :=
begin
  let m : J → ℤ := λ j, ((hK j).some),
  have hm : ∀ (j : J), (K j).is_strictly_le (m j),
  { intro j,
    exact ⟨(hK j).some_spec⟩, },
  let μ := finset.max (finset.image m ⊤),
  by_cases μ = ⊥,
  { simp only [finset.max_eq_bot, finset.top_eq_univ, finset.image_eq_empty,
      finset.univ_eq_empty_iff] at h,
    exact ⟨0, λ j, by { exfalso, exact h.false j, }⟩, },
  { obtain ⟨μ', hμ'⟩ := with_bot.ne_bot_iff_exists.1 h,
    refine ⟨μ', λ j, _⟩,
    haveI := hm j,
    refine cochain_complex.is_strictly_le_of_le (K j) (m j) _ _,
    have eq := finset.le_max (finset.mem_image_of_mem m (finset.mem_univ j)),
    change _ ≤ μ at eq,
    simpa only [← hμ', with_bot.coe_le_coe] using eq, },
end

variable (J)

lemma is_bounded_above_is_closed_under_limits_of_shape :
  closed_under_limits_of_shape J (cochain_complex.is_bounded_above : cochain_complex C ℤ → Prop) :=
λ F c hc hF, begin
  obtain ⟨n, hn⟩ := bound_of_finite F.obj hF,
  refine ⟨n, λ i hi, _⟩,
  have hc' := is_limit_of_preserves (homological_complex.eval C (complex_shape.up ℤ) i) hc,
  refine is_zero_of_is_limit_of_is_zero _ hc' (λ j, _),
  haveI := hn j,
  dsimp,
  exact cochain_complex.is_strictly_le.is_zero (F.obj j) n i hi,
end

lemma is_bounded_above_is_closed_under_colimits_of_shape :
  closed_under_colimits_of_shape J (cochain_complex.is_bounded_above : cochain_complex C ℤ → Prop) :=
λ F c hc hF, begin
  obtain ⟨n, hn⟩ := bound_of_finite F.obj hF,
  refine ⟨n, λ i hi, _⟩,
  have hc' := is_colimit_of_preserves (homological_complex.eval C (complex_shape.up ℤ) i) hc,
  refine is_zero_of_is_colimit_of_is_zero _ hc' (λ j, _),
  haveI := hn j,
  dsimp,
  exact cochain_complex.is_strictly_le.is_zero (F.obj j) n i hi,
end

instance : has_finite_limits (bounded_above_cochain_complex C) :=
⟨λ J, begin
  introI,
  introI,
  apply has_limits_of_shape_of_closed_under_limits,
  apply is_bounded_above_is_closed_under_limits_of_shape,
end⟩

instance : has_finite_colimits (bounded_above_cochain_complex C) :=
⟨λ J, begin
  introI,
  introI,
  apply has_colimits_of_shape_of_closed_under_colimits,
  apply is_bounded_above_is_closed_under_colimits_of_shape,
end⟩

end limits

namespace projective_model_structure

variable {C}

lemma CM1 : has_finite_limits (bounded_above_cochain_complex C) ∧
  has_finite_colimits (bounded_above_cochain_complex C) :=
⟨infer_instance, infer_instance⟩

end projective_model_structure

end bounded_above_cochain_complex
