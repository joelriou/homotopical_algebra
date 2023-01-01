/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.preadditive.projective
--import category_theory.limits.shapes.kernels
import algebra.homology.short_exact.preadditive
import for_mathlib.category_theory.retracts
import category_theory.abelian.projective
import category_theory.abelian.basic
import for_mathlib.category_theory.limits.kernel_functor

noncomputable theory

open category_theory category_theory.limits category_theory.category category_theory.preadditive
open_locale zero_object

namespace category_theory

variables {C : Type*} [category C]

namespace short_exact

lemma of_mono [abelian C] {X Y : C} (i : X ⟶ Y) [category_theory.mono i] :
  short_exact i (cokernel.π i) :=
{ mono := infer_instance,
  epi := infer_instance,
  exact := abelian.exact_cokernel i, }

lemma of_epi [abelian C] {X Y : C} (p : X ⟶ Y) [category_theory.epi p] :
  short_exact (kernel.ι p) p :=
{ mono := infer_instance,
  epi := infer_instance,
  exact := abelian.exact_of_is_kernel (kernel.ι p) p (kernel.condition p) (kernel_is_kernel p), }

lemma is_right_split_of_projective [abelian C] {X Y Z : C} {i : X ⟶ Y}
  {p : Y ⟶ Z} (h : short_exact i p) [projective Z] : right_split i p :=
{ right_split := begin
    haveI := h.epi,
    exact ⟨projective.factor_thru (𝟙 Z) p, projective.factor_thru_comp _ _⟩,
  end,
  mono := h.mono,
  exact := h.exact }

def lift [abelian C] {X Y Z W : C} {i : X ⟶ Y} {p : Y ⟶ Z} (h : short_exact i p) (f : W ⟶ Y)
  (hf : f ≫ p = 0) : W ⟶ X :=
begin
  haveI := h.mono,
  exact (kernel_fork.is_limit.lift' ((abelian.is_limit_of_exact_of_mono i p (h.exact))) f hf).1,
end

@[simp, reassoc]
lemma lift_comp [abelian C] {X Y Z W : C} {i : X ⟶ Y} {p : Y ⟶ Z} (h : short_exact i p) (f : W ⟶ Y)
  (hf : f ≫ p = 0) : h.lift f hf ≫ i = f :=
begin
  haveI := h.mono,
  exact (kernel_fork.is_limit.lift' ((abelian.is_limit_of_exact_of_mono i p (h.exact))) f hf).2,
end

end short_exact

namespace right_split

def split [abelian C] {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z} (h : category_theory.right_split i p) :
  split i p  :=
begin
  haveI := h.mono,
  cases h.right_split with s hs,
  refine ⟨⟨h.short_exact.lift (𝟙 Y - p ≫ s) _, s, _, hs, h.exact.w, _, _⟩⟩,
  { simp only [hs, sub_comp, id_comp, assoc, comp_id, sub_self], },
  { simp only [← cancel_mono i, h.exact.w_assoc, id_comp, assoc, comp_id, short_exact.lift_comp,
      comp_sub, zero_comp, sub_zero], },
  { rw [← cancel_mono i, assoc, short_exact.lift_comp, comp_sub, comp_id,
      ← assoc, hs, id_comp, sub_self, zero_comp], },
  { simp only [short_exact.lift_comp, sub_add_cancel], },
end

end right_split

namespace preadditive

variable (C)

def mono_with_projective_coker [preadditive C] : morphism_property C :=
  λ X Y φ, ∃ (Z : C) (hZ : projective Z) (p : Y ⟶ Z), category_theory.split φ p

namespace mono_with_projective_coker

lemma mem_iff [abelian C] {X Y : C} (φ : X ⟶ Y) :
  mono_with_projective_coker C φ ↔ (mono φ ∧ projective (cokernel φ)) :=
begin
  split,
  { rintro ⟨Z, hZ, p, hp⟩,
    haveI := hp.short_exact.epi,
    refine ⟨hp.short_exact.mono, _⟩,
    have e : Z ≅ cokernel φ := is_colimit.cocone_point_unique_up_to_iso
      (abelian.is_colimit_of_exact_of_epi φ p hp.exact) (limits.colimit.is_colimit _),
    rw ← projective.iso_iff e,
    exact hZ, },
  { intro h,
    haveI := h.1,
    haveI := h.2,
    refine ⟨cokernel φ, h.2, cokernel.π _, _⟩,
    exact (short_exact.of_mono φ).is_right_split_of_projective.split, }
end

lemma of_biprod_inl [preadditive C] (X Y : C) [hY : projective Y] [has_binary_biproduct X Y] :
  mono_with_projective_coker C (biprod.inl : X ⟶ X ⊞ Y) :=
⟨Y, hY, biprod.snd, ⟨⟨biprod.fst, biprod.inr, by tidy⟩⟩⟩

variable {C}

lemma id_mem [preadditive C] [has_zero_object C] (X : C) :
  mono_with_projective_coker C (𝟙 X) :=
⟨0, projective.zero_projective, 0, split.mk ⟨𝟙 X, 0, by simp⟩⟩

lemma of_is_iso [preadditive C] [has_zero_object C] {X Y : C} (f : X ⟶ Y) [is_iso f] :
  mono_with_projective_coker C f :=
⟨0, projective.zero_projective, 0, split.mk ⟨inv f, 0, by simp⟩⟩

variable (C)

lemma is_stable_by_composition [preadditive C] [has_binary_biproducts C]:
  (mono_with_projective_coker C).stable_under_composition :=
begin
  intros X Y Z f g hf hg,
  rcases hf with ⟨A, hA, p, hp⟩,
  rcases hg with ⟨B, hB, q, hq⟩,
  haveI := hA,
  haveI := hB,
  rcases hp with ⟨rf, i, hfr, hip, hfp, hir, hY⟩,
  rcases hq with ⟨rg, j, hgr, hjq, hgq, hjr, hZ⟩,
  refine ⟨A ⊞ B, infer_instance, biprod.lift (rg ≫ p) q,
    ⟨⟨rg ≫ rf, biprod.desc (i ≫ g) j, _, _, _, _, _⟩⟩⟩,
  { slice_lhs 2 3 { rw hgr, },
    rw [id_comp, hfr], },
  { ext,
    { simp only [biprod.inl_desc_assoc, assoc, biprod.lift_fst, comp_id, biprod.inl_fst],
      slice_lhs 2 3 { rw hgr, },
      rw [id_comp, hip], },
    { simp only [biprod.inl_desc_assoc, assoc, biprod.lift_snd, comp_id, biprod.inl_snd,
        hgq, comp_zero], },
    { simp only [biprod.inr_desc_assoc, assoc, biprod.lift_fst, comp_id, biprod.inr_fst],
      rw [← assoc, hjr, zero_comp], },
    { simp only [biprod.inr_desc_assoc, assoc, biprod.lift_snd, comp_id, biprod.inr_snd,
        hjq], }, },
  { ext,
    { simp only [assoc, biprod.lift_fst, zero_comp],
      slice_lhs 2 3 { rw hgr },
      rw [id_comp, hfp], },
    { simp only [assoc, biprod.lift_snd, zero_comp, hgq, comp_zero], }, },
  { ext,
    { simp only [biprod.inl_desc_assoc, assoc, comp_zero],
      slice_lhs 2 3 { rw hgr, },
      rw [id_comp, hir], },
    { simp only [biprod.inr_desc_assoc, comp_zero],
      slice_lhs 1 2 { rw hjr, },
      rw zero_comp, }, },
  { simp only [assoc, biprod.lift_desc],
    rw [← hZ, ← add_assoc, ← comp_add, ← assoc, ← assoc, ← add_comp, hY, id_comp], },
end

lemma is_stable_by_retract [abelian C] :
  (mono_with_projective_coker C).is_stable_by_retract :=
begin
  intros X₁ X₂ Y₁ Y₂ x y hxy hy,
  rw mem_iff at ⊢ hy,
  exact ⟨morphism_property.is_stable_by_retract.for_monomorphisms x y hxy hy.1,
    projective.of_retract (is_retract.imp_of_functor (limits.cokernel_functor C) _ _ hxy) hy.2⟩,
end

end mono_with_projective_coker

end preadditive

end category_theory
