/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.twist_cocycle
import category_theory.additive.basic
import algebra.homology.short_exact.preadditive

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace cochain_complex

variables {C : Type*} [category C] [additive_category C] [has_binary_biproducts C] /- Fix this -/

namespace hom_complex

namespace twist

variables {F₁ F₂ F₃ : cochain_complex C ℤ} {f₁₂ : F₁ ⟶ F₂} {f₂₃ : F₂ ⟶ F₃}
variables (spl : Π n, splitting (f₁₂.f n) (f₂₃.f n))

include spl

namespace iso_of_termwise_split

@[simps]
def z : cocycle F₃ F₁ 1 :=
cocycle.mk (cochain.mk (λ p q hpq, (spl p).section ≫ F₂.d p q ≫ (spl q).retraction)) 2 rfl
begin
  ext,
  subst hpq,
  have d₂ := congr_arg (λ φ, (spl p).section ≫ φ ≫ (spl (p+2)).retraction) (F₂.d_comp_d p (p+1) (p+2)),
  rw [← id_comp (F₂.d (p+1) (p+2)), ← (spl (p+1)).split_add] at d₂,
  simpa only [δ_v 1 2 rfl _ p (p+2) rfl (p+1) (p+1) (by linarith) rfl,
    cochain.mk_v, assoc, ε_succ, ε_1, neg_neg, one_zsmul, cochain.zero_v, comp_zero, zero_comp,
    comp_add, add_comp, ← f₂₃.comm_assoc p (p+1), splitting.section_π_assoc,
    f₁₂.comm_assoc (p+1) (p+2), splitting.ι_retraction, comp_id] using d₂,
end

@[simps]
def α : twist (z spl) ⟶ F₂ :=
twist.desc (z spl) (cochain.of_homs (λ q, (spl q).section)) f₁₂ (zero_add 1)
begin
  ext,
  have h := congr_arg (λ φ, (spl p).section ≫ F₂.d p q ≫ φ) ((spl q).split_add),
  simp only [comp_id, splitting.section_π_assoc, comp_add, ← f₂₃.comm_assoc] at h,
  simp only [δ_v 0 1 rfl _ p q hpq p q (by linarith) hpq,
    zero_add, cochain.of_homs_v, ε_1, neg_smul, one_zsmul, z_coe,
    cochain.comp_zero_cochain, cochain.mk_v, cochain.of_hom_v, assoc,
    ← h, add_neg_cancel_right],
end

def β : F₂ ⟶ twist (z spl) :=
twist.lift (z spl) (cocycle.of_hom f₂₃) (cochain.of_homs (λ q, (spl q).retraction)) (zero_add 1) (zero_add 1)
begin
  ext,
  have h := congr_arg (λ φ, φ ≫ F₂.d p q ≫ (spl q).retraction) ((spl p).split_add),
  simp only [assoc, id_comp, comp_id, add_comp, f₁₂.comm_assoc, splitting.ι_retraction] at h,
  simp only [cochain.add_v, δ_v 0 1 rfl _ p q hpq p q (by linarith) hpq,
    cochain.of_homs_v, zero_add, ε_1, neg_zsmul, one_zsmul,
    z_coe, cochain.zero_cochain_comp, cochain.mk_v, cochain.zero_v,
    cocycle.of_hom_coe, cochain.of_hom_v],
  nth_rewrite 0 h.symm,
  abel,
end

end iso_of_termwise_split

def iso_of_termwise_split : twist (iso_of_termwise_split.z spl) ≅ F₂ :=
{ hom := iso_of_termwise_split.α spl,
  inv := iso_of_termwise_split.β spl,
  hom_inv_id' := cochain.of_hom_injective begin
    simp [iso_of_termwise_split.α, iso_of_termwise_split.β, desc, lift,
      cochain_ext _ _ _ (zero_add 1) (zero_add 0).symm,
      ← cochain.comp_assoc_of_second_is_zero_cochain, inl_comp_desc_cochain,
      inr_comp_desc_cochain],
    simp only [cochain_ext' (iso_of_termwise_split.z spl) _ _ (add_zero 1) (zero_add 0).symm,
      cochain.comp_assoc_of_second_is_zero_cochain, lift_cochain_comp_fst,
      lift_cochain_comp_snd, inl_comp_fst, inl_comp_snd, inr_comp_fst, inr_comp_snd],
    simp only [cochain.of_hom, cochain.of_homs_comp, splitting.section_π,
      splitting.ι_retraction, splitting.section_retraction, cochain.of_homs_zero,
      λ p, (spl p).comp_eq_zero],
    tauto,
  end,
  inv_hom_id' := begin
    apply cochain.of_hom_injective,
    simp only [iso_of_termwise_split.α, iso_of_termwise_split.β, desc, lift,
      lift_cochain_eq _ _ _ rfl (zero_add 1), inl_comp_desc_cochain, inr_comp_desc_cochain,
      cochain.of_hom_comp, cocycle.cochain_of_hom_hom_of_eq_coe, lift_hom_as_cocycle_coe,
      cocycle.of_hom_coe, desc_hom_as_cocycle_coe, cochain.add_comp,
      cochain.comp_assoc_of_third_is_zero_cochain],
    ext,
    simp only [cochain.add_v, cochain.comp_zero_cochain, cochain.of_hom_v,
      cochain.of_homs_v, homological_complex.id_f, ← (spl p).split_add, add_comm],
  end, }

end twist

end hom_complex

end cochain_complex
