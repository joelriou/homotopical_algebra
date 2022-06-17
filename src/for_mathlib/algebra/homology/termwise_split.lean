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

namespace algebra

namespace homology

variables {C : Type*} [category C] [additive_category C] [has_binary_biproducts C] /- Fix this -/

namespace hom_complex

namespace twist

variables {F₁ F₂ F₃ : cochain_complex C ℤ} {f₁₂ : F₁ ⟶ F₂} {f₂₃ : F₂ ⟶ F₃}
variables (spl : Π n, splitting (f₁₂.f n) (f₂₃.f n))

include spl

namespace iso_of_termwise_split

@[simps]
def z : cocycle F₃ F₁ 1 :=
begin
  refine ⟨λ q q' hqq', (spl q).section ≫ F₂.d q q' ≫ (spl q').retraction, _⟩,
  rw cocycle.mem_iff 1 2 (by linarith),
  ext q q' hqq',
  subst hqq',
  have d₂ := congr_arg (λ φ, (spl q).section ≫ φ ≫ (spl (q+2)).retraction) (F₂.d_comp_d q (q+1) (q+2)),
  rw [← id_comp (F₂.d (q+1) (q+2)), ← (spl (q+1)).split_add] at d₂,
  simpa only [δ_eq 1 2 (by linarith) q (q+2) rfl (q+1) (q+1) (by linarith) (by linarith),
    comp_zero, zero_comp, assoc, add_comp,comp_add, f₁₂.comm_assoc (q+1) (q+2), splitting.ι_retraction,
    comp_id, ← f₂₃.comm_assoc q (q+1), splitting.section_π_assoc,
    hε', hε₁, neg_neg, one_smul, cochain.zero_apply] using d₂,
end

@[simps]
def α : twist (z spl) ⟶ F₂ :=
twist.desc (z spl) f₁₂ (zero_add 1) (cochain.of_homs (λ q, (spl q).section))
begin
  ext q q' hqq',
  subst hqq',
  simp only [δ_eq 0 1 (zero_add 1).symm q (q+1) rfl q (q+1) (by linarith) rfl, zero_add, hε₁,
    cochain.comp_eq _ _ (add_zero 1).symm q (q+1) (q+1) rfl (by linarith),
    cochain.of_hom_eq, cochain.of_homs_eq, z, assoc],
  have h := congr_arg (λ φ, (spl q).section ≫ F₂.d q (q+1) ≫ φ) ((spl (q+1)).split_add),
  simp only [comp_id, splitting.section_π_assoc, comp_add, ← f₂₃.comm_assoc] at h,
  rw ← h,
  simp only [neg_smul, one_zsmul, add_neg_cancel_right],
end

@[simps]
def β : F₂ ⟶ twist (z spl) :=
twist.lift (z spl) (zero_add 1) (cocycle.of_hom f₂₃) (cochain.of_homs (λ q, (spl q).retraction))
begin
  ext q q' hqq',
  subst hqq',
  simp only [δ_eq 0 1 (zero_add 1).symm q (q+1) rfl q (q+1) (by linarith) rfl, zero_add, hε₁, cochain.sub_apply,
    cochain.comp_eq (cocycle.of_hom f₂₃).1 (z spl).1 (zero_add 1).symm q q (q+1) (by linarith) rfl],
  simp only [cochain.of_hom_eq, cocycle.of_hom, cochain.of_homs_eq, z],
  have h := congr_arg (λ φ, φ ≫ F₂.d q (q+1) ≫ (spl (q+1)).retraction) ((spl q).split_add),
  simp only [add_comp, assoc, f₁₂.comm_assoc q (q+1), splitting.ι_retraction, id_comp, comp_id] at h,
  nth_rewrite 0 h.symm,
  abel,
end

end iso_of_termwise_split


def iso_of_termwise_split : twist (iso_of_termwise_split.z spl) ≅ F₂ :=
{ hom := iso_of_termwise_split.α spl,
  inv := iso_of_termwise_split.β spl,
  hom_inv_id' := begin
    ext q; dsimp,
    { simp only [iso_of_termwise_split.β_f, biprod.inl_desc_assoc, assoc, biprod.lift_fst, comp_id, biprod.inl_fst,
        cochain.comp_eq' 0 0 (q+1-1) q (q+1-1) (q+1-1) (by linarith) (by linarith) (by linarith),
        cochain.of_homs_eq, cochain.of_hom_eq, splitting.section_π], },
    { simp only [iso_of_termwise_split.β_f, biprod.inl_desc_assoc, assoc, biprod.lift_snd, comp_id, biprod.inl_snd,
        cochain.eval' 0 (q+1-1) q (by linarith) q q (by linarith) rfl (cochain.of_homs (λ q, (spl q).section)),
        cochain.of_homs_eq, eq_to_hom_refl, id_comp, splitting.section_retraction, comp_zero], },
    { simp only [iso_of_termwise_split.β_f, biprod.inr_desc_assoc, comp_id],
      ext,
      { simp only [assoc, biprod.lift_fst, biprod.inr_fst,
          cochain.eval' 0 q (q+1-1) (by linarith) q q rfl (by linarith) (cochain.of_hom f₂₃),
          cochain.of_hom_eq, eq_to_hom_refl, id_comp, (spl q).comp_eq_zero_assoc, zero_comp], },
      { simp only [assoc, biprod.lift_snd, splitting.ι_retraction, biprod.inr_snd], }, },
  end,
  inv_hom_id' := begin
    ext q,
    simp only [homological_complex.comp_f, iso_of_termwise_split.β_f, iso_of_termwise_split.α_f,
      biprod.lift_desc, homological_complex.id_f, cochain.comp_eq' 0 0 q (q+1-1) q q (by linarith) (by linarith) (by linarith),
      cochain.of_hom_eq, cochain.of_homs_eq],
    rw [add_comm, (spl q).split_add],
  end, }

end twist

end hom_complex

end homology

end algebra