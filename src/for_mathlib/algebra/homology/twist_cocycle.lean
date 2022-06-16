/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.hom_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace algebra

namespace homology

namespace hom_complex

variables {C : Type*} [category C] [preadditive C]

variables {F G : chain_complex C ℤ} {n : ℤ} [∀ p, has_binary_biproduct (F.X (p-1-n)) (G.X p)]

def twist (z : hom_complex.Z F G n) : chain_complex C ℤ :=
{ X := λ p, biprod (F.X (p-1-n)) (G.X p),
  d := λ p q, begin
    refine biprod.desc (biprod.lift (ε (n+1) • F.d (p-1-n) (q-1-n)) (z.1 (p-1-n) ≫ _)) (biprod.lift 0 (G.d p q)),
    by_cases q+1=p,
    { exact eq_to_hom (by { congr, rw ← h, linarith, }), },
    { exact 0, }
  end,
  shape' := λ p q hpq, begin
    have hpq' : ¬ (q-1-n)+1 = p-1-n,
    { intro h₁,
      change ¬ q+1 = p at hpq,
      apply hpq,
      linarith, },
    split_ifs,
    { exfalso, exact hpq h, },
    { ext,
      { simp only [comp_zero, biprod.inl_desc, biprod.lift_fst, zero_comp, smul_zero, F.shape (p-1-n) (q-1-n) hpq'], },
      { simp only [comp_zero, biprod.inl_desc, biprod.lift_snd, zero_comp], },
      { simp only [comp_zero, biprod.inr_desc, biprod.lift_fst, zero_comp], },
      { simp only [comp_zero, biprod.inr_desc, biprod.lift_snd, zero_comp, G.shape p q hpq], }, },
  end,
  d_comp_d' := λ p q r hpq hpr, begin
    change q+1 = p at hpq,
    change r+1 = q at hpr,
    substs hpq hpr,
    split_ifs,
    { ext,
      { simp only [add_zero, biprod.inl_desc_assoc, biprod.lift_desc, linear.smul_comp, assoc,
          preadditive.add_comp, biprod.lift_fst, linear.comp_smul, homological_complex.d_comp_d,
            smul_zero, comp_zero, zero_comp], },
      { simp only [biprod.inl_desc_assoc, biprod.lift_desc, linear.smul_comp, assoc, preadditive.add_comp,
          biprod.lift_snd, linear.comp_smul, comp_zero, zero_comp],
        have hz₁ := z.2,
        dsimp only [Z] at hz₁,
        rw add_monoid_hom.mem_ker at hz₁,
        have hz₂ := congr_fun hz₁ (r+1-n),
        have h₁ : r+1+1-1-n = r+1-n := by linarith,
        have h₂ : r+1-n+ (n-1) = r := by linarith,
        have hz₃ := congr_arg (λ φ, eq_to_hom (congr_arg F.X h₁) ≫ φ ≫ eq_to_hom (congr_arg G.X h₂)) hz₂,
        have eqz₁ := eq_to_hom_f n z.1 (r+1-n+(n-1)-n) (r-n) (by linarith),
        have eqz₂ := eq_to_hom_f n z.1 (r+1-1-n) (r-n) (by linarith),
        have eqz₃ := eq_to_hom_f n z.1 (r+1+1-1-n) (r+1-n) (by linarith),
        dsimp at eqz₁ eqz₂ eqz₃ hz₃ ⊢,
        rw [eq_to_hom_d G (r+1-n+n) (r+1-n+(n-1)) (r+1) r (by linarith) (by linarith),
          eq_to_hom_d F (r+1-n) (r+1-n+(n-1)-n) (r+1-n) (r-n) (by linarith) (by linarith),
          eqz₁] at hz₃,
        rw [eq_to_hom_d F (r+1+1-1-n) (r+1-1-n) (r+1-n) (r-n) (by linarith) (by linarith), eqz₂, eqz₃],
        conv_lhs { rw add_comm, },
        simpa only [assoc, eq_to_hom_refl, id_comp, comp_id, zero_comp, comp_zero, comp_add, add_comp,
          comp_zsmul, zsmul_comp, eq_to_hom_trans, eq_to_hom_trans_assoc] using hz₃, },
      { simp only [zero_add, biprod.inr_desc_assoc, biprod.lift_desc, zero_comp, assoc, biprod.lift_fst, comp_zero], },
      { simp only [zero_add, biprod.inr_desc_assoc, biprod.lift_desc, zero_comp, assoc,
          biprod.lift_snd, homological_complex.d_comp_d, comp_zero], }, },
    { exfalso, exact h rfl, },
  end }

end hom_complex

end homology

end algebra