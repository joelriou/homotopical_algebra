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

variables {F G : cochain_complex C ℤ} {n : ℤ} [∀ p, has_binary_biproduct (F.X (p+1-n)) (G.X p)]

namespace twist

@[protected, simp]
def δ (z : cocycle F G n) (p q : ℤ) : biprod (F.X (p+1-n)) (G.X p) ⟶ biprod (F.X (q+1-n)) (G.X q) :=
begin
  refine biprod.desc _ (biprod.lift 0 (G.d p q)),
  refine biprod.lift (ε (n+1) • F.d (p+1-n) (q+1-n)) _,
  by_cases p+1 = q,
  { exact z.1 (p+1-n) q (by linarith), },
  { exact 0, },
end

end twist

@[simps]
def twist (z : cocycle F G n) : cochain_complex C ℤ :=
{ X := λ p, biprod (F.X (p+1-n)) (G.X p),
  d := λ p q, twist.δ z p q,
  shape' := λ p q hpq, begin
    dsimp [twist.δ],
    ext,
    { simp only [biprod.inl_desc, biprod.lift_fst, comp_zero, zero_comp],
      rw [F.shape, smul_zero],
      intro h,
      apply hpq,
      change p+1-n+1=q+1-n at h,
      change p+1=q,
      linarith, },
    { simp only [biprod.inl_desc, biprod.lift_snd, comp_zero, zero_comp],
      split_ifs,
      { exfalso, exact hpq h, },
      { refl, }, },
    { simp only [biprod.inr_desc, biprod.lift_fst, comp_zero, zero_comp], },
    { simp only [biprod.inr_desc, biprod.lift_snd, comp_zero, zero_comp, G.shape p q hpq], },
  end,
  d_comp_d' := λ i j k hij hjk, begin
    change i+1=j at hij,
    subst hij,
    change i+1+1=k at hjk,
    have hjk' : i+2 = k := by linarith,
    subst hjk',
    simp only [twist.δ, dif_pos rfl, dif_pos (show i+1+1 = i+2, by linarith)],
    ext,
    { simp only [add_zero, biprod.inl_desc_assoc, biprod.lift_desc, linear.smul_comp,
        add_comp, assoc, biprod.lift_fst,
        linear.comp_smul, homological_complex.d_comp_d, smul_zero, comp_zero, zero_comp], },
    { simp only [biprod.inl_desc_assoc, biprod.lift_desc, linear.smul_comp,
        add_comp, assoc, biprod.lift_snd, comp_zero, zero_comp],
      have hz₁ := z.2,
      rw cocycle.mem_iff n (n+1) rfl at hz₁,
      have hz₂ := congr_fun₃ hz₁ (i+1-n) (i+2) (by linarith),
      simp only [cochain.zero_apply,
        δ_eq n (n+1) rfl (i+1-n) (i+2) (by linarith) (i+1) (i+1+1-n) (by linarith) (by linarith)] at hz₂,
      rw ← hz₂,
      abel, },
    { simp only [zero_add, biprod.inr_desc_assoc, biprod.lift_desc, zero_comp, assoc, biprod.lift_fst, comp_zero], },
    { simp only [zero_add, biprod.inr_desc_assoc, biprod.lift_desc, zero_comp, assoc, biprod.lift_snd, homological_complex.d_comp_d,
  comp_zero], },
  end }

namespace twist

@[simps]
def ι (z : cocycle F G n) : G ⟶ twist z :=
{ f := λ p, biprod.lift 0 (𝟙 (G.X p)), }

@[simp]
def φ {z : cocycle F G n} {K : cochain_complex C ℤ} (f : twist z ⟶ K) {n' : ℤ} (hn' : n'+1 = n) :
  cochain F K n' :=
λ q q' hqq', eq_to_hom (by { congr, linarith, }) ≫ biprod.inl ≫ f.f q'

@[simps]
def γ {z : cocycle F G n} {K : cochain_complex C ℤ} (f : twist z ⟶ K) : G ⟶ K :=
twist.ι z ≫ f

attribute [reassoc] homological_complex.d_comp_eq_to_hom

def dφ {z : cocycle F G n} {K : cochain_complex C ℤ} (f : twist z ⟶ K) {n' : ℤ} (hn' : n'+1 = n) :
  δ n' n (φ f hn') = cochain.comp z.1 (cochain.of_hom (γ f)) (add_zero n).symm :=
begin
  ext q q' hqq',
  simp only [cochain.comp_eq z.1 (cochain.of_hom (γ f)) (add_zero n).symm q q' q' hqq' (add_zero q').symm,
    cochain.of_hom_eq, δ_eq n' n hn' q q' hqq' (q'-1) (q+1) rfl rfl],
  have hq : q = (q'-1)+1-n := by linarith,
  subst hq, /- This substitution makes the eq_to_hom disappear when unfolding φ -/
  have h₁ : q'-1+1-n+1 = q'+1-n := by linarith,
  have h₂ : q'-1+1-n+1 = q'-1+1-n+1 := rfl,
  have hf₁ := f.comm (q'-1) q',
  have hf₂ := congr_arg (λ α, biprod.inl ≫ α) hf₁,
  have h₃ : ε (n+1) = -ε (n'+1) := by { rw hn', apply hε', },
  simp only [twist_d, twist.δ, biprod.inl_desc_assoc, biprod.lift_eq,
    dif_pos (show q' - 1 + 1 = q', by linarith), h₃] at hf₂,
  simp only [φ, γ, ι, homological_complex.comp_f, eq_to_hom_refl, id_comp,
    homological_complex.d_comp_eq_to_hom_assoc F h₁ h₂,
    assoc, hf₂, biprod.lift_eq,
    zero_add, neg_smul, neg_comp, linear.smul_comp, add_comp,
    neg_add_cancel_comm, zero_comp, id_comp],
end

@[simps]
def twist.desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  twist z ⟶ K :=
{ f := λ p, biprod.desc (φ (p+1-n) p (by linarith)) (γ.f p),
  comm' := λ i j hij, begin
    ext,
    { change i+1 = j at hij,
      subst hij,
      simp only [biprod.inl_desc_assoc, twist.δ, twist_d, biprod.lift_desc, linear.smul_comp, dif_pos],
      have hφγ₂ := congr_fun₃ hφγ (i+1-n) (i+1) (by linarith),
      simp only [δ_eq n' n hn' (i+1-n) (i+1)  (by linarith) i (i+1+1-n) (by linarith) (by linarith),
        cochain.comp_eq z.1 (cochain.of_hom γ) (add_zero n).symm (i+1-n) (i+1) (i+1) (by linarith) (by linarith),
        cochain.of_hom_eq] at hφγ₂,
      have hn'' : ε (n+1) = -ε (n'+1) := by { rw hn', apply hε', },
      simp only [← hφγ₂, hn'', neg_smul, neg_add_cancel_comm_assoc], },
    { simp only [zero_add, biprod.inr_desc_assoc, homological_complex.hom.comm,
        twist.δ, twist_d, biprod.lift_desc, zero_comp], },
  end, }

@[simps]
def twist.lift (z : cocycle F G n) {K : cochain_complex C ℤ} {n' : ℤ} (hn' : n'+n=1)
  (ψ : cocycle K F n') (υ : cochain K G 0) (hψυ : δ 0 1 υ = -cochain.comp ψ.1 z.1 hn'.symm) :
  K ⟶ twist z :=
{ f := λ p, biprod.lift (ψ.1 p (p+1-n) (by linarith)) (υ p p (by linarith)),
  comm' := λ i j hij, begin
    have hn'' : n' = 1-n := by linarith,
    change i+1 = j at hij,
    substs hij hn'',
    ext,
    { simp only [twist_d, add_zero, twist.δ, biprod.lift_desc, add_comp, assoc, biprod.lift_fst,
        linear.comp_smul, comp_zero],
      have hψ₁ := ψ.2,
      rw cocycle.mem_iff (1-n) (1+1-n) (by linarith) at hψ₁,
      have hψ₂ := congr_fun₃ hψ₁ i (i+1+1-n) (by linarith),
      simp only [δ_eq (1-n) (1+1-n) (by linarith) i (i+1+1-n) (by linarith) (i+1-n) (i+1) (by linarith) rfl ψ.1,
        cochain.zero_apply, add_eq_zero_iff_eq_neg] at hψ₂,
      rw [hψ₂],
      have eq : -ε (n+1) * ε (1-n+1) = 1,
      { rw [show 1-n+1=(-n)+1+1, by linarith],
        simp only [hε, hε₁, mul_neg, mul_one, neg_neg],
        rw [← hε n (-n), add_right_neg, hε₀], },
      simp only [zsmul_neg', neg_smul, smul_smul, eq, one_smul], },
    { have hψυ₂ := congr_fun₃ hψυ i (i+1) (by linarith),
      simp only [cochain.neg_apply,
        cochain.comp_eq ψ.1 z.1 (show 1=1-n+n, by linarith) i (i+1-n) (i+1) (by linarith) (by linarith),
        δ_eq 0 1 rfl i (i+1) rfl i (i+1) (by linarith) rfl, zero_add, hε₁, neg_smul, one_smul] at hψυ₂,
      simp only [twist_d, twist.δ, dif_pos, biprod.lift_desc, biprod.lift_snd, add_comp, assoc],
      suffices : Π (a b c : K.X i ⟶ G.X (i + 1)), a + (-b) = -c → c+a=b,
      { exact this _ _ _ hψυ₂, },
      intros a b c h,
      have h' := congr_arg (λ x, -x) h,
      simp only [neg_add_rev, neg_neg] at h',
      rw [← h', neg_add_cancel_right], },
  end, }

end twist

end hom_complex

end homology

end algebra
