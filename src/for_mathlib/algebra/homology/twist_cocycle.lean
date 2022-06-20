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
  refine biprod.desc (biprod.lift (ε (n+1) • F.d (p+1-n) (q+1-n)) _) (biprod.lift 0 (G.d p q)),
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

lemma biprod_is_zero_iff {C : Type*} [category C] [preadditive C] (A B : C) [has_binary_biproduct A B] :
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

def is_bounded_above (z : cocycle F G n) (hF : F.is_bounded_above) (hG : G.is_bounded_above) :
  (twist z).is_bounded_above :=
begin
  cases hF with r hr,
  cases hG with s hs,
  use max (r+n-1) s,
  intros i hi,
  dsimp only [twist],
  rw biprod_is_zero_iff,
  split,
  { apply hr,
    have h := lt_of_le_of_lt (le_max_left _ _) hi,
    linarith, },
  { apply hs,
    exact lt_of_le_of_lt (le_max_right _ _) hi, }, 
end

@[simp]
def inl (z : cocycle F G n) {n' : ℤ} (hn' : n'+1=n) : cochain F (twist z) n' :=
λ q q' hqq', cochain.of_hom (𝟙 F) q (q'+1-n) (by linarith) ≫ biprod.inl
@[simps]
def inr (z : cocycle F G n) : G ⟶ twist z := { f := λ p, biprod.inr, }
@[simp]
def fst (z : cocycle F G n) {n' : ℤ} (hn' : n+n'=1) : cocycle (twist z) F n' :=
cocycle.mk (λ q q' hqq', biprod.fst ≫ (cochain.of_hom (𝟙 F) (q+1-n) q' (by linarith))) (n'+1) rfl
begin
  have hn'' : n'=1-n := by linarith,
  substs  hn'',
  ext1 q, ext1 q', ext1 hqq',
  simp only [δ_eq (1-n) (1-n+1) rfl q q' hqq' (q+1-n) (q+1) (by linarith) rfl,
    cochain.of_hom_eq, homological_complex.id_f, comp_id, twist_d, twist.δ, dif_pos, cochain.zero_apply],
  ext,
  { have hq' : q' = q+1+1-n := by linarith,
    subst hq',
    have eq : ε (1-n+1) * ε (n+1) = ε ((1 : ℤ) + 1 + 1) := by { rw [← hε], congr' 1, linarith, },
    have eq' : ε ((1 : ℤ)+1+1) = -1 := by { rw [hε', hε', hε₁, neg_neg], },
    simp only [cochain.of_hom_eq, homological_complex.id_f, comp_id, comp_add, biprod.inl_fst_assoc,
      linear.comp_smul, biprod.inl_desc_assoc, biprod.lift_fst, smul_smul,
      eq, eq', neg_smul, one_smul, comp_zero, add_right_neg], },
  { simp only [comp_add, biprod.inr_fst_assoc, zero_comp, linear.comp_smul, biprod.inr_desc_assoc,
      biprod.lift_fst_assoc, smul_zero, add_zero, comp_zero], },
end
@[simp]
def snd (z : cocycle F G n) : cochain (twist z) G 0 := λ q q' hqq', biprod.snd ≫ (cochain.of_hom (𝟙 G)) q q' hqq'

@[simp]
lemma inl_comp_fst (z : cocycle F G n) {n' n'': ℤ} (hn' : n'+1=n) (hn'' : n+n''=1) :
  (inl z hn').comp (fst z hn'').1 (show 0=n'+n'', by linarith) = cochain.of_hom (𝟙 F) :=
begin
  ext q q' hqq',
  have h : n'' = -n' := by linarith,
  have hqq'' : q = q' := by linarith,
  unfreezingI { substs hn' h hqq'', },
  simp only [cochain.comp_eq _ _ (show 0 = n'+(-n'), by linarith) q (q+n') q rfl (by linarith),
    inl, fst, cocycle.mk, assoc, biprod.inl_fst_assoc, cochain.of_hom_eq,
    homological_complex.id_f, cochain.of_hom_eq, cochain.of_hom, id_comp, eq_to_hom_trans],
end

@[simp]
lemma inl_comp_snd (z : cocycle F G n) {n' : ℤ} (hn' : n'+1=n) : (inl z hn').comp (snd z) (add_zero n').symm = 0 :=
begin
  ext q q' hqq',
  simp only [inl, snd, cochain.comp₀, cochain.of_hom_eq, homological_complex.id_f, comp_id, assoc,
    biprod.inl_snd, comp_zero, cochain.zero_apply],
end

@[simp]
lemma inr_comp_fst (z : cocycle F G n) {n' : ℤ} (hn' : n+n'=1) :
  (cochain.of_hom (inr z)).comp (fst z hn').1 (zero_add n').symm = 0 :=
begin
  ext q q' hqq',
  simp only [cocycle.mk, fst, cochain.comp₀', cochain.of_hom_eq, inr_f, biprod.inr_fst_assoc, zero_comp, cochain.zero_apply],
end

@[simp]
lemma inr_comp_snd (z : cocycle F G n) : (cochain.of_hom (inr z)).comp (snd z) (add_zero 0).symm = cochain.of_hom (𝟙 G) :=
begin
  ext q q' hqq',
  simp only [snd, add_zero, cochain.comp₀', cochain.of_hom_eq, inr_f, biprod.inr_snd_assoc],
end

lemma δ_inl (z : cocycle F G n) {n' : ℤ} (hn' : n'+1=n) :
  δ n' n (inl z hn') = cochain.comp z.1 (cochain.of_hom (inr z)) (add_zero n).symm :=
begin
  ext q q' hqq',
  { dsimp [δ, cochain.of_hom],
    have h₁ : q+1 = q'+1-n := by linarith,
    have h₂ : q+1 = q+n-n' := by linarith,
    have h₃ : (q+n'+1-n)+1 = q'+1-n := by linarith,
    have eq : ε (n'+1) = - ε (n+1) := by rw [hε' n, neg_neg, hn'],
    simp only [F.d_comp_eq_to_hom h₁ h₂, F.eq_to_hom_comp_d h₁ h₃, eq, id_comp, assoc, biprod.inl_desc, neg_smul, add_comp,
      biprod.lift_fst, linear.comp_smul, neg_comp, linear.smul_comp, biprod.inl_fst, comp_id, add_right_neg,
      cochain.comp₀, eq_to_hom_refl, biprod.inr_fst, comp_zero], },
  { have hq : q = q'-1+1-n := by linarith,
    subst hq,
    simp only [cochain.comp_eq z.1 (cochain.of_hom _) (add_zero n).symm (q'-1+1-n) q' q' hqq' (add_zero q').symm,
      cochain.of_hom_eq, δ_eq n' n hn' (q'-1+1-n) q' hqq' (q'-1) (q'-1+1-n+1) rfl rfl,
      inl, sub_add_cancel, add_zero, cochain.of_hom_eq, homological_complex.id_f, id_comp, twist.δ, twist_d, dif_pos,
      biprod.inl_desc, add_comp, biprod.lift_snd, linear.smul_comp, assoc, biprod.inl_snd, comp_zero, smul_zero, inr_f,
      biprod.inr_snd, comp_id], },
end

lemma δ_snd (z : cocycle F G n) {n' : ℤ} (hn' : n+n'=1) :
  δ 0 1 (snd z) = -cochain.comp (fst z hn').1 z.1 (by linarith) :=
begin
  ext1 q, ext1 q', ext1 hqq',
  subst hqq',
  simp only [δ_eq 0 1 (zero_add 1) q (q+1) rfl q (q+1) (by linarith) rfl, zero_add, hε₁,
    cochain.neg_apply, cochain.comp_eq _ z.1 (show 1=n'+n, by linarith) q (q+1-n) (q+1) (by linarith) (by linarith),
    twist.δ, twist_d, dif_pos, fst, snd, cochain.of_hom_eq, homological_complex.id_f, comp_id, neg_smul, one_smul,
    cocycle.mk],
  ext,
  { simp only [zero_add, comp_add, biprod.inl_snd_assoc, zero_comp, comp_neg, biprod.inl_desc_assoc, biprod.lift_snd,
      biprod.inl_fst_assoc], },
  { simp only [neg_zero, comp_add, biprod.inr_snd_assoc, comp_neg, biprod.inr_desc_assoc, biprod.lift_snd, add_right_neg,
      biprod.inr_fst_assoc, zero_comp], },
end

@[simp]
def φ {z : cocycle F G n} {K : cochain_complex C ℤ} (f : twist z ⟶ K) {n' : ℤ} (hn' : n'+1 = n) :
  cochain F K n' :=
λ q q' hqq', eq_to_hom (by { congr, linarith, }) ≫ biprod.inl ≫ f.f q'

@[simps]
def γ {z : cocycle F G n} {K : cochain_complex C ℤ} (f : twist z ⟶ K) : G ⟶ K :=
twist.inr z ≫ f

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
  simp only [φ, γ, inr, homological_complex.comp_f, eq_to_hom_refl, id_comp,
    homological_complex.d_comp_eq_to_hom_assoc F h₁ h₂,
    assoc, hf₂, biprod.lift_eq,
    zero_add, neg_smul, neg_comp, linear.smul_comp, add_comp,
    neg_add_cancel_comm, zero_comp, id_comp],
end

lemma cochain_ext (z : cocycle F G n) {K : cochain_complex C ℤ} (m n' n'' : ℤ) (hn' : n'+1=n) (hn'' : n'' = n'+m) (y₁ y₂ : cochain (twist z) K m) :
  y₁ = y₂ ↔ cochain.comp (inl z hn') y₁ hn'' = cochain.comp (inl z hn') y₂ hn'' ∧
    cochain.comp (cochain.of_hom (inr z)) y₁ (zero_add m).symm = cochain.comp (cochain.of_hom (inr z)) y₂ (zero_add m).symm :=
begin
  unfreezingI { substs hn' hn'', },
  split,
  { intro h,
    subst h,
    tauto, },
  { intro h,
    ext q q' hqq',
    { simpa only [cochain.comp_eq _ _ (rfl : n'+m = _) (q+1-(n'+1)) q q' (by linarith) (by linarith), inl,
        cochain.of_hom_eq, homological_complex.id_f, id_comp] using congr_fun₃ h.1 (q+1-(n'+1)) q' (by linarith), },
    { simpa only [cochain.comp₀', cochain.of_hom_eq] using congr_fun₃ h.2 q q' hqq', }, }
end

def desc_cochain (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' : ℤ}
  (γ : cochain G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) : cochain (twist z) K m :=
cochain.comp (snd z) γ (zero_add m).symm + cochain.comp (fst z (add_eq_of_eq_sub' rfl)).1 φ (by linarith)

@[simp]
def desc_cochain_eq (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' n'': ℤ}
  (γ : cochain G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) (hn'' : n+n''=1):
desc_cochain z γ φ hn' = cochain.comp (snd z) γ (zero_add m).symm + cochain.comp (fst z hn'').1 φ (by linarith) :=
begin
  have h : n'' = 1-n := by linarith,
  subst h,
  refl,
end

@[simp]
lemma inr_comp_desc_cochain (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' : ℤ}
  (γ : cochain G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) :
  cochain.comp (cochain.of_hom (inr z)) (desc_cochain z γ φ hn') (zero_add m).symm = γ :=
begin
  simp only [desc_cochain],
  simp only [cochain.comp_add, inr_comp_fst, inr_comp_snd, cochain.id_comp, cochain.zero_comp, add_zero,
    ← cochain.comp_assoc _ _ _ (zero_add 0).symm (zero_add m).symm (show m = _, by linarith),
    ← cochain.comp_assoc _ _ _ (zero_add (1-n)).symm (show m=(1-n)+n', by linarith) (show m = _, by linarith)],
end

def δ_desc_cochain (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' n'' n''' : ℤ}
  (γ : cochain G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) (m' : ℤ) (hm' : m+1=m') (hn'' : n+n'' = 1)
  (hn''' : n''' = n'+1):
  δ m m' (desc_cochain z γ φ hn') =
  (fst z hn'').1.comp (ε (m+1) • (z.1.comp γ (show n''' = _, by linarith)) + δ n' n''' φ) (show m'=_, by linarith) +
  (snd z).comp (δ m m' γ) (zero_add m').symm :=
begin
  simp only [cochain_ext z m' (n-1) (n-1+m') (by linarith) (by linarith),
    desc_cochain_eq z γ φ hn' hn'', cochain.comp_add, δ_add, hε',
    δ_comp (fst z hn'').1 φ (show m=_, by linarith) _ n''' m' hm' rfl hn'''.symm, cocycle.δ_eq_zero,
    δ_comp (snd z) γ (zero_add m).symm 1 m' m' hm' (zero_add 1) hm',
    cochain.zero_comp, cochain.comp_zero, zsmul_zero, add_zero, cochain.comp_add,
    cochain.comp_neg, δ_snd z hn'', cochain.neg_comp, cochain.comp_neg, zsmul_neg, neg_smul,
    cochain.zsmul_comp, cochain.comp_zsmul,
    cochain.comp_assoc (fst z hn'').1 z.1 γ (show 1=n''+n, by linarith) (show n''' = n+m, by linarith) (show m'= _, by linarith)],
  suffices : ∀ (X Y : cochain_complex C ℤ) (q : ℤ) (x y z : cochain X Y q), x+y+z = y+z+x,
  { split; apply this, },
  intros X Y q x y z,
  abel,
end

@[simps]
def δ_desc_cocycle (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' n''' : ℤ}
  (γ : cocycle G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) (m' : ℤ) (hm' : m+1=m') (hn''' : n''' = n'+1)
  (hφ : δ n' n''' φ = ε m • (z.1.comp γ.1 (show n'''=_, by linarith))) : cocycle (twist z) K m :=
cocycle.mk (desc_cochain z γ.1 φ hn') m' hm'
(by simp only [δ_desc_cochain z γ.1 φ hn' m' hm' (show n+(1-n)=1, by linarith) hn''', hφ, neg_smul, add_left_neg,
    cochain.comp_zero, zero_add, cocycle.δ_eq_zero, hε'])

@[simps]
def desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  twist z ⟶ K :=
begin
  equiv_rw (cocycle.equiv_hom (twist z) K).to_equiv,
  apply δ_desc_cocycle z (cocycle.of_hom γ) φ (by linarith) 1 (zero_add 1) hn'.symm,
  simpa only [hε₀, one_smul, hφγ],
end

@[simp]
def inr_comp_desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  inr z ≫ desc z γ hn' φ hφγ = γ :=
begin
  sorry
end

#exit

@[simp]
def ι_desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  twist.ι z ≫ (twist.desc z γ hn' φ hφγ) = γ :=
begin
  ext q,
  simp only [homological_complex.comp_f, ι_f, desc_f, biprod.inr_desc],
end

@[simps]
def lift (z : cocycle F G n) {K : cochain_complex C ℤ} {n' : ℤ} (hn' : n'+n=1)
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
