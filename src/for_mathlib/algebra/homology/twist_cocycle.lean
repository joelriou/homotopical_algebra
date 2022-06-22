/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.hom_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace cochain_complex

namespace hom_complex

variables {C : Type*} [category C] [preadditive C]

variables {F G K : cochain_complex C ℤ} {n m : ℤ} [∀ p, has_binary_biproduct (F.X (p+1-n)) (G.X p)]

namespace twist

@[protected, simp]
def δ (z : cocycle F G n) (p q : ℤ) :
  biprod (F.X (p+1-n)) (G.X p) ⟶ biprod (F.X (q+1-n)) (G.X q) :=
begin
  refine biprod.desc (biprod.lift (ε (n+1) • F.d (p+1-n) (q+1-n)) _) (biprod.lift 0 (G.d p q)),
  by_cases p+1 = q,
  { exact z.1.v (p+1-n) q (show q=(p+1-n)+n, by linarith), },
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
      have hz₂ := cochain.congr_v hz₁ (i+1-n) (i+2) (by linarith),
      simp only [δ_v n (n+1) rfl _ (i+1-n) (i+2) (by linarith) (i+1) (i+1+1-n)
        (by linarith) (by linarith), cochain.zero_v] at hz₂,
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

def inl (z : cocycle F G n) {n₀ : ℤ} (hn₀ : n₀+1=n) : cochain F (twist z) n₀ :=
cochain.mk (λ p q hpq, (cochain.of_hom (𝟙 F)).v p (q+1-n) (by linarith) ≫ biprod.inl)

def inr (z : cocycle F G n) : G ⟶ twist z := { f := λ p, biprod.inr, }

def fst (z : cocycle F G n) {n₁ : ℤ} (hn₁ : n+n₁=1) : cocycle (twist z) F n₁ :=
cocycle.mk (cochain.mk (λ p q hpq, biprod.fst ≫
  (cochain.of_hom (𝟙 F)).v (p+1-n) q (show q=p+1-n+0, by linarith))) (n₁+1) rfl
begin
  have hn₁' : n₁ = 1-n := by linarith,
  subst hn₁',
  ext1,
  simp only [δ_v (1-n) (1-n+1) rfl _ p q hpq (p+1-n) (p+1) (by linarith) rfl,
    cochain.mk_v, cochain.of_hom_v, homological_complex.id_f, comp_id, twist_d, twist.δ, dif_pos,
      cochain.zero_v],
  ext,
  { have hq : q = p+1+1-n := by linarith,
    subst hq,
    have eq : ε (1-n+1) * ε (n+1) = ε ((1 : ℤ) + 1 + 1) := by { rw ← ε_add, congr' 1, linarith, },
    have eq' : ε ((1 : ℤ)+1+1) = -1 := by { simp only [ε_succ, ε_1, neg_neg], },
    simp only [biprod.inl_fst_assoc, biprod.inl_desc_assoc, biprod.lift_fst, comp_add,
      cochain.of_hom_v, homological_complex.id_f, comp_zsmul, comp_id, comp_zero, smul_smul,
      eq, eq', neg_smul, one_zsmul, add_right_neg], },
  { simp only [zero_add, neg_eq_zero, comp_add, biprod.inr_fst_assoc, zero_comp,
      linear.comp_smul, biprod.inr_desc_assoc, biprod.lift_fst_assoc, smul_zero, comp_zero], },
end

def snd (z : cocycle F G n) : cochain (twist z) G 0 :=
cochain.mk (λ p q hpq, biprod.snd ≫ (cochain.of_hom (𝟙 G)).v p q hpq)

@[simp]
lemma inl_comp_fst (z : cocycle F G n) {n₀ n₁ : ℤ} (hn₀ : n₀+1=n) (hn₁ : n+n₁=1) :
  (inl z hn₀).comp ↑(fst z hn₁) (show 0=n₀+n₁, by linarith) = cochain.of_hom (𝟙 F) :=
begin
  ext,
  dsimp [cochain.comp, cochain.mk, cochain.v, cochain.of_hom, cochain.of_homs, inl, fst],
  simp only [id_comp, assoc, biprod.inl_fst_assoc, eq_to_hom_trans, eq_to_hom_refl],
end

@[simp]
lemma inl_comp_snd (z : cocycle F G n) {n₀ : ℤ} (hn₀ : n₀+1=n) :
  (inl z hn₀).comp (snd z) (add_zero n₀).symm = 0 :=
begin
  ext,
  simp only [inl, snd, cochain.comp, cochain.mk, cochain.v, cochain.of_hom, cochain.of_homs,
    assoc, biprod.inl_snd_assoc, zero_comp, comp_zero, cochain.zero_v],
end

@[simp]
lemma inr_comp_fst (z : cocycle F G n) {n₁ : ℤ} (hn₁ : n+n₁=1) :
  (cochain.of_hom (inr z)).comp (fst z hn₁ : cochain (twist z) F n₁) (zero_add n₁).symm = 0 :=
begin
  ext,
  simp only [inr, fst, cochain.zero_cochain_comp, cochain.of_hom_v, cocycle.mk_coe,
    cochain.mk_v, biprod.inr_fst_assoc, zero_comp, cochain.zero_v],
end

@[simp]
lemma inr_comp_snd (z : cocycle F G n) :
  (cochain.of_hom (inr z)).comp (snd z) (add_zero 0).symm = cochain.of_hom (𝟙 G) :=
begin
  ext,
  simp only [inr, snd, cochain.comp_zero_cochain, cochain.mk_v, cochain.of_hom_v,
    homological_complex.id_f, comp_id, biprod.inr_snd],
end

@[simp]
lemma δ_inl (z : cocycle F G n) {n₀ : ℤ} (hn₀ : n₀+1=n) :
  δ n₀ n (inl z hn₀) = cochain.comp z.1 (cochain.of_hom (inr z)) (add_zero n).symm :=
begin
  ext1,
  simp only [δ_v n₀ n hn₀ (inl z hn₀) p q hpq _ _ rfl rfl, twist_d, twist.δ],
  ext,
  { simp only [← hn₀, inl, cochain.mk_v, ε_succ, neg_neg, assoc, biprod.inl_desc, neg_smul,
      add_comp, biprod.lift_fst, comp_zsmul, cochain.of_hom_v_comp_d,
      homological_complex.id_f, id_comp, neg_comp, zsmul_comp, biprod.inl_fst, comp_id,
      cochain.d_comp_of_hom_v, add_right_neg, cochain.comp_zero_cochain, cochain.of_hom_v,
      inr, biprod.inr_fst, comp_zero], },
  { simp only [inl, inr, add_zero, sub_add_cancel, eq_self_iff_true, cochain.mk_v,
      subtype.val_eq_coe, dif_pos, assoc, biprod.inl_desc, add_comp, biprod.lift_snd,
      linear.smul_comp, biprod.inl_snd, comp_zero, smul_zero, cochain.comp_zero_cochain,
      cochain.of_hom_v, biprod.inr_snd, comp_id, id_comp,
      cochain.zero_cochain_comp' _ _ p (q-1+1-n) q, homological_complex.id_f], },
end

@[simp]
lemma δ_snd (z : cocycle F G n) {n₁ : ℤ} (hn₁ : n+n₁=1) :
  δ 0 1 (snd z) = -cochain.comp (fst z hn₁).1 (↑z) (show 1 = n₁+n, by rw [← hn₁, add_comm]) :=
begin
  ext1,
  simp only [δ_v 0 1 (zero_add 1) _ p q hpq p q (by linarith) hpq, fst, snd, zero_add, ε_1,
    cochain.mk_v, cochain.of_hom_v, homological_complex.id_f, comp_id, neg_zsmul, one_zsmul,
    subtype.val_eq_coe, cochain.neg_v, cocycle.mk_coe, twist_d, twist.δ,
    cochain.comp_v _ _ (show 1=n₁+n, by linarith) p (p+1-n) q (by linarith) (by linarith)],
  ext,
  { simp only [dif_pos hpq.symm, zero_add, comp_add, biprod.inl_snd_assoc, zero_comp,
      comp_neg, biprod.inl_desc_assoc, biprod.lift_snd, biprod.inl_fst_assoc], },
  { simp only [neg_zero, comp_add, biprod.inr_snd_assoc, comp_neg, biprod.inr_desc_assoc,
      biprod.lift_snd, add_right_neg, biprod.inr_fst_assoc, zero_comp], },
end

def id_eq (z : cocycle F G n) {n₀ n₁ : ℤ} (hn₀ : n₀+1=n)  (hn₁ : n+n₁=1) : cochain.of_hom (𝟙 (twist z)) =
cochain.comp ↑(fst z hn₁) (inl z hn₀) (show 0=n₁+n₀, by linarith) +
cochain.comp (snd z) (cochain.of_hom (inr z)) (zero_add 0).symm :=
begin
  ext1,
  simpa only [fst, inl, snd, inr, cochain.add_v,
    cochain.comp_v _ _ (show 0 = n₁+n₀, by linarith) p (p+1-n) p (by linarith) (by linarith),
    cochain.of_hom_v, homological_complex.id_f, cocycle.mk_coe, cochain.mk_v,
    comp_id, id_comp, cochain.comp_zero_cochain, biprod.total],
end

lemma cochain_ext (z : cocycle F G n) (y₁ y₂ : cochain (twist z) K m) {n₀ n₁ : ℤ} (hn₀ : n₀+1=n)
  (hn₁ : n₁ = n₀+m) :
  y₁ = y₂ ↔ cochain.comp (inl z hn₀) y₁ hn₁ = cochain.comp (inl z hn₀) y₂ hn₁ ∧
    cochain.comp (cochain.of_hom (inr z)) y₁ (zero_add m).symm =
      cochain.comp (cochain.of_hom (inr z)) y₂ (zero_add m).symm :=
begin
  split,
  { intro h, rw h, tauto, },
  { rintro ⟨hl, hr⟩,
    suffices : cochain.comp (cochain.of_hom (𝟙 _)) y₁ (zero_add m).symm =
      cochain.comp (cochain.of_hom (𝟙 _)) y₂ (zero_add m).symm,
    { ext1,
      simpa only [cochain.id_comp] using cochain.congr_v this p q hpq, },
    simp only [id_eq z hn₀ (show n+(-n₀)=1, by linarith), cochain.add_comp,
      cochain.comp_assoc_of_second_is_zero_cochain,
      cochain.comp_assoc _ _ _ (show 0=-n₀+n₀, by linarith) (show n₁=n₀+m, by linarith)
      (show m=-n₀+n₀+m, by linarith), hl, hr], }
end

def desc_cochain (z : cocycle F G n) {m m₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
  (hm₁ : m₁+1=n+m) : cochain (twist z) K m :=
cochain.comp ↑(fst z (show n+(m-m₁) = 1, by linarith)) y₁ (eq_add_of_sub_eq rfl : m=(m-m₁)+m₁) +
  cochain.comp (snd z) y₂ (zero_add m).symm

def desc_cochain_eq (z : cocycle F G n) {m m₁ n₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
  (hm₁ : m₁+1=n+m) (hn₁ : n+n₁=1) : desc_cochain z y₁ y₂ hm₁ =
cochain.comp ↑(fst z hn₁) y₁ (show m = n₁+m₁, begin
  suffices : m+1=n₁+m₁+1,
  { simpa only [add_left_inj] using this, },
  rw [add_assoc, hm₁, ← hn₁, add_comm n₁, add_comm n m, add_assoc],
end) + cochain.comp (snd z) y₂ (zero_add m).symm :=
begin
  have h : n₁ = m-m₁ := by linarith,
  subst h,
  refl,
end

lemma inl_comp_desc_cochain (z : cocycle F G n) {m m₁ n₀ : ℤ} (y₁ : cochain F K m₁)
  (y₂ : cochain G K m) (hm₁ : m₁+1=n+m) (hn₀ : n₀+1=n) :
  cochain.comp (inl z hn₀) (desc_cochain z y₁ y₂ hm₁) begin
    suffices : m₁+1 = n₀+m+1,
    { simpa only [add_left_inj] using this, },
    rw [add_assoc, hm₁, ← hn₀, add_assoc, add_comm 1 m],
  end = y₁ :=
begin
  simp only [desc_cochain_eq z y₁ y₂ hm₁ (show n+(-n₀)=1, by linarith), cochain.comp_add,
    ← cochain.comp_assoc (inl z hn₀) _ y₁ (show 0=n₀+(-n₀), by linarith)
      (show m= _, by linarith) (show m₁=_, by linarith),
    ← cochain.comp_assoc_of_second_is_zero_cochain, add_zero,
    inl_comp_fst, inl_comp_snd, cochain.id_comp, cochain.zero_comp],
end

lemma inr_comp_desc_cochain (z : cocycle F G n) {m m₁ n₀: ℤ} (y₁ : cochain F K m₁)
  (y₂ : cochain G K m) (hm₁ : m₁+1=n+m) :
  cochain.comp (cochain.of_hom (inr z)) (desc_cochain z y₁ y₂ hm₁) (zero_add m).symm = y₂ :=
begin
  simp only [desc_cochain_eq z y₁ y₂ hm₁ (show n+(1-n)=1, by linarith), cochain.comp_add,
    ← cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_snd, cochain.id_comp,
    ← cochain.comp_assoc_of_first_is_zero_cochain, inr_comp_fst, cochain.zero_comp, zero_add],
end

lemma δ_desc_cochain (z : cocycle F G n) {m m₁ m₂ n₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
  (hm₁ : m₁+1=n+m)  {n₁ n₂ : ℤ} (hn₁ : n+n₁=1) (hm₂ : m₁+1=m₂)
  (m' : ℤ) (hm' : m+1=m') :
  δ m m' (desc_cochain z y₁ y₂ hm₁) =
  cochain.comp (fst z hn₁ : cochain (twist z) F n₁) (δ m₁ m₂ y₁ +
    ε (m+1) • cochain.comp ↑z y₂ (show m₂ = n+m, by linarith)) (show m' = n₁+m₂, by linarith) +
  cochain.comp (snd z) (δ m m' y₂) (zero_add m').symm :=
begin
  simp only [desc_cochain_eq z y₁ y₂ hm₁ hn₁, δ_add],
  rw cochain_ext z _ _ (show (n-1)+1=n, by linarith),
  split,
  { sorry, },
  { simp only [δ_comp _ _ (show m = n₁ + m₁, by linarith) (n₁+1) m₂ m' hm' rfl hm₂,
      δ_comp_of_first_is_zero_cochain _ _ _ hm', cocycle.δ_eq_zero, δ_snd z hn₁,
      add_zero, cochain.zero_comp, smul_zero, subtype.val_eq_coe,
      cochain.neg_comp, zsmul_neg', neg_smul, cochain.comp_add,
      cochain.comp_neg, cochain.comp_zsmul, ε_succ,
      ← cochain.comp_assoc_of_first_is_zero_cochain,
      inr_comp_fst, zero_add, neg_zero], },
end

#exit
--attribute [reassoc] homological_complex.d_comp_eq_to_hom

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
def desc_cocycle (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' n''' : ℤ}
  (γ : cocycle G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) (m' : ℤ) (hm' : m+1=m') (hn''' : n''' = n'+1)
  (hφ : δ n' n''' φ = ε m • (z.1.comp γ.1 (show n'''=_, by linarith))) : cocycle (twist z) K m :=
cocycle.mk (desc_cochain z γ.1 φ hn') m' hm'
(by simp only [δ_desc_cochain z γ.1 φ hn' m' hm' (show n+(1-n)=1, by linarith) hn''', hφ, neg_smul, add_left_neg,
    cochain.comp_zero, zero_add, cocycle.δ_eq_zero, hε'])

@[simp]
lemma inr_comp_desc_cocycle (z : cocycle F G n) {K : cochain_complex C ℤ} {m n' n''' : ℤ}
  (γ : cocycle G K m) (φ : cochain F K n') (hn' : n'+1 = n+m) (m' : ℤ) (hm' : m+1=m') (hn''' : n''' = n'+1)
  (hφ : δ n' n''' φ = ε m • (z.1.comp γ.1 (show n'''=_, by linarith))) :
  cochain.comp (cochain.of_hom (inr z)) (desc_cocycle z γ φ hn' m' hm' hn''' hφ).1 (zero_add m).symm = γ.1 :=
by simp only [desc_cocycle, cocycle.mk, inr_comp_desc_cochain]

@[simps]
def desc_hom_as_cocycle (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  cocycle (twist z) K 0 :=
begin
  apply desc_cocycle z (cocycle.of_hom γ) φ (by linarith) 1 (zero_add 1) hn'.symm,
  simpa only [hε₀, one_smul, hφγ],
end

@[simps]
def desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  twist z ⟶ K :=
(cocycle.equiv_hom (twist z) K).to_equiv.inv_fun (desc_hom_as_cocycle z γ hn' φ hφγ)

@[simp]
def desc_hom_as_cocycle_compatibility (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  (cocycle.equiv_hom _ _).to_equiv (desc z γ hn' φ hφγ) = desc_hom_as_cocycle z γ hn' φ hφγ :=
by apply equiv.right_inv

@[simp]
def comp_equiv_hom {L : cochain_complex C ℤ} (f : L ⟶ F) (g : F ⟶ G) :
  (cochain.of_hom f).comp ((cocycle.equiv_hom F G).to_equiv g).1 (zero_add 0).symm
    = ((cocycle.equiv_hom L G).to_equiv (f ≫ g)).1 :=
by apply cochain.cochain_of_hom_comp

@[simp]
def inr_comp_desc (z : cocycle F G n) {K : cochain_complex C ℤ}
  (γ : G ⟶ K) {n' : ℤ} (hn' : n'+1 = n) (φ : cochain F K n')
  (hφγ : δ n' n φ = cochain.comp z.1 (cochain.of_hom γ) (add_zero n).symm) :
  inr z ≫ desc z γ hn' φ hφγ = γ :=
begin
  apply (cocycle.equiv_hom G K).to_equiv.injective,
  ext1,
  simpa only [← subtype.val_eq_coe, ← comp_equiv_hom, desc_hom_as_cocycle_compatibility, desc_hom_as_cocycle,
    inr_comp_desc_cocycle],
end

def lift_cochain (z : cocycle F G n) {K : cochain_complex C ℤ} {m p : ℤ}
  (ψ : cochain K F p) (υ : cochain K G m) (hp : m+1=p+n) : cochain K (twist z) m :=
cochain.comp ψ (inl z (sub_add_cancel n 1)) (by linarith) + cochain.comp υ (cochain.of_hom (inr z)) (add_zero m).symm

def lift_cochain_eq (z : cocycle F G n) {K : cochain_complex C ℤ} {m p q : ℤ}
  (ψ : cochain K F p) (υ : cochain K G m)  (hq : q+1=n) (hp : m = p+q) :
lift_cochain z ψ υ (show m+1=p+n, by rw [hp, add_assoc, hq]) =
cochain.comp ψ (inl z hq) hp + cochain.comp υ (cochain.of_hom (inr z)) (add_zero m).symm := rfl

lemma δ_lift_cochain (z : cocycle F G n) {K : cochain_complex C ℤ} {m p q : ℤ}
  (ψ : cochain K F p) (υ : cochain K G m)  (hq : q+1=n) (hp : m =p+q) (m' p' : ℤ) (hm' : m+1=m') (hp' : p+1=p') :
  δ m m' (lift_cochain z ψ υ (show m+1=p+n, by rw [hp, add_assoc, hq])) =
  (cochain.comp ψ z.1 (show m' = p+n, by rw [← hm', hp, add_assoc, hq])).comp (cochain.of_hom (inr z)) (add_zero m').symm +
    ε q • cochain.comp (δ p p' ψ) (inl z hq) (by { rw [← hp', ← hm', hp, add_assoc p 1, add_comm 1 q, add_assoc]}) +
    cochain.comp (δ m m' υ) (cochain.of_hom (inr z)) (add_zero m').symm :=
begin
  simp only [lift_cochain_eq z ψ υ hq hp, δ_comp ψ (inl z hq) hp p' n m' hm' hp' hq,
    δ_inl z hq, ← cochain.comp_assoc ψ z.1 (cochain.of_hom (inr z)) (show m'=_, by linarith) (add_zero n).symm (show m'=_, by linarith),
    δ_comp_cochain_of_hom, δ_add],
end

def lift_cocycle (z : cocycle F G n) {K : cochain_complex C ℤ} {m p : ℤ}
  (ψ : cocycle K F p) (υ : cochain K G m) (m' : ℤ) (hm' : m+1=m') (hpn : m' = p+n)
  (hψυ : δ m m' υ = -cochain.comp ψ.1 z.1 hpn) :
cocycle K (twist z) m := cocycle.mk (lift_cochain z ψ.1 υ (by linarith)) m' hm'
  (by rw [δ_lift_cochain z ψ.1 υ (sub_add_cancel n 1) (by linarith) m' (p+1) hm' rfl, cocycle.δ_eq_zero, cochain.zero_comp, smul_zero, add_zero,
    ← cochain.add_comp, hψυ, add_right_neg, cochain.zero_comp])

def lift (z : cocycle F G n) {K : cochain_complex C ℤ} {p : ℤ}
  (ψ : cocycle K F p) (υ : cochain K G 0) (hpn : p+n=1)
  (hψυ : δ 0 1 υ = -cochain.comp ψ.1 z.1 hpn.symm) : K ⟶ twist z :=
(cocycle.equiv_hom K (twist z)).to_equiv.inv_fun (lift_cocycle z ψ υ 1 (zero_add 1) hpn.symm hψυ)

@[simp]
def lift_hom_as_cocycle_compatibility (z : cocycle F G n) {K : cochain_complex C ℤ} {p : ℤ}
  (ψ : cocycle K F p) (υ : cochain K G 0) (hpn : p+n=1)
  (hψυ : δ 0 1 υ = -cochain.comp ψ.1 z.1 hpn.symm) :
(cocycle.equiv_hom _ _).to_equiv (lift z ψ υ hpn hψυ) = lift_cocycle z ψ υ 1 (zero_add 1) hpn.symm hψυ :=
by apply equiv.right_inv

end twist

end hom_complex

end cochain_complex
