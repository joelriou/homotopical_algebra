/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.hom_complex
import for_mathlib.algebra.homology.bounded_above

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace cochain_complex

namespace hom_complex

variables {C : Type*} [category C] [preadditive C]

variables {F G K : cochain_complex C ℤ} {n : ℤ} (z : cocycle F G n) {m : ℤ} [∀ p, has_binary_biproduct (F.X (p+1-n)) (G.X p)]
include z

namespace twist

@[protected, simp]
def δ (p q : ℤ) :
  biprod (F.X (p+1-n)) (G.X p) ⟶ biprod (F.X (q+1-n)) (G.X q) :=
begin
  refine biprod.desc (biprod.lift (ε (n+1) • F.d (p+1-n) (q+1-n)) _) (biprod.lift 0 (G.d p q)),
  by_cases p+1 = q,
  { exact (z : cochain F G n).v (p+1-n) q (show q=(p+1-n)+n, by linarith), },
  { exact 0, },
end

end twist

@[simps]
def twist : cochain_complex C ℤ :=
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

omit z

lemma is_bounded_above (z : cocycle F G n) (hF : F.is_bounded_above) (hG : G.is_bounded_above) :
  (twist z).is_bounded_above :=
begin
  cases hF with r hr,
  cases hG with s hs,
  use max (r+n-1) s,
  intros i hi,
  dsimp only [twist],
  rw is_zero.iff_of_biprod,
  split,
  { apply hr,
    have h := lt_of_le_of_lt (le_max_left _ _) hi,
    linarith, },
  { apply hs,
    exact lt_of_le_of_lt (le_max_right _ _) hi, },
end

include z
def inl {n₀ : ℤ} (hn₀ : n₀+1=n) : cochain F (twist z) n₀ :=
cochain.mk (λ p q hpq, (cochain.of_hom (𝟙 F)).v p (q+1-n) (by linarith) ≫ biprod.inl)

def inr : G ⟶ twist z := { f := λ p, biprod.inr, }

def fst {n₁ : ℤ} (hn₁ : n+n₁=1) : cocycle (twist z) F n₁ :=
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

def snd : cochain (twist z) G 0 :=
cochain.mk (λ p q hpq, biprod.snd ≫ (cochain.of_hom (𝟙 G)).v p q hpq)

@[simp]
lemma inl_comp_fst {n₀ n₁ : ℤ} (hn₀ : n₀+1=n) (hn₁ : n+n₁=1) :
  (inl z hn₀).comp ↑(fst z hn₁) (show 0=n₀+n₁, by linarith) = cochain.of_hom (𝟙 F) :=
begin
  ext,
  dsimp [cochain.comp, cochain.mk, cochain.v, cochain.of_hom, cochain.of_homs, inl, fst],
  simp only [id_comp, assoc, biprod.inl_fst_assoc, eq_to_hom_trans, eq_to_hom_refl],
end

@[simp]
lemma inl_comp_snd {n₀ : ℤ} (hn₀ : n₀+1=n) :
  (inl z hn₀).comp (snd z) (add_zero n₀).symm = 0 :=
begin
  ext,
  simp only [inl, snd, cochain.comp, cochain.mk, cochain.v, cochain.of_hom, cochain.of_homs,
    assoc, biprod.inl_snd_assoc, zero_comp, comp_zero, cochain.zero_v],
end

@[simp]
lemma inr_comp_fst {n₁ : ℤ} (hn₁ : n+n₁=1) :
  (cochain.of_hom (inr z)).comp (fst z hn₁ : cochain (twist z) F n₁) (zero_add n₁).symm = 0 :=
begin
  ext,
  simp only [inr, fst, cochain.zero_cochain_comp, cochain.of_hom_v, cocycle.mk_coe,
    cochain.mk_v, biprod.inr_fst_assoc, zero_comp, cochain.zero_v],
end

@[simp]
lemma inr_comp_snd :
  (cochain.of_hom (inr z)).comp (snd z) (add_zero 0).symm = cochain.of_hom (𝟙 G) :=
begin
  ext,
  simp only [inr, snd, cochain.comp_zero_cochain, cochain.mk_v, cochain.of_hom_v,
    homological_complex.id_f, comp_id, biprod.inr_snd],
end

@[simp]
lemma δ_inl {n₀ : ℤ} (hn₀ : n₀+1=n) :
  δ n₀ n (inl z hn₀) = cochain.comp ↑z (cochain.of_hom (inr z)) (add_zero n).symm :=
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
      dif_pos, assoc, biprod.inl_desc, add_comp, biprod.lift_snd,
      linear.smul_comp, biprod.inl_snd, comp_zero, smul_zero, cochain.comp_zero_cochain,
      cochain.of_hom_v, biprod.inr_snd, comp_id, id_comp,
      cochain.zero_cochain_comp' _ _ p (q-1+1-n) q, homological_complex.id_f], },
end

@[simp]
lemma δ_snd {n₁ : ℤ} (hn₁ : n+n₁=1) :
  δ 0 1 (snd z) = -cochain.comp (fst z hn₁ : cochain (twist z) F n₁) (↑z) (show 1 = n₁+n, by rw [← hn₁, add_comm]) :=
begin
  ext1,
  simp only [δ_v 0 1 (zero_add 1) _ p q hpq p q (by linarith) hpq, fst, snd, zero_add, ε_1,
    cochain.mk_v, cochain.of_hom_v, homological_complex.id_f, comp_id, neg_zsmul, one_zsmul,
    cochain.neg_v, cocycle.mk_coe, twist_d, twist.δ,
    cochain.comp_v _ _ (show 1=n₁+n, by linarith) p (p+1-n) q (by linarith) (by linarith)],
  ext,
  { simp only [dif_pos hpq.symm, zero_add, comp_add, biprod.inl_snd_assoc, zero_comp,
      comp_neg, biprod.inl_desc_assoc, biprod.lift_snd, biprod.inl_fst_assoc], },
  { simp only [neg_zero, comp_add, biprod.inr_snd_assoc, comp_neg, biprod.inr_desc_assoc,
      biprod.lift_snd, add_right_neg, biprod.inr_fst_assoc, zero_comp], },
end

lemma id_eq {n₀ n₁ : ℤ} (hn₀ : n₀+1=n)  (hn₁ : n+n₁=1) : cochain.of_hom (𝟙 (twist z)) =
cochain.comp ↑(fst z hn₁) (inl z hn₀) (show 0=n₁+n₀, by linarith) +
cochain.comp (snd z) (cochain.of_hom (inr z)) (zero_add 0).symm :=
begin
  ext1,
  simpa only [fst, inl, snd, inr, cochain.add_v,
    cochain.comp_v _ _ (show 0 = n₁+n₀, by linarith) p (p+1-n) p (by linarith) (by linarith),
    cochain.of_hom_v, homological_complex.id_f, cocycle.mk_coe, cochain.mk_v,
    comp_id, id_comp, cochain.comp_zero_cochain, biprod.total],
end

lemma cochain_ext (y₁ y₂ : cochain (twist z) K m) {n₀ n₁ : ℤ} (hn₀ : n₀+1=n)
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

def desc_cochain {m m₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
  (hm₁ : m₁+1=n+m) : cochain (twist z) K m :=
cochain.comp ↑(fst z (show n+(m-m₁) = 1, by linarith)) y₁ (eq_add_of_sub_eq rfl : m=(m-m₁)+m₁) +
  cochain.comp (snd z) y₂ (zero_add m).symm

lemma desc_cochain_eq {m m₁ n₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
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

lemma inl_comp_desc_cochain {m m₁ n₀ : ℤ} (y₁ : cochain F K m₁)
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

lemma inr_comp_desc_cochain {m m₁ : ℤ} (y₁ : cochain F K m₁)
  (y₂ : cochain G K m) (hm₁ : m₁+1=n+m) :
  cochain.comp (cochain.of_hom (inr z)) (desc_cochain z y₁ y₂ hm₁) (zero_add m).symm = y₂ :=
begin
  simp only [desc_cochain_eq z y₁ y₂ hm₁ (show n+(1-n)=1, by linarith), cochain.comp_add,
    ← cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_snd, cochain.id_comp,
    ← cochain.comp_assoc_of_first_is_zero_cochain, inr_comp_fst, cochain.zero_comp, zero_add],
end

lemma δ_desc_cochain {m m₁ m₂ n₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : cochain G K m)
  (hm₁ : m₁+1=n+m) (hn₁ : n+n₁=1) (hm₂ : m₁+1=m₂)
  (m' : ℤ) (hm' : m+1=m') :
  δ m m' (desc_cochain z y₁ y₂ hm₁) =
  cochain.comp (fst z hn₁ : cochain (twist z) F n₁) (δ m₁ m₂ y₁ +
    ε (m+1) • cochain.comp ↑z y₂ (show m₂ = n+m, by linarith)) (show m' = n₁+m₂, by linarith) +
  cochain.comp (snd z) (δ m m' y₂) (zero_add m').symm :=
begin
  simp only [desc_cochain_eq z y₁ y₂ hm₁ hn₁, δ_add, cochain.comp_add,
    δ_comp_of_first_is_zero_cochain _ _ _ hm', δ_snd z hn₁,
    δ_comp ↑(fst z hn₁) y₁ (show m = n₁+m₁, by linarith) _ m₂ m' hm' rfl hm₂,
    cochain.comp_zsmul, cochain.neg_comp, zsmul_neg, ε_add, ε_1, mul_neg, mul_one,
    neg_zsmul, cochain.comp_neg, cocycle.δ_eq_zero, cochain.zero_comp, zsmul_zero, add_zero,
    add_assoc],
  rw cochain.comp_assoc _ _ _ (show 1=n₁+n, by linarith) (show m₂=n+m, by linarith)
    (show m' = n₁+n+m, by linarith),
  conv_rhs { congr, skip, rw add_comm, },
end

@[simps]
def desc_cocycle {m m₁ n₂ : ℤ} (y₁ : cochain F K m₁) (y₂ : cocycle G K m)
  (hm₁ : m₁+1=n+m) (hn₂ : n₂ = n+m)
  (hy : δ m₁ n₂ y₁ = ε m • cochain.comp (z : cochain F G n) (y₂ : cochain G K m) hn₂) :
  cocycle (twist z) K m :=
cocycle.mk (desc_cochain z y₁ ↑y₂ hm₁) _ rfl
begin
  simp only [δ_desc_cochain z y₁ ↑y₂ hm₁ (show n+(1-n)=1, by linarith) (show m₁+1=n₂, by linarith) _ rfl,
    cocycle.δ_eq_zero, cochain.comp_zero, add_zero, hy, ε_add, ε_1, mul_neg, mul_one, neg_zsmul,
    add_right_neg, cochain.comp_zero],
end

lemma inr_comp_desc_cocycle {m m₁ n₂ : ℤ} (y₁ : cochain F K m₁) (y₂ : cocycle G K m)
  (hm₁ : m₁+1=n+m) (hn₂ : n₂ = n+m)
  (hy : δ m₁ n₂ y₁ = ε m • cochain.comp (z : cochain F G n) (y₂ : cochain G K m) hn₂) :
  cochain.comp (cochain.of_hom (inr z)) (desc_cocycle z y₁ y₂ hm₁ hn₂ hy : cochain (twist z) K m)
    (zero_add m).symm = y₂ :=
by simp only [desc_cocycle, cocycle.mk_coe, inr_comp_desc_cochain]

@[simps]
def desc_hom_as_cocycle {m₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : G ⟶ K)(hm₁ : m₁+1=n)
  (hy : δ m₁ n y₁ = cochain.comp (z : cochain F G n) (cochain.of_hom y₂) (add_zero n).symm) :
  cocycle (twist z) K 0 :=
begin
  apply desc_cocycle z y₁ (cocycle.of_hom y₂) (by linarith) (add_zero n).symm,
  simpa only [hy, ε_0, one_zsmul],
end

@[simps]
def desc {m₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : G ⟶ K)
  (hm₁ : m₁+1=n)
  (hy : δ m₁ n y₁ = cochain.comp (z : cochain F G n) (cochain.of_hom y₂) (add_zero n).symm) :
  twist z ⟶ K :=
cocycle.hom_of (desc_hom_as_cocycle z y₁ y₂ hm₁ hy)

@[simp]
lemma inr_comp_desc {m₁ : ℤ} (y₁ : cochain F K m₁) (y₂ : G ⟶ K)
  (hm₁ : m₁+1=n)
  (hy : δ m₁ n y₁ = cochain.comp (z : cochain F G n) (cochain.of_hom y₂) (add_zero n).symm) :
  inr z ≫ desc z y₁ y₂ hm₁ hy = y₂ :=
begin
  apply (cocycle.equiv_hom G K).to_equiv.injective,
  ext1,
  dsimp [cocycle.equiv_hom],
  simp only [cocycle.of_hom, cocycle.mk_coe, cochain.of_hom_comp, desc,
    cocycle.cochain_of_hom_hom_of_eq_coe, desc_hom_as_cocycle_coe, inr_comp_desc_cochain],
end



def lift_cochain {m₁ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m)
  (hm : m+1=m₁+n) : cochain K (twist z) m :=
cochain.comp y₁ (inl z (show (n-1)+1=n, by linarith)) (show m=m₁+(n-1), by linarith) +
  cochain.comp y₂ (cochain.of_hom (inr z)) (add_zero m).symm

lemma lift_cochain_eq {m₁ n₀ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m) (hm : m+1=m₁+n)
  (hn₀ : n₀+1=n) : lift_cochain z y₁ y₂ hm =
cochain.comp y₁ (inl z hn₀) (begin
  suffices : m+1=m₁+n₀+1,
  { simpa only [add_left_inj] using this, },
  rw [hm, ← hn₀, add_assoc],
end) + cochain.comp y₂ (cochain.of_hom (inr z)) (add_zero m).symm :=
begin
  have eq : n₀ = n-1 := by linarith,
  subst eq,
  refl,
end

lemma lift_cochain_v {m₁ n₀ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m)
  (hm : m+1=m₁+n) (hn₀ : n₀+1 = n) (p q : ℤ) (hpq : q = p + m) (p' : ℤ) (hp' : p' = p + m₁):
  (lift_cochain z y₁ y₂ hm).v p q hpq =
    y₁.v p p' hp' ≫ (inl z hn₀).v p' q (by rw [hpq, hp', add_assoc, add_right_inj,
      ← add_left_inj (1 : ℤ), hm, ← hn₀, add_assoc]) +
    y₂.v p q hpq ≫ (inr z).f q :=
begin
  have hn₀' : n₀ = n-1 := by linarith,
  substs hn₀' hp' hpq,
  dsimp [lift_cochain, cochain.comp],
  simp only [cochain.of_hom_v],
end

@[simp]
lemma lift_cochain_comp_fst {m₁ n₁ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m) (hm : m+1=m₁+n)
  (hn₁ : n+n₁=1) : cochain.comp (lift_cochain z y₁ y₂ hm) ↑(fst z hn₁)
    (show m₁=m+n₁, by { suffices : m₁+n = m+n₁+n,
    { simpa only [add_left_inj] using this,},
    rw [← hm, ← hn₁, add_comm n, add_assoc]}) = y₁ :=
begin
  simp only [lift_cochain, cochain.add_comp,
    cochain.comp_assoc _ _ _ (show m=m₁+(n-1), by linarith) (show 0=n-1+n₁, by linarith)
    (show m₁=_, by linarith), inl_comp_fst, cochain.comp_id, add_zero,
    cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst, cochain.comp_zero],
end

@[simp]
lemma lift_cochain_comp_snd {m₁ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m) (hm : m+1=m₁+n) :
  cochain.comp (lift_cochain z y₁ y₂ hm) (snd z) (add_zero m).symm = y₂ :=
by simp only [lift_cochain, cochain.add_comp, cochain.comp_assoc_of_third_is_zero_cochain,
    inl_comp_snd, cochain.comp_zero, zero_add, inr_comp_snd, cochain.comp_id]

lemma δ_lift_cochain {m₁ n₀ m₂ : ℤ} (y₁ : cochain K F m₁) (y₂ : cochain K G m) (hm : m+1=m₁+n)
  (hn₀ : n₀+1=n) (hm₂ : m₁+1=m₂) (m' : ℤ) (hm' : m+1=m') :
  δ m m' (lift_cochain z y₁ y₂ hm) =
    ε n₀ • cochain.comp (δ m₁ m₂ y₁) (inl z hn₀)
    (by rw [← hm', ← hm₂, hm, ← hn₀, add_comm n₀ 1, add_assoc]) +
  cochain.comp (δ m m' y₂ + cochain.comp y₁ ↑z (by rw [← hm', hm]))
    (cochain.of_hom (inr z)) (add_zero m').symm :=
begin
  simp only [lift_cochain_eq z y₁ y₂ hm hn₀, δ_add,
    δ_comp y₁ (inl z hn₀) (show m = m₁+n₀, by linarith) m₂ n m' hm' hm₂ hn₀,
    δ_comp_of_second_is_zero_cochain _ _ _ hm', δ_inl, cocycle.δ_cochain_of_hom,
    cochain.comp_zero, zero_add, cochain.comp_assoc_of_third_is_zero_cochain,
    cochain.add_comp],
  conv_lhs { rw [add_assoc, add_comm, add_assoc], },
end

def lift_cocycle {m₁ n₀ : ℤ} (y₁ : cocycle K F m₁) (y₂ : cochain K G m) (hm : m+1=m₁+n)
  (hn₀ : n₀+1=n) (m' : ℤ) (hm' : m+1=m')
  (hy : δ m m' y₂ + cochain.comp (y₁ : cochain K F m₁) ↑z (show m'=m₁+n, by rw [← hm', hm]) = 0) :
  cocycle K (twist z) m := cocycle.mk (lift_cochain z ↑y₁ y₂ hm) m' hm'
(by simp only [δ_lift_cochain z ↑y₁ y₂ hm hn₀ rfl m' hm', cocycle.δ_eq_zero, cochain.zero_comp,
    zsmul_zero, zero_add, hy])

@[simps]
def lift_hom_as_cocycle {m₁ n₀ : ℤ} (y₁ : cocycle K F m₁) (y₂ : cochain K G 0) (hm : m₁+n=1)
  (hn₀ : n₀+1=n)
  (hy : δ 0 1 y₂ + cochain.comp (y₁ : cochain K F m₁) ↑z hm.symm = 0) : cocycle K (twist z) 0 :=
lift_cocycle z y₁ y₂ (show 0+1 = m₁+n, by linarith) hn₀ 1 (zero_add 1) hy

@[simps]
def lift {m₁ n₀ : ℤ} (y₁ : cocycle K F m₁) (y₂ : cochain K G 0) (hm : m₁+n=1)
  (hn₀ : n₀+1=n)
  (hy : δ 0 1 y₂ + cochain.comp (y₁ : cochain K F m₁) ↑z hm.symm = 0) :
  K ⟶ twist z :=
cocycle.hom_of (lift_hom_as_cocycle z y₁ y₂ hm hn₀ hy)

lemma cochain_ext' (y₁ y₂ : cochain K (twist z) m) {n₁ m₁ : ℤ} (hn₁ : n+n₁=1) (hm₁ : m₁ = m+n₁) :
  y₁ = y₂ ↔ cochain.comp y₁ (fst z hn₁ : cochain (twist z) F n₁) hm₁
      = cochain.comp y₂ (fst z hn₁ : cochain (twist z) F n₁) hm₁ ∧
  cochain.comp y₁ (snd z) (add_zero m).symm =
  cochain.comp y₂ (snd z) (add_zero m).symm :=
begin
  split,
  { intro h, rw h, tauto, },
  { rintro ⟨hl, hr⟩,
    suffices : cochain.comp y₁ (cochain.of_hom (𝟙 _)) (add_zero m).symm =
      cochain.comp y₂ (cochain.of_hom (𝟙 _)) (add_zero m).symm,
    { ext1,
      simpa only [cochain.comp_id] using cochain.congr_v this p q hpq, },
    simp only [id_eq z (show n-1+1=n, by linarith) hn₁, cochain.add_comp,
      cochain.comp_add],
    simp only [← cochain.comp_assoc_of_second_is_zero_cochain,
      ← cochain.comp_assoc _ _ _ hm₁ (show 0=n₁+(n-1), by linarith)
      (show m=m+n₁+(n-1), by linarith), hl, hr], },
end

lemma of_d_eq (n₁ n₂ n₃ : ℤ) (hn₁ : n + n₁ = 1) (hn₂ : n₂ = n₁+1) (hn₃ : n₃+1=n) : cochain.of_d (twist z) =
  ε (n+1) • ((fst z hn₁ : cochain (twist z) F n₁).comp (cochain.of_d F) hn₂).comp (inl z hn₃)
    (by rw [← hn₁, hn₂, ← hn₃, add_comm n₃, add_assoc, add_comm n₃, ← add_assoc, add_comm n₁]) +
    ((fst z hn₁ : cochain (twist z) F n₁).comp (z : cochain F G n) (show 1 = n₁ + n, by rw [← hn₁, add_comm])).comp
      (cochain.of_hom (inr z)) (add_zero 1).symm +
    ((snd z).comp (cochain.of_d G) (zero_add 1).symm).comp (cochain.of_hom (inr z)) (add_zero 1).symm :=
begin
  rw cochain_ext z (cochain.of_d (twist z)) _ hn₃ hn₃.symm,
  split,
  { simp only [cochain.comp_add, cochain.comp_zsmul],
    simp only [← cochain.comp_assoc_of_third_is_zero_cochain,
      ← cochain.comp_assoc_of_second_is_zero_cochain, inl_comp_snd, inl_comp_fst, cochain.id_comp,
      ← cochain.comp_assoc (inl z hn₃) _ _ (show 1 = n₃+n₂, by linarith) _ (show n = n₃+n₂+n₃, by linarith),
      ← cochain.comp_assoc (inl z hn₃) _ _ (show 0 = n₃ + n₁, by linarith) _ (show 1 = n₃ + n₁ + 1, by linarith),
      ← cochain.comp_assoc (inl z hn₃) _ _ (show 0 = n₃ + n₁, by linarith) (show 1 = n₁ + n, by linarith)
      (show n = n₃+n₁+n, by linarith), cochain.zero_comp, add_zero,
      cochain_ext' z _ _ hn₁ (show 1 = n+n₁, by linarith)],
    split,
    { simp only [cochain.add_comp, cochain.zsmul_comp,
        cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst, cochain.comp_zero, inl_comp_fst,
        cochain.comp_assoc _ (inl z hn₃) _ (show n = 1+n₃, by linarith) (show 0 = n₃ + n₁, by linarith)
        (show 1 = 1 + n₃ + n₁, by linarith), add_zero, cochain.comp_id],
      ext p q hpq,
      dsimp [inl, fst, cochain.comp],
      simp only [twist.δ, cochain.of_d_v, twist_d, assoc, biprod.inl_desc, biprod.lift_fst_assoc,
        linear.smul_comp, cochain.d_comp_of_hom_v, homological_complex.id_f, comp_id,
        linear.comp_smul, cochain.of_hom_v_comp_d, id_comp], },
    { simp only [cochain.comp_assoc_of_third_is_zero_cochain, cochain.add_comp, cochain.zsmul_comp,
        inl_comp_snd, inr_comp_snd, cochain.comp_zero, zsmul_zero, zero_add, cochain.comp_id],
      ext p q hpq,
      have hp : ∃ (p' : ℤ), p = p' + 1 -n := ⟨p+n-1, by linarith⟩,
      obtain ⟨p', hp'⟩ := hp,
      subst hp',
      rw cochain.comp_v _ _ hn₃.symm (p'+1-n) p' q (by linarith) (by linarith),
      dsimp [inl, snd],
      simp only [cochain.of_hom_v, homological_complex.id_f, id_comp, cochain.comp_zero_cochain,
        twist.δ, cochain.of_d_v, twist_d, cochain.mk_v, comp_id, biprod.inl_desc_assoc,
        biprod.lift_snd, dif_pos (show p'+1 = q, by linarith)], }, },
  { simp only [ε_succ, neg_smul,
      cochain.comp_add, cochain.comp_neg, cochain.comp_zsmul,
      ← cochain.comp_assoc_of_first_is_zero_cochain, inr_comp_fst, cochain.zero_comp, zsmul_zero,
      zero_add, neg_zero, inr_comp_snd, cochain.id_comp,
      cochain_ext' z _ _ hn₁ (show n₂ = 1 + n₁, by linarith)],
    split,
    { rw [cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst, cochain.comp_zero],
      ext p q hpq,
      simp only [cochain.comp_assoc_of_first_is_zero_cochain, cochain.zero_cochain_comp,
        cochain.of_hom_v, cochain.zero_v,
        cochain.comp_v _ _ (show n₂ = 1 + n₁, by linarith) p (p+1) q rfl (by linarith)],
      dsimp [inr, fst],
      simp only [twist.δ, cochain.of_d_v, twist_d, biprod.inr_desc_assoc,
        biprod.lift_fst_assoc, zero_comp], },
    { rw [cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_snd, cochain.comp_id],
      ext p q hpq,
      dsimp [inr, snd],
      simp only [cochain.comp_assoc_of_third_is_zero_cochain, cochain.zero_cochain_comp,
        cochain.of_hom_v, cochain.comp_zero_cochain, twist.δ, cochain.of_d_v, twist_d,
        cochain.mk_v, homological_complex.id_f, comp_id, biprod.inr_desc_assoc,
        biprod.lift_snd], }, },
end

end twist

end hom_complex

end cochain_complex
