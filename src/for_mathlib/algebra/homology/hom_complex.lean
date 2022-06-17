/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy
import algebra.homology.additive
import algebra.category.Group.abelian
import data.int.parity


noncomputable theory

open category_theory category_theory.preadditive category_theory.limits category_theory.category

universes v u

namespace algebra

namespace homology

variables {C : Type u} [category.{v} C] [preadditive C]
variables (F G : cochain_complex C ℤ)

namespace hom_complex

class has_sign (α : Type*) [add_comm_group α] [has_one α] :=
(ε : α → ℤ) (hε : ∀ x y, ε (x+y) = ε x * ε y) (hε₁ : ε 1 = -1)

def ε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : α → ℤ := s.ε
lemma hε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x y : α) : ε (x+y) = ε x * ε y := by apply s.hε
lemma hε₁ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : ε (1 : α) = -1 := s.hε₁
lemma hε' {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε (x+1) = - ε x := by rw [hε, hε₁, mul_neg, mul_one]
lemma hε₀ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : ε (0 : α) = 1 :=
by simpa only [add_zero, hε₁, neg_mul, one_mul, neg_inj] using (hε (1 : α) 0).symm
lemma hε'' {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε (x-1) = - ε x :=
begin
  have eq := hε (x-1) 1,
  simp only [sub_add_cancel] at eq,
  simp only [eq, hε₁, mul_neg, mul_one, neg_neg],
end
lemma hε₂ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε x * ε x = 1 :=
begin
  have eq := hε x (-x),
  simp only [add_right_neg, hε₀] at eq,
  cases int.eq_one_or_neg_one_of_mul_eq_one eq.symm,
  { rw [h, mul_one], },
  { rw [h, mul_neg, mul_one, neg_neg], },
end

instance : has_sign ℤ :=
{ ε := λ n, begin
    by_cases even n,
    exacts [1, -1],
  end,
  hε := λ x y, begin
    by_cases hx : even x;
    by_cases hy : even y;
    split_ifs;
    try { simp only [mul_neg, mul_one, neg_neg], },
    all_goals { exfalso, },
    { apply h, exact even.add hx hy, },
    { rw ← int.odd_iff_not_even at hy,
      rw int.even_iff_not_odd at h,
      apply h,
      exact even.add_odd hx hy, },
    { rw ← int.odd_iff_not_even at hx,
      rw int.even_iff_not_odd at h,
      apply h,
      exact odd.add_even hx hy, },
    { rw ← int.odd_iff_not_even at hx hy,
      apply h,
      exact odd.add_odd hx hy },
  end,
  hε₁ := begin
    split_ifs,
    { exfalso,
      rw int.even_iff_not_odd at h,
      exact h odd_one, },
    { refl, },
  end, }

def cochain (n : ℤ) := Π q q' (hqq' : q'=q+n), F.X q ⟶ G.X q'

instance (n : ℤ) : add_comm_group (cochain F G n) :=
{ add := λ f₁ f₂ q q' hqq', f₁ q q' hqq' + f₂ q q' hqq',
  zero := λ q q' hqq', 0,
  neg := λ f q q' hqq', -f q q' hqq',
  add_assoc := λ f₁ f₂ f₃, by { ext q q' hqq', apply_rules [add_assoc], },
  add_comm := λ f₁ f₂, by { ext q q' hqq', apply_rules [add_comm], },
  add_left_neg := λ f, by { ext q q' hqq', apply_rules [add_left_neg], },
  zero_add := λ f, by { ext q q' hqq', apply_rules [zero_add], },
  add_zero := λ f, by { ext q q' hqq', apply_rules [add_zero], },
  zsmul := λ n f q q' hqq', n • (f q q' hqq'),
  zsmul_zero' := λ f, by { ext q q' hqq', apply_rules [zero_zsmul], },
  zsmul_succ' := λ n f, by { ext q q' hqq', simpa only [nat.succ_eq_one_add,
    int.of_nat_eq_coe, int.coe_nat_add, add_zsmul, coe_nat_zsmul, one_smul], },
  zsmul_neg' := λ n f, by { ext q q' hqq', rw [← neg_inj, neg_neg, ← neg_zsmul], refl, }, }

namespace cochain

@[simp]
lemma zero_apply (n : ℤ) (q q' : ℤ) (hqq' : q' = q+n) :
  (0 : cochain F G n) q q' hqq' = 0 := rfl

@[simp]
lemma add_apply {n : ℤ} (f₁ f₂ : cochain F G n) (q q' : ℤ) (hqq' : q' = q+n) :
  (f₁ + f₂) q q' hqq' = f₁ q q' hqq' + f₂ q q' hqq' := rfl

@[simp]
lemma sub_apply {n : ℤ} (f : cochain F G n) (q q' : ℤ) (hqq' : q' = q+n) :
  (-f) q q' hqq' = -f q q' hqq' := rfl

@[simp]
lemma zsmul_apply {n : ℤ} (k : ℤ) (f : cochain F G n) (q q' : ℤ) (hqq' : q' = q+n) :
  (k • f) q q' hqq' = k • (f q q' hqq') := rfl

variables {F G}

def of_hom (φ : F ⟶ G) : cochain F G 0 :=
λ q q' hqq', φ.f q ≫ eq_to_hom (by { congr, rw [hqq', add_zero],})

@[simp]
lemma of_hom_eq (φ : F ⟶ G) (q : ℤ) : of_hom φ q q (add_zero q).symm = φ.f q :=
by { dsimp [of_hom], rw comp_id, }

def of_homs (φ : Π n, F.X n ⟶ G.X n) : cochain F G 0 :=
λ q q' hqq', φ q ≫ eq_to_hom (by { congr, rw [hqq', add_zero],})

@[simp]
lemma of_homs_eq (φ : Π n, F.X n ⟶ G.X n) (q : ℤ) : of_homs φ q q (add_zero q).symm = φ q :=
by { dsimp [of_homs], rw comp_id, }

@[simp]
def of_homotopy {φ₁ φ₂ : F ⟶ G} (ho : homotopy φ₁ φ₂) : cochain F G (-1) :=
λ q q' hqq', ho.hom q q'

def comp {K : cochain_complex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂) :
  cochain F K n₁₂ := λ q q' hqq', z₁ q (q+n₁) rfl ≫ z₂ (q+n₁) q' (by linarith)

@[simp]
def comp_eq {K : cochain_complex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂)
  (q q' q'' : ℤ) (h₁ : q'=q+n₁) (h₂ : q'' = q'+n₂) :
  comp z₁ z₂ h q q'' (by { rw [h₂, h₁, h, add_assoc], }) = z₁ q q' h₁ ≫ z₂ q' q'' h₂ :=
by { subst h₁, refl, }

lemma comp_eq' {F G K : cochain_complex C ℤ} (n₁ n₂ : ℤ) (q q₁' q₂' q'' : ℤ) (h₁ : q₁'=q+n₁) (h₂ : q'' = q₁'+n₂) (h₃ : q₁'=q₂')
  (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) :
  z₁ q q₁' h₁ ≫ z₂ q₁' q'' h₂ = z₁ q q₂' (by rw [← h₃, h₁]) ≫ z₂ q₂' q'' (by rw [← h₃, h₂]) :=
by subst h₃

lemma eval' {F G : cochain_complex C ℤ} (n : ℤ) (q₁ q₁' : ℤ) (hqq' : q₁'=q₁+n) (q₂ q₂' : ℤ) (h : q₁=q₂) (h' : q₁' = q₂') (z : cochain F G n) :
  z q₁ q₁' hqq' = eq_to_hom (by rw h) ≫ z q₂ q₂' (by { rw [← h, ← h', hqq'], }) ≫ eq_to_hom (by rw h') :=
begin
  substs h h',
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

@[simp]
def add_comp {K : cochain_complex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ z₁': cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂) :
  comp (z₁+z₁') z₂ h = comp z₁ z₂ h + comp z₁' z₂ h :=
begin
  ext q q' hqq',
  dsimp [comp],
  simp only [add_comp],
end

@[simp]
def comp_add {K : cochain_complex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ z₂': cochain G K n₂) (h : n₁₂ = n₁ + n₂) :
  comp z₁ (z₂+z₂') h = comp z₁ z₂ h + comp z₁ z₂' h :=
begin
  ext q q' hqq',
  dsimp [comp],
  simp only [comp_add],
end

end cochain

variables {F G}

def δ (n m : ℤ) (f : cochain F G n) : cochain F G m := λ q q' hqq',
f q (q+n) rfl ≫ G.d (q+n) q' + ε (n+1) • F.d q (q+m-n) ≫ f (q+m-n) q' (by linarith)

lemma δ_eq (n m : ℤ) (hnm : n+1=m) (q q' : ℤ) (hqq' : q'=q+m)
  (q₁ q₂ : ℤ) (hq₁ : q₁=q'-1) (hq₂ : q₂=q+1) (f : cochain F G n) :
  δ n m f q q' hqq' = f q q₁ (by { rw [hq₁, hqq', ← hnm, ← add_assoc, add_tsub_cancel_right], }) ≫
    G.d q₁ q' + ε (n+1) • F.d q q₂ ≫ f q₂ q'
    (by { rw [hq₂, hqq', ← hnm, add_comm n, add_assoc], }) :=
begin
  have h₁ : q₁ = q+n := by linarith,
  have h₂ : q₂ = q+m-n := by linarith,
  substs h₁ h₂,
  refl,
end
variables (F G)

def δ_hom (n m : ℤ) : cochain F G n →+ cochain F G m :=
{ to_fun := δ n m,
  map_zero' := begin
    ext q q' hqq',
    dsimp [δ],
    simp only [zero_comp, comp_zero, smul_zero,
      add_zero],
  end,
  map_add' := λ f₁ f₂, begin
    ext q q' hqq',
    dsimp [δ],
    simp only [add_comp, comp_add, smul_add],
    abel,
  end, }

def δ_comp {K : cochain_complex C ℤ} {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂)
  (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂+1 = m₁₂) (h₁ : n₁+1 = m₁) (h₂ : n₂+1 = m₂) :
δ n₁₂ m₁₂ (cochain.comp z₁ z₂ h) = cochain.comp z₁ (δ n₂ m₂ z₂) (by linarith) + ε n₂ • cochain.comp (δ n₁ m₁ z₁) z₂ (by linarith) :=
begin
  ext q q' hqq',
  have hqq'' : q' = q+n₁+n₂+1 := by linarith,
  substs h h₁ h₂ h₁₂ hqq'',
  have eq : ε n₂ * ε (n₁+1) = ε (n₁+n₂+1),
  { rw ← hε, congr' 1, linarith, },
  simp only [assoc, cochain.add_apply, cochain.zsmul_apply,
    δ_eq (n₁+n₂) (n₁+n₂+1) rfl q (q+n₁+n₂+1) hqq' (q+n₁+n₂) (q+1) (by linarith) (by linarith),
    cochain.comp_eq z₁ z₂ rfl q (q+n₁) (q+n₁+n₂) rfl rfl,
    cochain.comp_eq z₁ z₂ rfl (q+1) (q+n₁+1) (q+n₁+n₂+1) (by linarith) (by linarith),
    cochain.comp_eq (δ n₁ (n₁+1) z₁) z₂ (show n₁+n₂+1=n₁+1+n₂, by linarith) q (q+n₁+1) (q+n₁+n₂+1) (by linarith) (by linarith),
    δ_eq n₁ (n₁+1) rfl q (q+n₁+1) (by linarith) (q+n₁) (q+1) (by linarith) rfl,
    cochain.comp_eq z₁ (δ n₂ (n₂+1) z₂) (add_assoc n₁ n₂ 1) q (q+n₁) (q+n₁+n₂+1) rfl (by linarith),
    δ_eq n₂ (n₂+1) rfl (q+n₁) (q+n₁+n₂+1) (by linarith) (q+n₁+n₂) (q+n₁+1) (by linarith) rfl,
    comp_add, linear.comp_smul, add_comp, assoc, linear.smul_comp, smul_add, hε' n₂, smul_smul, eq, neg_smul, comp_neg],
  have simplif : Π (a b c : F.X q ⟶ K.X (q + n₁ + n₂ + 1)), a+b=a+(-c)+(c+b) := λ a b c, by abel,
  apply simplif,
end

end hom_complex

variables (F G)

open hom_complex

def hom_complex : cochain_complex AddCommGroup ℤ :=
{ X := λ n, AddCommGroup.of (cochain F G n),
  d := λ n m, AddCommGroup.of_hom (δ_hom F G n m),
  shape' := λ n m hnm, begin
    ext f q q' hqq',
    dsimp [δ_hom, δ],
    change ¬ n+1 = m at hnm,
    rw [F.shape, G.shape, comp_zero, zero_comp, smul_zero, add_zero],
    { change ¬ q+n+1 = q', intro h, apply hnm, linarith, },
    { change ¬ q+1 = q+m-n, intro h, apply hnm, linarith, },
  end,
  d_comp_d' := λ i j k hij hjk, begin
    ext f q q' hqq',
    simp only [comp_apply],
    dsimp [δ_hom],
    change i+1=j at hij,
    subst hij,
    change i+1+1=k at hjk,
    have hjk' : i+2 = k := by linarith,
    subst hjk',
    rw δ_eq (i+1) (i+2) (by linarith) q q' hqq' (q'-1) (q+1) rfl rfl,
    rw δ_eq i (i+1) rfl q (q'-1) (by linarith) (q'-2) (q+1) (by linarith) rfl,
    rw δ_eq i (i+1) rfl (q+1) q' (by linarith) (q'-1) (q+2) rfl (by linarith),
    simp only [hε', add_zero, neg_neg, zero_add, neg_zero, neg_smul, add_comp, assoc,
      homological_complex.d_comp_d, comp_zero, neg_comp, linear.smul_comp, comp_add,
      comp_neg, linear.comp_smul, homological_complex.d_comp_d_assoc, zero_comp,
      smul_zero, add_left_neg],
  end, }

namespace hom_complex

def cocycle (n : ℤ) : add_subgroup (cochain F G n) :=
add_monoid_hom.ker ((hom_complex F G).d n (n+1))

namespace cocycle

variables {F G}

def mem_iff (n m : ℤ) (hnm : n+1=m) (z : cochain F G n) :
  z ∈ cocycle F G n ↔ δ n m z = 0 :=
by { subst hnm, refl, }

@[simps]
def of_hom (φ : F ⟶ G) : cocycle F G 0 :=
begin
  refine ⟨cochain.of_hom φ, _⟩,
  rw mem_iff 0 1 (by linarith),
  ext q q' hqq',
  rw δ_eq 0 1 (by linarith) q q' hqq' q q' (by linarith) hqq',
  simp only [zero_add, cochain.of_hom_eq, homological_complex.hom.comm, cochain.zero_apply, hε₁,
    neg_smul, one_smul, add_right_neg],
end

variables (F G)

def equiv_hom : (F ⟶ G) ≃+ cocycle F G 0 :=
{ to_fun := of_hom,
  inv_fun := λ z,
  { f := λ i, z.1 i i (add_zero i).symm,
    comm' := λ i j hij, begin
      change i+1 =j at hij,
      have hz₁ := z.2,
      rw mem_iff 0 1 (by linarith) at hz₁,
      have hz₂ := congr_fun₃ hz₁ i j hij.symm,
      rw δ_eq 0 1 (by linarith) i j hij.symm i j (by linarith) hij.symm z.1 at hz₂,
      simpa only [zero_add, cochain.zero_apply, hε₁, neg_smul, one_smul,
      tactic.ring.add_neg_eq_sub, sub_eq_zero] using hz₂,
    end, },
  left_inv := λ f, begin
    ext i,
    simp only [subtype.val_eq_coe, of_hom_coe, cochain.of_hom_eq],
  end,
  right_inv := λ z, begin
    ext q q' hqq',
    have h : q' = q := by linarith,
    subst h,
    simp only [subtype.val_eq_coe, of_hom_coe, cochain.of_hom_eq],
  end,
  map_add' := λ f₁ f₂, begin
    ext q q' hqq',
    have h : q' = q := by linarith,
    subst h,
    simp only [of_hom_coe, cochain.of_hom_eq, homological_complex.add_f_apply,
      add_subgroup.coe_add, cochain.add_apply],
  end, }

end cocycle

def equiv_homotopy {φ₁ φ₂ : F ⟶ G} :
  homotopy φ₁ φ₂ ≃ { z : cochain F G (-1) // cochain.of_hom φ₁ = δ (-1) 0 z + cochain.of_hom φ₂ } :=
{ to_fun := λ ho, begin
    refine ⟨cochain.of_homotopy ho, _⟩,
    ext q q' hqq',
    have h : q = q' := by linarith,
    subst h,
    have comm := ho.comm q,
    rw [d_next_eq ho.hom (show q+1=q+1, by linarith), prev_d_eq ho.hom (show q-1+1=q, by linarith)] at comm,
    simp only [cochain.of_homotopy, cochain.of_hom_eq, cochain.add_apply,
      δ_eq (-1) 0 (by linarith) q q hqq' (q-1) (q+1) rfl rfl,
      hε₀, add_left_neg, one_zsmul, comm],
    abel,
  end,
  inv_fun := λ z,
  { hom := λ i j, begin
      by_cases j+1 = i,
      { exact z.1 i j (by linarith), },
      { exact 0, },
    end,
    zero' := λ i j hij, begin
      change ¬j+1=i at hij,
      rw dif_neg hij,
    end,
    comm := λ q, begin
      have h₁ : q+1 = q+1 := rfl,
      have h₂ : q-1+1 = q := by linarith,
      have h₁' : (complex_shape.up ℤ).rel q (q+1) := h₁,
      have h₂' : (complex_shape.up ℤ).rel (q-1) q := h₂,
      rw [d_next_eq _ h₁', prev_d_eq _ h₂', dif_pos h₁, dif_pos h₂],
      have h₃ := congr_fun₃ z.2 q q (by linarith),
      simp only [cochain.of_hom_eq, cochain.add_apply,
        δ_eq (-1) 0 (by linarith) q q (by linarith) (q-1) (q+1) rfl rfl,
        add_left_neg, hε₀, one_smul] at h₃,
      conv_rhs at h₃ { congr, rw add_comm, },
      rw h₃,
    end, },
  left_inv := λ ho, begin
    ext i j,
    dsimp,
    split_ifs,
    { refl, },
    { rw ho.zero i j h, }
  end,
  right_inv := λ z, begin
    ext q q' hqq',
    dsimp,
    split_ifs,
    { refl, },
    { exfalso, apply h, linarith, },
  end, }

end hom_complex

end homology

end algebra