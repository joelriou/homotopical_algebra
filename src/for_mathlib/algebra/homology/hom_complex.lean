/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy
import algebra.homology.additive
import algebra.category.Group.abelian
import data.int.parity
import algebra.homology.short_exact.preadditive

noncomputable theory

open category_theory category_theory.preadditive category_theory.limits category_theory.category

universes v u

variables {C : Type u} [category.{v} C] [preadditive C]

namespace cochain_complex

variables {F G K L : cochain_complex C ℤ} (n m : ℤ)

namespace hom_complex

@[simp]
def ε (n : ℤ) : ℤ := ↑((-1 : units ℤ) ^ n)

@[simp]

lemma ε_add (n₁ n₂ : ℤ) : ε (n₁ + n₂) = ε n₁ • ε n₂ :=
by { dsimp, rw [← units.coe_mul, ← units.ext_iff, zpow_add], }

@[simp]
lemma ε_0 : ε 0 = 1 := rfl

@[simp]
lemma ε_1 : ε 1 = -1 := rfl

@[simp]
lemma ε_succ (n : ℤ) : ε (n + 1) = - ε n :=
by simp only [ε_add, ε_1, algebra.id.smul_eq_mul, mul_neg, mul_one]

lemma ε_even (n : ℤ) (hn : even n) : ε n = 1 :=
begin
  change _ = ↑(1 : units ℤ),
  cases hn with k hk,
  simp only [ε, ← units.ext_iff, hk, zpow_add, ← mul_zpow, int.units_mul_self],
end

lemma ε_odd (n : ℤ) (hn : odd n) : ε n = -1 :=
begin
  cases hn with k hk,
  rw [hk, ε_add, ε_1, ε_even (2*k) ⟨k, two_mul k⟩, one_zsmul],
end

structure triplet (n : ℤ) := (p : ℤ) (q : ℤ) (hpq : q=p+n)

variables (F G)

@[derive add_comm_group]
def cochain := Π (T : triplet n), F.X T.p ⟶ G.X T.q

namespace cochain

variables {F G n}

def mk (v : Π (p q : ℤ) (hpq : q=p+n), F.X p ⟶ G.X q) : cochain F G n :=
λ T, v T.p T.q T.hpq

def v (c : cochain F G n) (p q : ℤ) (hpq : q=p+n) := c (triplet.mk p q hpq)

@[simp]
lemma zero_v {n : ℤ} (p q : ℤ) (hpq : q=p+n) : (0 : cochain F G n).v p q hpq = 0 := rfl

lemma mk_v (v : Π (p q : ℤ) (hpq : q=p+n), F.X p ⟶ G.X q) (p q : ℤ) (hpq : q=p+n) :
  (mk v).v p q hpq = v p q hpq := rfl

lemma congr_v {z₁ z₂ : cochain F G n} (h : z₁ = z₂) (p q : ℤ) (hpq : q=p+n) :
  z₁.v p q hpq = z₂.v p q hpq := by subst h

@[ext]
lemma ext (z₁ z₂ : cochain F G n) (h : ∀ (p q : ℤ) (hpq : q=p+n), z₁.v p q hpq = z₂.v p q hpq) :
  z₁ = z₂ :=
begin
  ext T,
  rcases T with ⟨p, q, hpq⟩,
  exact h p q hpq,
end

@[ext]
lemma ext₀ (z₁ z₂ : cochain F G 0)
  (h : ∀ (p : ℤ), z₁.v p p (add_zero p).symm = z₂.v p p (add_zero p).symm ) : z₁ = z₂ :=
begin
  ext,
  have eq : q=p := by rw [hpq, add_zero],
  subst eq,
  apply h,
end

def of_homs (ψ : Π (p : ℤ), F.X p ⟶ G.X p) : cochain F G 0 :=
cochain.mk (λ p q hpq, ψ p ≫ eq_to_hom (by rw [hpq, add_zero]))

@[simp]
lemma of_homs_eq (ψ : Π (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
  (of_homs ψ).v p p (add_zero p).symm = ψ p :=
by simp only [of_homs, mk_v, eq_to_hom_refl, comp_id]

def of_hom (φ : F ⟶ G) : cochain F G 0 :=
of_homs (λ p, φ.f p)

@[simp]
lemma of_hom_v (φ : F ⟶ G) (p : ℤ) : (of_hom φ).v p p (add_zero p).symm = φ.f p :=
by simp only [of_hom, of_homs_eq]

@[simp]
def of_homotopy {φ₁ φ₂ : F ⟶ G} (ho : homotopy φ₁ φ₂) : cochain F G (-1) :=
cochain.mk (λ p q hpq, ho.hom p q)

def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂) :
  cochain F K n₁₂ :=
cochain.mk (λ p q hpq, z₁.v p (p+n₁) rfl ≫ z₂.v (p+n₁) q (by linarith))

notation a ` ≫[` b `] ` c := cochain.comp a c b

lemma comp_v {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁+n₂)
  (p₁ p₂ p₃ : ℤ) (h₁ : p₂=p₁+n₁) (h₂ : p₃=p₂+n₂) :
  (comp z₁ z₂ h).v p₁ p₃ (by rw [h₂, h₁, h, add_assoc]) =
  z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by { subst h₁, refl,}

@[simp]
lemma zero_comp {n₁ n₂ n₁₂ : ℤ} (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (0 : cochain F G n₁) z₂ h = 0 :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [zero_comp],
end

@[simp]
lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (z₁+z₁') z₂ h = comp z₁ z₂ h + comp z₁' z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [add_comp],
end

@[simp]
lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁' : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (z₁-z₁') z₂ h = comp z₁ z₂ h - comp z₁' z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [sub_comp],
end

@[simp]
lemma neg_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (-z₁) z₂ h = -comp z₁ z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [neg_comp],
end

@[simp]
lemma zsmul_comp {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (k • z₁) z₂ h = k • comp z₁ z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [zsmul_comp],
end

@[simp]
lemma zero_cochain_comp {n : ℤ} (z₁ : cochain F G 0) (z₂ : cochain G K n)
  (p q : ℤ) (hpq : q=p+n) :
  (cochain.comp z₁ z₂ (zero_add n).symm).v p q hpq =
    z₁.v p p (add_zero p).symm ≫ z₂.v p q hpq :=
comp_v z₁ z₂ (zero_add n).symm p p q (add_zero p).symm hpq

@[simp]
lemma id_comp {n : ℤ} (z₂ : cochain F G n) :
  cochain.comp (cochain.of_hom (𝟙 F)) z₂ (zero_add n).symm = z₂ :=
begin
  ext,
  simp only [zero_cochain_comp, of_hom_v, homological_complex.id_f, id_comp],
end

@[simp]
lemma comp_zero {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁)
  (h : n₁₂ = n₁ + n₂) : comp z₁ (0 : cochain G K n₂) h = 0 :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [comp_zero],
end

@[simp]
lemma comp_add {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ z₂' : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp z₁ (z₂+z₂') h = comp z₁ z₂ h + comp z₁ z₂' h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [comp_add],
end

@[simp]
lemma comp_sub {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ z₂' : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp z₁ (z₂-z₂') h = comp z₁ z₂ h - comp z₁ z₂' h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [comp_sub],
end

@[simp]
lemma comp_neg {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp z₁ (-z₂) h = -comp z₁ z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [comp_neg],
end

@[simp]
lemma comp_zsmul {n₁ n₂ n₁₂ : ℤ} (k : ℤ) (z₁ : cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp z₁ (k • z₂) h = k • comp z₁ z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [comp_zsmul],
end

@[simp]
lemma comp_zero_cochain {n : ℤ} (z₁ : cochain F G n) (z₂ : cochain G K 0)
  (p q : ℤ) (hpq : q=p+n) :
  (cochain.comp z₁ z₂ (add_zero n).symm).v p q hpq =
    z₁.v p q hpq ≫ z₂.v q q (add_zero q).symm :=
comp_v z₁ z₂ (add_zero n).symm p q q hpq (add_zero q).symm

@[simp]
lemma comp_id {n : ℤ} (z₁ : cochain F G n) :
  cochain.comp z₁ (cochain.of_hom (𝟙 G)) (add_zero n).symm = z₁ :=
begin
  ext,
  simp only [comp_zero_cochain, of_hom_v, homological_complex.id_f, comp_id],
end

@[simp]
lemma cochain_of_hom_comp (f : F ⟶ G) (g : G ⟶ K) :
  cochain.comp (cochain.of_hom f) (cochain.of_hom g) (zero_add 0).symm =
  cochain.of_hom (f ≫ g) :=
begin
  ext,
  simp only [comp_zero_cochain, of_hom_v, homological_complex.comp_f],
end

lemma comp_assoc {n₁ n₂ n₃ n₁₂ n₂₃ n₁₂₃ : ℤ}
  (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (z₃ : cochain K L n₃)
  (h₁₂ : n₁₂ = n₁ + n₂) (h₂₃ : n₂₃ = n₂ + n₃) (h₁₂₃ : n₁₂₃ = n₁ + n₂ + n₃) :
  cochain.comp (cochain.comp z₁ z₂ h₁₂) z₃ (show n₁₂₃ = n₁₂ + n₃, by rw [h₁₂, h₁₂₃]) =
    cochain.comp z₁ (cochain.comp z₂ z₃ h₂₃)
      (show n₁₂₃ = n₁ + n₂₃, by rw [h₂₃, h₁₂₃, add_assoc]) :=
begin
  ext,
  simp only [comp_v _ _ (show n₁₂₃ = n₁₂ + n₃, by rw [h₁₂, h₁₂₃]) p (p+n₁₂) q rfl (by linarith),
    comp_v _ _ h₁₂ p (p+n₁) (p+n₁₂) rfl (by linarith),
    comp_v z₁ (cochain.comp z₂ z₃ h₂₃) (show n₁₂₃ = n₁ + n₂₃, by linarith)
      p (p+n₁) q rfl (by linarith),
    comp_v _ _ h₂₃ (p+n₁) (p+n₁₂) q (by linarith) (by linarith), assoc],
end

@[simp]
lemma comp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : ℤ}
  (z₁ : cochain F G 0) (z₂ : cochain G K n₂) (z₃ : cochain K L n₃)
  (h₂₃ : n₂₃ = n₂ + n₃) :
  cochain.comp (cochain.comp z₁ z₂ (zero_add n₂).symm) z₃ h₂₃ =
    cochain.comp z₁ (cochain.comp z₂ z₃ h₂₃)
      (zero_add n₂₃).symm :=
comp_assoc z₁ z₂ z₃ (zero_add n₂).symm h₂₃ (by linarith)

@[simp]
lemma comp_assoc_of_second_is_zero_cochain {n₁ n₃ n₁₃ : ℤ}
  (z₁ : cochain F G n₁) (z₂ : cochain G K 0) (z₃ : cochain K L n₃) (h₁₃ : n₁₃ = n₁ + n₃) :
  cochain.comp (cochain.comp z₁ z₂ (add_zero n₁).symm) z₃ h₁₃ =
    cochain.comp z₁ (cochain.comp z₂ z₃ (zero_add n₃).symm) h₁₃ :=
comp_assoc z₁ z₂ z₃ (add_zero n₁).symm (zero_add n₃).symm (by linarith)

@[simp]
lemma comp_assoc_of_third_is_zero_cochain {n₁ n₂ n₁₂ : ℤ}
  (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (z₃ : cochain K L 0) (h₁₂ : n₁₂ = n₁ + n₂) :
  cochain.comp (cochain.comp z₁ z₂ h₁₂) z₃ (add_zero n₁₂).symm =
    cochain.comp z₁ (cochain.comp z₂ z₃ (add_zero n₂).symm) h₁₂ :=
comp_assoc z₁ z₂ z₃ h₁₂ (add_zero n₂).symm (by linarith)

end cochain

/- Differentials -/

variables {F G} (n)

def δ (z : cochain F G n) : cochain F G m :=
cochain.mk (λ (p q : ℤ) hpq, z.v p (p+n) rfl ≫ G.d (p+n) q +
  ε (n+1) • F.d p (p+m-n) ≫ z.v (p+m-n) q (by { dsimp [int.sub], linarith}))

lemma δ_v (z : cochain F G n) (p q : ℤ) (hpq : q=p+m)  (hnm : n+1=m) (q₁ q₂ : ℤ)
  (hq₁ : q₁=q-1) (hq₂ : q₂=p+1) : (δ n m z).v p q hpq =
  z.v p q₁ (by {rw [hq₁, hpq, ← hnm, ← add_assoc, add_tsub_cancel_right],}) ≫ G.d q₁ q
  + ε (n+1) • F.d p q₂ ≫ z.v q₂ q (by rw [hpq, hq₂, ← hnm, add_comm n, add_assoc]) :=
begin
  have h₁ : q₁ = p+n := by linarith,
  have h₂ : q₂ = p+m-n := by linarith,
  substs h₁ h₂,
  refl,
end

lemma δ_shape (hnm : ¬ n+1=m) (z : cochain F G n) : δ n m z = 0 :=
begin
  ext,
  dsimp [δ, cochain.mk, cochain.v],
  rw [F.shape, G.shape, limits.comp_zero, limits.zero_comp, smul_zero, add_zero],
  all_goals
  { change ¬ _=_ ,
    intro h,
    apply hnm,
    linarith, },
end

variables (F G)

def δ_hom : cochain F G n →+ cochain F G m :=
{ to_fun := δ n m,
  map_zero' := begin
    ext,
    dsimp [δ, cochain.mk, cochain.v],
    simp only [limits.zero_comp, limits.comp_zero, smul_zero, add_zero],
  end,
  map_add' := λ z₁ z₂, begin
    ext,
    dsimp [δ, cochain.mk, cochain.v],
    simp only [preadditive.add_comp, preadditive.comp_add, smul_add],
    abel,
  end}

variables {F G}

@[simp]
lemma δ_add (z₁ z₂ : cochain F G n) : δ n m (z₁ + z₂) = δ n m z₁ + δ n m z₂ :=
(δ_hom F G n m).map_add z₁ z₂

@[simp]
lemma δ_sub (z₁ z₂ : cochain F G n) : δ n m (z₁ - z₂) = δ n m z₁ - δ n m z₂ :=
(δ_hom F G n m).map_sub z₁ z₂

@[simp]
lemma δ_zero : δ n m (0 : cochain F G n) = 0 := (δ_hom F G n m).map_zero

@[simp]
lemma δ_neg (z : cochain F G n) : δ n m (-z) = - δ n m z :=
(δ_hom F G n m).map_neg z

@[simp]
lemma δ_zsmul (k : ℤ) (z : cochain F G n) : δ n m (k • z) = k • δ n m z :=
(δ_hom F G n m).map_zsmul z k

@[simp]
lemma δδ (n₀ n₁ n₂ : ℤ) (z : cochain F G n₀) : δ n₁ n₂ (δ n₀ n₁ z) = 0 :=
begin
  by_cases h₀₁ : n₀+1 = n₁, swap,
  { rw [δ_shape n₀ n₁ h₀₁, δ_zero], },
  by_cases h₁₂ : n₁+1 = n₂, swap,
  { rw [δ_shape n₁ n₂ h₁₂], },
  ext,
  rw δ_v n₁ n₂ _ p q hpq h₁₂ _ _ rfl rfl,
  rw δ_v n₀ n₁ z p (q-1) (by linarith) h₀₁ (q-2) _ (by linarith) rfl,
  rw δ_v n₀ n₁ z (p+1) q (by linarith) h₀₁ _ (p+2) rfl (by linarith),
  simp only [← h₀₁, ε_succ, add_comp, neg_neg, neg_zsmul, neg_comp, cochain.zero_v,
    zsmul_comp, comp_zsmul, comp_add, comp_neg, assoc, homological_complex.d_comp_d,
    homological_complex.d_comp_d_assoc, comp_zero, zero_comp, zsmul_zero, neg_zero, add_zero,
    zero_add, add_left_neg],
end

end hom_complex

variables (F G)

open hom_complex

def hom_complex : cochain_complex AddCommGroup ℤ :=
{ X := λ i, AddCommGroup.of (cochain F G i),
  d := λ i j, AddCommGroup.of_hom (δ_hom F G i j),
  shape' := λ i j hij, by { ext1 z, exact δ_shape i j hij z, },
  d_comp_d' := λ i j k hij hjk, by { ext1 f, apply δδ, } }

namespace hom_complex

def cocycle : add_subgroup (cochain F G n) :=
add_monoid_hom.ker ((hom_complex F G).d n (n+1))

namespace cocycle

variables {F G}

def mem_iff (hnm : n+1=m) (z : cochain F G n) :
  z ∈ cocycle F G n ↔ δ n m z = 0 :=
by { subst hnm, refl, }

variable {n}

@[simps]
def mk (z : cochain F G n) (m : ℤ) (hnm : n+1 = m) (h : δ n m z = 0) : cocycle F G n :=
⟨z, by simpa only [mem_iff n m hnm z] using h⟩

@[simp]
lemma δ_eq_zero {n : ℤ} (z : cocycle F G n) (m : ℤ) : δ n m (z : cochain F G n) = 0 :=
begin
  by_cases n+1=m,
  { rw ← mem_iff n m h,
    exact z.2, },
  { apply δ_shape n m h, }
end

def of_hom (φ : F ⟶ G) : cocycle F G 0 := mk (cochain.of_hom φ) 1 (zero_add 1)
begin
  ext,
  simp only [δ_v 0 1 _ p q hpq (zero_add 1) p q (by linarith) hpq,
    cochain.of_hom_v, homological_complex.hom.comm, ε_1, neg_smul, one_zsmul,
    add_right_neg, cochain.zero_v, zero_add],
end

@[simp]
lemma δ_cochain_of_hom (φ : F ⟶ G) : δ 0 1 (cochain.of_hom φ) = 0 :=
by apply δ_eq_zero (of_hom φ)

@[simps]
def hom_of (z : cocycle F G 0) : F ⟶ G :=
{ f := λ i, (z : cochain F G 0).v i i (add_zero i).symm,
  comm' := λ i j hij, begin
    change i+1=j at hij,
    have hz₁ := z.2,
    rw mem_iff 0 1 (zero_add 1) at hz₁,
    simpa only [δ_v 0 1 z.1 i j hij.symm (zero_add 1) i j (by linarith) hij.symm,
      zero_add, ε_1, neg_smul, one_zsmul, cochain.zero_v, add_neg_eq_zero]
      using cochain.congr_v hz₁ i j hij.symm,
  end, }

@[simp]
lemma hom_of_of_hom_eq_self (φ : F ⟶ G) : hom_of (of_hom φ) = φ :=
by { ext i, simp only [of_hom, hom_of_f, mk_coe, cochain.of_hom_v], }

@[simp]
lemma of_hom_hom_of_eq_self (z : cocycle F G 0) : of_hom (hom_of z) = z :=
begin
  ext,
  simp only [of_hom, mk_coe, cochain.of_hom_v, hom_of_f],
end

@[simp]
lemma coe_of_hom_hom_of_eq_coe (z : cocycle F G 0) : (of_hom (hom_of z) : cochain F G 0) = z :=
by rw of_hom_hom_of_eq_self z

variables (F G)

def equiv_hom : (F ⟶ G) ≃+ cocycle F G 0 :=
{ to_fun := of_hom,
  inv_fun := hom_of,
  left_inv := hom_of_of_hom_eq_self,
  right_inv := of_hom_hom_of_eq_self,
  map_add' := λ φ₁ φ₂, begin
    ext,
    simp only [of_hom, cochain.of_hom, cochain.of_homs, cochain.mk, cochain.v,
      homological_complex.add_f_apply, mk_coe, eq_to_hom_refl, comp_id,
      add_subgroup.coe_add, pi.add_apply],
  end, }

end cocycle

end hom_complex

end cochain_complex
