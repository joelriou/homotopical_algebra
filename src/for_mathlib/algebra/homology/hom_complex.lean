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

def is_bounded_above (K : cochain_complex C ℤ) : Prop :=
∃ (r : ℤ), ∀ (i : ℤ) (hi : r < i), is_zero (K.X i)

variables {F G K L : cochain_complex C ℤ} (n m : ℤ)

namespace hom_complex

def ε (n : ℤ) : ℤ := ↑((-1 : units ℤ) ^ n)

@[simp]

lemma ε_add (n₁ n₂ : ℤ) : ε (n₁ + n₂) = ε n₁ * ε n₂ :=
by { dsimp [ε], rw [← units.coe_mul, ← units.ext_iff, zpow_add], }

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
  rw [hk, ε_add, ε_1, ε_even (2*k) ⟨k, two_mul k⟩, one_mul],
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

@[simp]
lemma zero_v {n : ℤ} (p q : ℤ) (hpq : q=p+n) : (0 : cochain F G n).v p q hpq = 0 := rfl

@[simp]
lemma add_v {n : ℤ} (z₁ z₂ : cochain F G n) (p q : ℤ) (hpq : q=p+n) :
  (z₁+z₂).v p q hpq = z₁.v p q hpq + z₂.v p q hpq := rfl

@[simp]
lemma sub_v {n : ℤ} (z₁ z₂ : cochain F G n) (p q : ℤ) (hpq : q=p+n) :
  (z₁-z₂).v p q hpq = z₁.v p q hpq - z₂.v p q hpq := rfl

@[simp]
lemma neg_v {n : ℤ} (z : cochain F G n) (p q : ℤ) (hpq : q=p+n) :
  (-z).v p q hpq = - (z.v p q hpq) := rfl

@[simp]
lemma zsmul_v {n k : ℤ} (z : cochain F G n) (p q : ℤ) (hpq : q=p+n) :
  (k • z).v p q hpq = k • (z.v p q hpq) := rfl

def of_homs (ψ : Π (p : ℤ), F.X p ⟶ G.X p) : cochain F G 0 :=
cochain.mk (λ p q hpq, ψ p ≫ eq_to_hom (by rw [hpq, add_zero]))

@[simp]
lemma of_homs_v (ψ : Π (p : ℤ), F.X p ⟶ G.X p) (p : ℤ) :
  (of_homs ψ).v p p (add_zero p).symm = ψ p :=
by simp only [of_homs, mk_v, eq_to_hom_refl, comp_id]

@[simp]
lemma of_homs_v_comp_d (ψ : Π (p : ℤ), F.X p ⟶ G.X p) (p q q' : ℤ) (hpq : q=p+0) :
  (of_homs ψ).v p q hpq ≫ G.d q q' = ψ p ≫ G.d p q' :=
begin
  rw add_zero at hpq,
  subst hpq,
  rw of_homs_v,
end

@[simp]
lemma d_comp_of_homs_v (ψ : Π (p : ℤ), F.X p ⟶ G.X p) (p' p q  : ℤ) (hpq : q=p+0) :
  F.d p' p ≫ (of_homs ψ).v p q hpq = F.d p' q ≫ ψ q :=
begin
  rw add_zero at hpq,
  subst hpq,
  rw of_homs_v,
end

def of_hom (φ : F ⟶ G) : cochain F G 0 :=
of_homs (λ p, φ.f p)

@[simp]
lemma of_hom_v (φ : F ⟶ G) (p : ℤ) : (of_hom φ).v p p (add_zero p).symm = φ.f p :=
by simp only [of_hom, of_homs_v]

@[simp]
lemma of_hom_v_comp_d (φ : F ⟶ G) (p q q' : ℤ) (hpq : q=p+0) :
  (of_hom φ).v p q hpq ≫ G.d q q' = φ.f p ≫ G.d p q' :=
by simp only [of_hom, of_homs_v_comp_d]

@[simp]
lemma d_comp_of_hom_v (φ : F ⟶ G) (p' p q  : ℤ) (hpq : q=p+0) :
  F.d p' p ≫ (of_hom φ).v p q hpq = F.d p' q ≫ φ.f q :=
by simp only [of_hom, d_comp_of_homs_v]

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

lemma zero_cochain_comp' {n : ℤ} (z₁ : cochain F G 0) (z₂ : cochain G K n)
  (p₁ p₂ p₃ : ℤ) (h₁₂ : p₂=p₁+0) (h₂₃ : p₃=p₂+n) :
  (z₁.v p₁ p₂ h₁₂ ≫ z₂.v p₂ p₃ h₂₃ : F.X p₁ ⟶ K.X p₃) =
  z₁.v p₁ p₁ (add_zero p₁).symm ≫ z₂.v p₁ p₃ (show p₃ = p₁+n, by rw [h₂₃, h₁₂, add_zero]) :=
by { rw add_zero at h₁₂, subst h₁₂, }

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
lemma comp_zero_cochain (z₁ : cochain F G n) (z₂ : cochain G K 0)
  (p q : ℤ) (hpq : q=p+n) :
  (cochain.comp z₁ z₂ (add_zero n).symm).v p q hpq =
    z₁.v p q hpq ≫ z₂.v q q (add_zero q).symm :=
comp_v z₁ z₂ (add_zero n).symm p q q hpq (add_zero q).symm

lemma comp_zero_cochain' (z₁ : cochain F G n) (z₂ : cochain G K 0)
  (p₁ p₂ p₃ : ℤ) (h₁₂ : p₂=p₁+n) (h₂₃ : p₃=p₂+0) :
  (z₁.v p₁ p₂ h₁₂ ≫ z₂.v p₂ p₃ h₂₃ : F.X p₁ ⟶ K.X p₃) =
  z₁.v p₁ p₃ (show p₃=p₁+n, by rw [h₂₃, h₁₂, add_zero]) ≫ z₂.v p₃ p₃ (add_zero p₃).symm :=
by { rw add_zero at h₂₃, subst h₂₃, }

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

lemma δ_v (hnm : n+1=m) (z : cochain F G n) (p q : ℤ) (hpq : q=p+m) (q₁ q₂ : ℤ)
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
  rw δ_v n₁ n₂ h₁₂ _ p q hpq _ _ rfl rfl,
  rw δ_v n₀ n₁ h₀₁ z p (q-1) (by linarith) (q-2) _ (by linarith) rfl,
  rw δ_v n₀ n₁ h₀₁ z (p+1) q (by linarith) _ (p+2) rfl (by linarith),
  simp only [← h₀₁, ε_succ, add_comp, neg_neg, neg_zsmul, neg_comp, cochain.zero_v,
    zsmul_comp, comp_zsmul, comp_add, comp_neg, assoc, homological_complex.d_comp_d,
    homological_complex.d_comp_d_assoc, comp_zero, zero_comp, zsmul_zero, neg_zero, add_zero,
    zero_add, add_left_neg],
end

lemma δ_comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂)
  (m₁ m₂ m₁₂ : ℤ) (h₁₂ : n₁₂+1 = m₁₂) (h₁ : n₁+1 = m₁) (h₂ : n₂+1 = m₂) :
δ n₁₂ m₁₂ (cochain.comp z₁ z₂ h) = cochain.comp z₁ (δ n₂ m₂ z₂) (by linarith) + ε n₂ • cochain.comp (δ n₁ m₁ z₁) z₂ (by linarith) :=
begin
  substs h₁₂ h₁ h₂,
  ext,
  have eq : ε (n₁₂ + 1) = ε n₂ * ε (n₁+1),
  { rw ← ε_add, congr' 1, linarith, },
  simp only [cochain.add_v, cochain.zsmul_v,
    cochain.comp_v z₁ (δ n₂ (n₂+1) z₂) (show n₁₂+1=n₁+(n₂+1), by linarith) p _ q rfl (by linarith),
    cochain.comp_v (δ n₁ (n₁+1) z₁) z₂ (show n₁₂+1=_, by linarith) p (p+n₁+1) q (by linarith) (by linarith),
    cochain.comp_v z₁ z₂ h p (p+n₁) (p+n₁₂) rfl (by linarith),
    cochain.comp_v z₁ z₂ h (p+1) (p+n₁+1) q (by linarith) (by linarith),
    δ_v n₁₂ _ rfl (cochain.comp z₁ z₂ h) p q hpq (p+n₁₂) _ (by linarith) rfl,
    δ_v n₁ (n₁+1) rfl z₁ p (p+n₁+1) (by linarith) (p+n₁) (p+1) (by linarith) rfl,
    δ_v n₂ (n₂+1) rfl z₂ (p+n₁) q (by linarith) (p+n₁₂) (p+n₁+1) (by linarith) rfl,
    assoc, comp_add, comp_zsmul, zsmul_add, add_comp, zsmul_comp, smul_smul, eq,
    ε_add n₂ 1, ε_1, mul_neg, mul_one, neg_zsmul, comp_neg, ← add_assoc],
  suffices : ∀ (a b c : F.X p ⟶ K.X q), a+b=a+(-c)+c+b,
  { apply this, },
  intros a b c,
  abel,
end

@[simp]
lemma δ_comp_of_first_is_zero_cochain {n₂ : ℤ} (z₁ : cochain F G 0) (z₂ : cochain G K n₂)
  (m₂ : ℤ) (h₂ : n₂+1 = m₂) :
δ n₂ m₂ (cochain.comp z₁ z₂ (zero_add n₂).symm) =
  cochain.comp z₁ (δ n₂ m₂ z₂) (by linarith) + ε n₂ • cochain.comp (δ 0 1 z₁) z₂ (by linarith) :=
δ_comp z₁ z₂ (zero_add n₂).symm 1 m₂ m₂ h₂ (zero_add 1) h₂

@[simp]
lemma δ_comp_of_second_is_zero_cochain {n₁ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K 0)
  (m₁ : ℤ) (h₁ : n₁+1 = m₁) : δ n₁ m₁ (cochain.comp z₁ z₂ (add_zero n₁).symm) =
  cochain.comp z₁ (δ 0 1 z₂) h₁.symm + cochain.comp (δ n₁ m₁ z₁) z₂ (add_zero m₁).symm :=
by simp only [δ_comp z₁ z₂ (add_zero n₁).symm m₁ 1 m₁ h₁ h₁ (zero_add 1), ε_0, one_zsmul]

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
  simp only [δ_v 0 1 (zero_add 1) _ p q hpq p q (by linarith) hpq,
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
    simpa only [δ_v 0 1 (zero_add 1) z.1 i j hij.symm i j (by linarith) hij.symm,
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

variables {F G}
def equiv_homotopy (φ₁ φ₂ : F ⟶ G) :
  homotopy φ₁ φ₂ ≃
    { z : cochain F G (-1) // cochain.of_hom φ₁ = δ (-1) 0 z + cochain.of_hom φ₂ } :=
{ to_fun := λ ho, begin
    refine ⟨cochain.of_homotopy ho, _⟩,
    ext,
    have comm := ho.comm p,
    rw [d_next_eq ho.hom rfl, prev_d_eq ho.hom (sub_add_cancel p 1)] at comm,
    rw [cochain.add_v, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl],
    simp only [δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl,
      add_left_neg, ε_0, one_zsmul, cochain.mk, cochain.of_hom_v, cochain.v,
      cochain.of_homotopy, cochain.of_hom_v],
    dsimp only,
    suffices : ∀ (a b c d : F.X p ⟶ G.X p) (h : a = b+c+d), a=c+b+d,
    { exact this _ _ _ _ comm, },
    { intros a b c d h, rw h, abel, },
  end,
  inv_fun := λ z,
    { hom := λ i j, begin
        by_cases j+1=i,
        { exact (z : cochain F G (-1)).v i j (by linarith), },
        { exact 0, },
      end,
      zero' := λ i j hij, begin
        change ¬ j+1 = i at hij,
        rw dif_neg hij,
      end,
      comm := λ p, begin
        have h₁ : p+1 = p+1 := rfl,
        have h₂ : p-1+1 = p := by linarith,
        have h₁' : (complex_shape.up ℤ).rel p (p+1) := h₁,
        have h₂' : (complex_shape.up ℤ).rel (p-1) p := h₂,
        rw [d_next_eq _ h₁', prev_d_eq _ h₂', dif_pos h₁, dif_pos h₂],
        have hz := cochain.congr_v z.2 p p (add_zero p).symm,
        simp only [cochain.add_v, δ_v (-1) 0 (neg_add_self 1) _ p p (add_zero p).symm _ _ rfl rfl,
          cochain.of_hom_v, add_left_neg, ε_0, one_zsmul] at hz,
        suffices : ∀ (a b c d : F.X p ⟶ G.X p) (h : a = b+c+d), a=c+b+d,
        { exact this _ _ _ _ hz, },
        { intros a b c d h, rw h, abel, },
      end, },
  left_inv := λ ho, begin
    ext i j,
    dsimp,
    split_ifs,
    { refl, },
    { rw ho.zero i j h, },
  end,
  right_inv := λ z, begin
    ext,
    dsimp [cochain.mk, cochain.v],
    simpa only [dif_pos (show q+1=p, by linarith)],
  end, }

end hom_complex

end cochain_complex
