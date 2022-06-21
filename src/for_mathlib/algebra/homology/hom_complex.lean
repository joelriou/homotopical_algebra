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

lemma mk_v (v : Π (p q : ℤ) (hpq : q=p+n), F.X p ⟶ G.X q) (p q : ℤ) (hpq : q=p+n) :
  (mk v).v p q hpq = v p q hpq := rfl

@[ext]
lemma ext (z₁ z₂ : cochain F G n) (h : ∀ (p q : ℤ) (hpq : q=p+n), z₁.v p q hpq = z₂.v p q hpq) :
  z₁ = z₂ :=
begin
  ext T,
  rcases T with ⟨p, q, hpq⟩,
  exact h p q hpq,
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
lemma of_hom_eq (φ : F ⟶ G) (p : ℤ) : (of_hom φ).v p p (add_zero p).symm = φ.f p :=
by simp only [of_hom, of_homs_eq]

@[simp]
def of_homotopy {φ₁ φ₂ : F ⟶ G} (ho : homotopy φ₁ φ₂) : cochain F G (-1) :=
cochain.mk (λ p q hpq, ho.hom p q)

def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁ + n₂) :
  cochain F K n₁₂ :=
cochain.mk (λ p q hpq, z₁.v p (p+n₁) rfl ≫ z₂.v (p+n₁) q (by linarith))

notation a ` ≫[` b `] ` c := cochain.comp a c b

lemma comp_eq {n₁ n₂ n₁₂ : ℤ} (z₁ : cochain F G n₁) (z₂ : cochain G K n₂) (h : n₁₂ = n₁+n₂)
  (p₁ p₂ p₃ : ℤ) (h₁ : p₂=p₁+n₁) (h₂ : p₃=p₂+n₂) :
  (comp z₁ z₂ h).v p₁ p₃ (by rw [h₂, h₁, h, add_assoc]) =
  z₁.v p₁ p₂ h₁ ≫ z₂.v p₂ p₃ h₂ := by { subst h₁, refl,}

@[simp]
lemma add_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁': cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (z₁+z₁') z₂ h = comp z₁ z₂ h + comp z₁' z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [add_comp],
end

@[simp]
lemma sub_comp {n₁ n₂ n₁₂ : ℤ} (z₁ z₁': cochain F G n₁) (z₂ : cochain G K n₂)
  (h : n₁₂ = n₁ + n₂) : comp (z₁-z₁') z₂ h = comp z₁ z₂ h - comp z₁' z₂ h :=
begin
  ext,
  dsimp [comp, mk, v],
  simp only [sub_comp],
end

end cochain

end hom_complex

end cochain_complex
