/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.hom_complex_old
import category_theory.abelian.projective

noncomputable theory

open category_theory category_theory.preadditive category_theory.limits category_theory.category

namespace algebra

namespace homology

variables {C : Type*} [category C] [abelian C] (F G : chain_complex C ℤ)

variables {F G}

structure lift_cycle {n : ℤ} (z : hom_complex.Z F G n) (p : ℤ) :=
(y : (hom_complex F G).X (n+1)) (hy : ∀ q, q ≤ p → (hom_complex F G).d (n+1) n y q = z.1 q)

namespace lift_cycle

@[simps]
def of_eq_p {n : ℤ} {z : hom_complex.Z F G n} {p p' : ℤ} (l : lift_cycle z p) (h : p=p') : lift_cycle z p' :=
{ y := l.y,
  hy := λ q hq, l.hy q (by { rw h, exact hq, }), }

end lift_cycle

def lift_cycle_induction {n p : ℤ} (z : hom_complex.Z F G n) (l : lift_cycle z p) (hX : projective (F.X (p+1)))
  (hG : G.cycles (p+1+n) = G.boundaries (p+1+n)) : {l' : lift_cycle z (p+1) // ∀ q, q ≤ p → l'.y q = l.y q} :=
begin
  let u := z.1 (p+1) - ((hom_complex F G).d (n + 1) n) l.y (p+1),
  have du : (G.boundaries (p+1+n)).factors u,
  { rw [← hG, G.cycles_eq_kernel_subobject (show  p+n+1 = p+1+n, by linarith), kernel_subobject_factors_iff],
    let u' := z.1 - ((hom_complex F G).d (n + 1) n) l.y,
    have du' : (hom_complex F G).d n (n-1) u' = 0,
    { dsimp only [u'],
      rw map_sub,
      have hz := z.2,
      dsimp only [hom_complex.Z] at hz,
      rw add_monoid_hom.mem_ker at hz,
      rw [hz, ← comp_apply, (hom_complex F G).d_comp_d (n+1) n (n-1), AddCommGroup.zero_apply, sub_self], },
    have hu' := congr_fun du' (p+1),
    dsimp at hu',
    have hu'' : u' (p + 1 + (n - 1) - n) = 0,
    { dsimp only [u'],
      rw [pi.sub_apply, l.hy (p+1+(n-1)-n) (by linarith), sub_self], },
    rw hu'' at hu',
    simp only [zero_comp, comp_zero, smul_zero, add_zero] at hu',
    rw [show u = u' (p+1), by refl],
    have hG' := eq_to_hom_d G (p+1+n) (p+n) (p+1+n) (p+1+(n-1)) (by linarith) (by linarith),
    simp only [eq_to_hom_refl, id_comp] at hG',
    rw [hG', ← assoc, hu', zero_comp], },
  rw G.boundaries_eq_image_subobject (show p+1+n+1 = p+1+(n+1), by linarith) at du,
  let φ : F.X (p + 1) ⟶ G.X (p + 1 + (n + 1)) := projective.factor_thru (subobject.factor_thru _ u du) (factor_thru_image_subobject _),
  have hφ : φ ≫ G.d (p + 1 + (n + 1)) (p + 1 + n) = u := begin
    rw ← subobject.factor_thru_arrow _ u du,
    dsimp only [φ],
    simp only [subobject.factor_thru_arrow, ← image_subobject_arrow_comp (G.d (p+1+(n+1)) (p+1+n)), ← assoc,
      projective.factor_thru_comp ((subobject.factor_thru _ u du)) (factor_thru_image_subobject _)],
  end,
  let δ : (hom_complex F G).X (n+1) := λ q, begin
    by_cases q = p+1,
    { exact eq_to_hom (by rw h) ≫ φ ≫ eq_to_hom (by rw h), },
    { exact 0, },
  end,
  have hδ₁ : ∀ q, q ≤ p → δ q = 0 := λ q hq, begin
    dsimp [δ],
    split_ifs,
    { exfalso, linarith, },
    { refl, },
  end,
  have hδ₂ : δ (p + 1) ≫ G.d (p + 1 + (n + 1)) (p + 1 + n) = u,
  { dsimp only [δ],
    split_ifs,
    { simpa only [eq_to_hom_refl, comp_id, id_comp] using hφ, },
    { exfalso, exact h rfl, }, },
  let l' : lift_cycle z (p+1) :=
  { y := l.y + δ,
    hy := λ q hq, begin
      rw [map_add, pi.add_apply],
      by_cases q ≤ p,
      { rw [l.hy q h, add_right_eq_self],
        dsimp,
        simp only [hδ₁ q h, hδ₁ (q+n-(n+1)) (by linarith), zero_comp, comp_zero, smul_zero, add_zero], },
      { have hq : q = p+1 := by linarith,
        subst hq,
        conv_lhs { congr, skip, dsimp, },
        simp only [hδ₁ (p+1+n-(n+1)) (by linarith), zero_comp, comp_zero, smul_zero, add_zero, hδ₂],
        dsimp only [u],
        abel, },
    end, },
  refine ⟨l', _⟩,
  intros q hq,
  dsimp,
  rw [add_right_eq_self, hδ₁ q hq],
end

example : 2+2=4 := rfl

def truncate (x : ℤ) : ℕ :=
begin
  by_cases 0 ≤ x,
  { exact (int.eq_coe_of_zero_le h).some, },
  { exact 0, },
end

def truncate_eq_zero (x : ℤ) (hx : x ≤ 0) : truncate x = 0 :=
begin
  dsimp [truncate],
  split_ifs,
  { let z := (int.eq_coe_of_zero_le h).some,
    change z = 0,
    have hz : x = z := (int.eq_coe_of_zero_le h).some_spec,
    have hx : x = 0 := by linarith,
    subst hx,
    rw ← int.coe_nat_eq_coe_nat_iff,
    exact hz.symm, },
  { refl, },
end

def truncate_eq (x : ℕ) : truncate x = x :=
begin
  dsimp [truncate],
  split_ifs,
  { simpa only [int.coe_nat_eq_coe_nat_iff] using (int.eq_coe_of_zero_le h).some_spec.symm, },
  { exfalso,
    exact h (int.coe_zero_le _), },
end

def sub_truncate (a b : ℤ) := truncate (a-b)

lemma coe_sub_truncate {a b : ℤ} (h : b≤a) : (sub_truncate a b : ℤ) = a -b :=
begin
  have h' : 0 ≤ a-b := by linarith,
  cases (int.eq_coe_of_zero_le h') with k hk,
  dsimp only [sub_truncate],
  rw [hk, truncate_eq],
end

def add_sub_truncate {a b : ℤ} (h : b ≤ a) : b + sub_truncate a b = a :=
begin
  rw coe_sub_truncate h,
  linarith,
end

def le_add_sub_truncate (a b : ℤ) : a ≤ b + sub_truncate a b :=
begin
  by_cases b ≤ a,
  { rw add_sub_truncate h, },
  { linarith, },
end

section

variables {n p₀ : ℤ} {z : hom_complex.Z F G n} (l₀ : lift_cycle z p₀) (projF : ∀ p, p₀+1 ≤ p → projective (F.X p))
variables (exactG : ∀ q, p₀+n+1≤q → G.cycles q = G.boundaries q)

include projF exactG l₀

noncomputable
def lift_cycle_rec : Π (k : ℕ), lift_cycle z (p₀+k)
|0 := l₀.of_eq_p (by simp only [int.coe_nat_zero, add_zero])
|(k+1) := (lift_cycle_induction z (lift_cycle_rec k) (projF _ (by linarith)) (exactG _ (by linarith))).1.of_eq_p (by simp only [int.coe_nat_succ, add_assoc])

def lift_cycle_rec_eventually_constant (k : ℕ) (q : ℤ) (hq : q ≤ p₀ + k) : (lift_cycle_rec l₀ projF exactG (k+1)).y q = (lift_cycle_rec l₀ projF exactG k).y q :=
begin
  unfold lift_cycle_rec,
  dsimp only [lift_cycle.of_eq_p],
  exact (lift_cycle_induction z (lift_cycle_rec l₀ projF exactG k) (projF _ (by linarith)) (exactG _ (by linarith))).2 q hq,
end

lemma d_lift_cycle_rec (k : ℕ) (q : ℤ) (hq : q ≤ p₀+k): (hom_complex F G).d (n + 1) n (lift_cycle_rec l₀ projF exactG k).y q = z.1 q :=
begin
  induction k with k hk,
  { dsimp only [lift_cycle_rec, lift_cycle.of_eq_p],
    exact l₀.2 q (by simpa only [int.coe_nat_zero, add_zero] using hq), },
  { dsimp only [lift_cycle_rec, lift_cycle.of_eq_p],
    simp only [int.coe_nat_succ] at hq,
    exact (lift_cycle_induction z (lift_cycle_rec l₀ projF exactG k) (projF _ (by linarith)) (exactG _ (by linarith))).1.hy q (by linarith), },
end

@[simp]
def lift_cycle_infty_y : (hom_complex F G).X (n+1) := λ q,
begin
  refine (lift_cycle_rec l₀ projF exactG _).y q,
  exact truncate (q-p₀),
end

lemma lift_cycle_infty_y_eq (q : ℤ) (k : ℕ) (hq : q≤p₀+k) : lift_cycle_infty_y l₀ projF exactG q = (lift_cycle_rec l₀ projF exactG k).y q :=
begin
  revert hq,
  induction k with k hk,
  { intro hq,
    dsimp only [lift_cycle_infty_y],
    rw truncate_eq_zero,
    simp only [int.coe_nat_zero, add_zero] at hq,
    linarith, },
  { intro hq,
    by_cases q ≤ p₀ + k,
    { rw [hk h, lift_cycle_rec_eventually_constant _ _ _ _ _ h], },
    { dsimp only [lift_cycle_infty_y],
      simp only [int.coe_nat_succ] at hq,
      rw [show q = p₀ + (k+1), by linarith],
      have eq : p₀ + (↑k + 1) - p₀ = k.succ := by simp only [add_tsub_cancel_left, int.coe_nat_succ],
      rw [eq, truncate_eq], }, },
end

lemma lift_cycle_infty_y_eq_l₀ (q : ℤ) (hq : q ≤ p₀) : lift_cycle_infty_y l₀ projF exactG q = l₀.y q :=
by simpa only [lift_cycle_infty_y_eq l₀ projF exactG q 0 (by simpa only [int.coe_nat_zero, add_zero] using hq)]

lemma d_lift_cycle_infty_y_eq (q : ℤ) (k : ℕ) (hq : q≤p₀+k) :
  (hom_complex F G).d (n + 1) n (lift_cycle_infty_y l₀ projF exactG) q =
  (hom_complex F G).d (n + 1) n (lift_cycle_rec l₀ projF exactG k).y q :=
begin
  dsimp only [hom_complex, AddCommGroup.of_hom_apply, add_monoid_hom.coe_mk],
  rw [lift_cycle_infty_y_eq, lift_cycle_infty_y_eq],
  { linarith, },
  { exact hq, },
end

lemma d_lift_cycle_infty : (hom_complex F G).d (n+1) n (lift_cycle_infty_y l₀ projF exactG) = z.1 :=
begin
  ext q,
  rw [d_lift_cycle_infty_y_eq _ _ _ _ _ (le_add_sub_truncate q p₀), d_lift_cycle_rec _ _ _ _ _ (le_add_sub_truncate q p₀)],
end

end

lemma hom_complex_exact (F G : chain_complex C ℤ) [hF₁ : ∀ n, projective (F.X n)] (hF₂ : ∃ p₀, ∀ p, p≤p₀ → is_zero (F.X p))
  (hG : ∀ n, G.cycles n = G.boundaries n) {n : ℤ} (z : hom_complex.Z F G n) :
    ∃ y, (hom_complex F G).d (n+1) n y = z :=
begin
  cases hF₂ with p₀ hp₀,
  let l₀ : lift_cycle z p₀ :=
  { y := 0,
    hy := λ q hq, (hp₀ q hq).eq_of_src _ _, },
  use lift_cycle_infty_y l₀ (λ p hp, hF₁ p) (λ q hq, hG q),
  apply d_lift_cycle_infty,
end

end homology

end algebra
