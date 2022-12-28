/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

/-
The purpose of this file is to show that a bounded above complexes of
projective objects in an abelian category is K-projective. It is now
broken due to the homology refactor...
-/

/-
import for_mathlib.algebra.homology.hom_complex
import category_theory.abelian.projective

namespace cochain_complex

open category_theory category_theory.category category_theory.limits

variables {C : Type*} [category C] [abelian C] {F G : cochain_complex C ℤ}

namespace hom_complex

structure lift_cycle {n : ℤ} (z : cocycle F G n) (N : ℤ) :=
(y : cochain F G (n-1)) (hy : ∀ p q hpq, N < p → (δ (n-1) n y).v p q hpq= (z : cochain F G n).v p q hpq)

namespace lift_cycle

noncomputable theory

@[simps]
def of_eq_N {n : ℤ} {z : cocycle F G n} {N N' : ℤ} (l : lift_cycle z N) (h : N=N') : lift_cycle z N' :=
{ y := l.y,
  hy := by { subst h, exact l.hy, }, }

def induction {n N : ℤ} {z : cocycle F G n} (l : lift_cycle z N)
  (hX : projective (F.X N))
  (hG : G.cycles (N+n) = G.boundaries (N+n)) :
  {l' : lift_cycle z (N-1) // ∀ p q hpq, N < p → l'.y.v p q hpq = l.y.v p q hpq} :=
begin
  let u := (↑z - δ (n-1) n l.y).v N (N+n) rfl,
  have hu : (↑z : cochain F G n).v N (N+n) rfl = (δ (n-1) n l.y).v N (N+n) rfl + u,
  { dsimp only [u],
    rw cochain.sub_v,
    abel, },
  have du : (G.boundaries (N+n)).factors u,
  { rw [← hG, G.cycles_eq_kernel_subobject (show N+n+1=N+n+1, by refl),
      kernel_subobject_factors_iff],
    let u' := ↑z - δ (n-1) n l.y,
    have du' : δ n (n+1) u' = 0,
    { dsimp only [u'],
      rw [δ_sub, δδ, sub_zero, cocycle.δ_eq_zero], },
    have hu' := cochain.congr_v du' N (N+n+1) (by linarith),
    have hu'' : u'.v (N + 1) (N + n + 1) (by linarith) = 0,
    { dsimp only [u'],
      simp only [cochain.sub_v, l.hy (N+1) (N+n+1) (by linarith) (lt_add_one N), sub_self], },
    rw [δ_v n (n+1) rfl u' N (N+n+1) (by linarith) (N+n) (N+1) (by linarith) rfl,
      cochain.zero_v] at hu',
    rw ← hu',
    symmetry,
    simp only [add_right_eq_self, hu'', comp_zero, smul_zero], },
  rw G.boundaries_eq_image_subobject (show (N+n-1)+1=N+n, by linarith) at du,
  let φ : F.X N ⟶ G.X (N+n-1) := projective.factor_thru (subobject.factor_thru _ u du) (factor_thru_image_subobject _),
  have hφ : φ ≫ G.d (N+n-1) (N+n) = u,
  { rw ← subobject.factor_thru_arrow _ u du,
    dsimp only [φ],
    simp only [subobject.factor_thru_arrow, ← image_subobject_arrow_comp (G.d (N+n-1) (N+n)),
      ← assoc, projective.factor_thru_comp ((subobject.factor_thru _ u du))
        (factor_thru_image_subobject _)], },
  let w : cochain F G (n-1) := cochain.mk (λ p q hpq, begin
    by_cases p=N,
    { refine eq_to_hom (by rw h) ≫ φ ≫ eq_to_hom (by { congr, linarith, }), },
    { exact 0, },
  end),
  have hw₁ : ∀ p q hpq, N < p → w.v p q hpq = 0,
  { intros p q hpq hp,
    apply dif_neg,
    linarith, },
  let l' : lift_cycle z (N-1) :=
  { y := l.y + w,
    hy := λ p q hpq hp, begin
      have hp' : N ≤ p := by linarith,
      obtain (hp₁ | hp₂) := hp'.lt_or_eq,
      { simp only [δ_add, cochain.add_v, l.hy p q hpq hp₁, add_right_eq_self,
          δ_v (n-1) n (by linarith) w p q hpq _ _ rfl rfl, hw₁ p (q-1) (by linarith) hp₁,
          hw₁ (p+1) q (by linarith) (by linarith),
          zero_add, zero_comp, comp_zero, smul_zero], },
      { substs hp₂ hpq,
        simp only [δ_add, cochain.add_v, hu],
        congr' 1,
        simp only [δ_v (n-1) n (by linarith) w N (N+n) rfl _ _ rfl rfl,
          hw₁ (N+1) (N+n) (by linarith) (lt_add_one N), comp_zero, smul_zero, add_zero,
          ← hφ],
        congr' 1,
        dsimp only [w, cochain.mk, cochain.v],
        simp only [dif_pos, eq_to_hom_refl, comp_id, id_comp], },
    end, },
  refine ⟨l', λ p q hpq hp, by simpa only [cochain.add_v, add_right_eq_self]
    using hw₁ p q hpq hp⟩,
end

section

variables {n N₀ : ℤ} {z : cocycle F G n} (l₀ : lift_cycle z N₀) (projF : ∀ p, p ≤ N₀ → projective (F.X p))
variables (exactG : ∀ q, q ≤ N₀+n → G.cycles q = G.boundaries q)


noncomputable
def sequence : Π (k : ℕ), lift_cycle z (N₀-k)
|0 := l₀.of_eq_N (by simp only [int.coe_nat_zero, sub_zero])
|(k+1) := ((sequence k).induction (projF _ (by simp only [sub_le_self_iff, int.coe_nat_nonneg]))
    (exactG _ (by simp only [add_le_add_iff_right, sub_le_self_iff,
      int.coe_nat_nonneg]))).1.of_eq_N (by { simp only [int.coe_nat_succ], linarith, })

lemma sequence_is_eventually_constant {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (p q : ℤ) (hpq : q=p+(n-1)) (hp : N₀ < p+k₁) :
  (sequence l₀ projF exactG (k₁)).y.v p q hpq = (sequence l₀ projF exactG k₂).y.v p q hpq :=
begin
  rw le_iff_exists_add at hk,
  cases hk with d hd,
  subst hd,
  induction d with d hd,
  { refl, },
  { rw hd,
    rw [show k₁+d.succ = k₁+d+1, by exact (add_assoc k₁ d 1).symm],
    unfold sequence,
    symmetry,
    refine (induction (sequence l₀ projF exactG (k₁+d)) (projF _ _)
      (exactG _ _)).2 p q hpq _,
    { simp only [int.coe_nat_add, sub_le_self_iff], linarith, },
    { simp only [int.coe_nat_add, add_le_add_iff_right, sub_le_self_iff], linarith, },
    { have h := int.coe_zero_le d, simp only [int.coe_nat_add], linarith, }, },
end

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

lemma self_lt_truncate (x : ℤ) : x ≤ truncate x :=
begin
  by_cases x ≤ 0,
  { rw truncate_eq_zero _ h,
    exact h, },
  { cases int.eq_coe_of_zero_le (show 0 ≤ x, by linarith) with m hm,
    simp only [hm, truncate_eq], }
end

lemma truncate_lt_iff (x : ℤ) (y : ℕ) : truncate x ≤ y ↔ x ≤ (y : ℤ) :=
begin
  by_cases x ≤ 0,
  { rw truncate_eq_zero _ h,
    simp only [zero_le, true_iff],
    linarith, },
  { cases int.eq_coe_of_zero_le (show 0 ≤ x, by linarith) with m hm,
    simp only [hm, truncate_eq, int.coe_nat_le], },
end

@[simp]
def sequence_limit : cochain F G (n-1) := cochain.mk (λ p q hpq,
  (sequence l₀ projF exactG (truncate (N₀+1-p))).y.v p q hpq)

def sequence_limit_v_eq (p q : ℤ) (hpq : q=p+(n-1)) (k : ℕ) (hk : N₀+1 ≤ p + ↑k) :
  (sequence_limit l₀ projF exactG).v p q hpq =
  (sequence l₀ projF exactG k).y.v p q hpq :=
begin
  revert hk,
  induction k with k hk,
  { intro hp,
    have h : truncate (N₀+1-p) = 0,
    { apply truncate_eq_zero,
      simp only [int.coe_nat_zero, add_zero] at hp,
      linarith, },
    simp only [sequence_limit, cochain.mk, cochain.v],
    congr', },
  { intro hp,
    simp only [sequence_limit, cochain.mk, cochain.v],
    dsimp only,
    apply sequence_is_eventually_constant,
    { rw truncate_lt_iff,
      linarith, },
    { have h := self_lt_truncate (N₀+1-p),
      linarith, }, },
end

lemma δ_sequence_limit_v (p q : ℤ) (hpq : q=p+n) (k : ℕ) (hk : N₀+1 ≤ p+k):
  (δ (n-1) n (sequence_limit l₀ projF exactG)).v p q hpq =
  (δ (n-1) n (sequence l₀ projF exactG k).y).v p q hpq :=
begin
  simp only [δ_v (n-1) n (by linarith) _ p q hpq _ _ rfl rfl],
  rw [sequence_limit_v_eq, sequence_limit_v_eq],
  all_goals { linarith, },
end

lemma δ_sequence_limit : δ (n-1) n (sequence_limit l₀ projF exactG) = ↑z :=
begin
  ext p q hpq,
  have h := self_lt_truncate (N₀+1-p),
  rw δ_sequence_limit_v l₀ projF exactG p q hpq (truncate (N₀+1-p)) (by linarith),
  exact (sequence l₀ projF exactG _).hy _ _ _ (by linarith),
end

end

end lift_cycle

lemma exact_of_bounded_above_termwise_projective_src_and_acyclic_tgt (F G : cochain_complex C ℤ)
  [hF₁ : ∀ n, projective (F.X n)] (hF₂ : ∃ N₀, ∀ p, N₀ < p → is_zero (F.X p))
  (hG : ∀ n, G.cycles n = G.boundaries n) {n m : ℤ} (z : hom_complex.cocycle F G n)
  (hnm : m+1=n) : ∃ y, (hom_complex F G).d m n y = z.1 :=
begin
  have hm : m = n-1 := by linarith,
  subst hm,
  cases hF₂ with N₀ hN₀,
  let l₀ : lift_cycle z N₀ :=
  { y := 0,
    hy := λ p q hpq hp, (hN₀ p hp).eq_of_src _ _, },
  use l₀.sequence_limit (λ p hp, hF₁ p) (λ q hq, hG q),
  apply lift_cycle.δ_sequence_limit,
end

end hom_complex

end cochain_complex
-/
