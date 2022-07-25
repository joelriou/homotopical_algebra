/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

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

def induction {n N : ℤ} (z : cocycle F G n) (l : lift_cycle z N)
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

end lift_cycle

lemma exact_of_bounded_above_termwise_projective (F G : cochain_complex C ℤ) [hF₁ : ∀ n, projective (F.X n)] (hF₂ : ∃ p₀, ∀ p, p≤p₀ → is_zero (F.X p))
  (hG : ∀ n, G.cycles n = G.boundaries n) {n m : ℤ} (z : hom_complex.cocycle F G n)
  (hnm : n+1=m) : ∃ y, (hom_complex F G).d m n y = z.1 :=
begin
  sorry
end

end hom_complex

end cochain_complex
