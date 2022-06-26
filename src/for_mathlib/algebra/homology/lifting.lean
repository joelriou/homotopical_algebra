/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.twist_cocycle
import for_mathlib.category_theory.comm_sq_lift

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace cochain_complex

namespace lifting

open hom_complex

variables {C : Type*} [category C] [abelian C]

variables {A B K X Y : cochain_complex C ℤ} {n : ℤ} {z : cocycle B A 1} {f : A ⟶ X} (g : twist z ⟶ Y) {p : X ⟶ Y} {j : K ⟶ X}
  (sq : comm_sq f (twist.inr z) p g) (l : Π q, comm_sq.lifts (sq.apply (homological_complex.eval C _ q)))
  (hpj : is_termwise_kernel j p)

@[simp]
def φ : cochain B Y 0 := cochain.comp (twist.inl z (zero_add 1)) (cochain.of_hom g) (zero_add 0).symm

lemma dφ : δ 0 1 (φ g) = cochain.comp ↑z (cochain.of_hom (twist.inr z ≫ g)) (add_zero 1).symm :=
by simp only [φ, add_left_eq_self, δ_comp_of_second_is_zero_cochain,
  cocycle.δ_cochain_of_hom, cochain.comp_zero, twist.δ_inl,
  cochain.comp_assoc_of_third_is_zero_cochain, cochain.of_hom_comp]

variable {g}

@[simp]
def L : cochain B X 0 := cochain.comp (twist.inl z (zero_add 1))
  (cochain.of_homs (λ q, (l q).l)) (zero_add 0).symm

include sq l

@[simps]
def obs₀ : cocycle B X 1 :=
cocycle.mk (δ 0 1 (L sq l) - cochain.comp ↑z (cochain.of_hom f) (add_zero 1).symm) 2 rfl
(by simp only [δ_sub, δδ, zero_sub, δ_comp_of_second_is_zero_cochain _ _ 2 rfl, neg_zero,
    cocycle.δ_eq_zero, cocycle.δ_cochain_of_hom, cochain.comp_zero, cochain.zero_comp, add_zero])


include hpj

--@[simps]
def obs : cocycle B K 1 :=
cocycle.lift_to_kernel (obs₀ sq l) hpj
begin
  sorry
end
/-begin
  refine cocycle.lift_to_kernel (obs₀ sq l) _ hpj,
  dsimp only [obs₀],
  rw [cochain.sub_comp, ← δ_comp_cochain_of_hom _ _ _, sub_eq_zero, cochain.comp_assoc₀],
  have hg := twist.dφ g (zero_add 1),
  simp only [twist.γ] at hg,
  simp only [cochain.cochain_of_hom_comp, sq.w, ← hg],
  congr' 1,
  ext q q' hqq',
  have hq' : q = q' := by linarith,
  subst hq',
  have hl := (l q).fac_right,
  dsimp at hl,
  simp only [cochain.comp_eq _ _ (zero_add 0).symm q q q (by linarith) (by linarith),
    L, cochain.of_homs_eq, cochain.of_hom_eq, twist.φ, ← hl, assoc],
end-/

@[simp]
lemma obs_comp :
  cochain.comp (obs sq l hpj : cochain B K 1) (cochain.of_hom j)
    (add_zero 1).symm = ↑(obs₀ sq l) :=
by apply cocycle.lift_to_kernel_comp

variables (w : cochain B K 0) (hw : δ 0 1 w = ↑(obs sq l hpj))

@[simp]
def F : cochain B X 0 := L sq l - cochain.comp w (cochain.of_hom j) (add_zero 0).symm

include hw
lemma dF :
  δ 0 1 (F sq l hpj w) =
    (z : cochain B A 1).comp (cochain.of_hom f) (add_zero 1).symm :=
by simp only [F, δ_sub, δ_comp_of_second_is_zero_cochain _ _ _ (zero_add 1),
  cocycle.δ_cochain_of_hom, cochain.comp_zero, zero_add, hw, obs_comp, obs₀,
  cocycle.mk_coe, sub_sub_cancel]

lemma lift_of_coboundary : comm_sq.lifts sq :=
{ l := twist.desc z (F sq l hpj w) f (zero_add 1) (dF sq l hpj w hw),
  fac_left := by apply twist.inr_comp_desc,
  fac_right := begin
    apply cochain.of_hom_injective,
    simp only [twist.desc, cochain.of_hom_comp,cocycle.cochain_of_hom_hom_of_eq_coe,
      twist.desc_hom_as_cocycle_coe,
      twist.cochain_ext z _ _ (zero_add 1) (zero_add 0).symm,
      ← cochain.comp_assoc_of_third_is_zero_cochain, twist.inl_comp_desc_cochain,
      twist.inr_comp_desc_cochain],
    split,
    { ext i,
      have hl := (l i).fac_right,
      simp only [homological_complex.eval_map] at hl,
      simp only [F, L, hl, cochain.sub_comp, cochain.comp_assoc_of_third_is_zero_cochain,
        cochain.sub_v, cochain.comp_zero_cochain, cochain.of_homs_v, cochain.of_hom_v,
        sub_eq_self, hpj.zero i, comp_zero], },
    { simp only [← cochain.of_hom_comp, sq.w], },
  end }

end lifting

end cochain_complex
