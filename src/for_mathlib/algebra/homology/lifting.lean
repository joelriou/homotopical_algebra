/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.twist_cocycle

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace cochain_complex

namespace lifting

open hom_complex

variables {C : Type*} [category C] [abelian C]

variables {A B K X Y : cochain_complex C ℤ} {n : ℤ} {z : cocycle B A 1} {f : A ⟶ X} (g : twist z ⟶ Y) {p : X ⟶ Y} {j : K ⟶ X}
  (sq : comm_sq f (twist.inr z) p g) (l : Π (q : ℤ), comm_sq.lift_struct ((homological_complex.eval C _ q).map_comm_sq sq))
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

def obs : cocycle B K 1 :=
cocycle.lift_to_kernel (obs₀ sq l) hpj
begin
  have eq₁ : cochain.comp (cochain.of_homs (λ (q : ℤ), (l q).l))
    (cochain.of_hom p) (zero_add 0).symm = cochain.of_hom g,
  { simp only [cochain.of_hom, cochain.of_homs_comp],
    congr' 1,
    ext1 q,
    exact (l q).fac_right, },
  have eq₂ : cochain.comp (δ 0 1 (cochain.of_homs (λ (q : ℤ), (l q).l))) (cochain.of_hom p)
    (add_zero 1).symm = 0,
  { suffices : δ 0 1 (cochain.comp (cochain.of_homs (λ (q : ℤ), (l q).l)) (cochain.of_hom p)
      (zero_add 0).symm) = 0,
    { simpa only [δ_comp_of_second_is_zero_cochain _ _ _ (zero_add 1),
        zero_add, cocycle.δ_cochain_of_hom, cochain.comp_zero] using this, },
    simp only [eq₁, cocycle.δ_cochain_of_hom], },
  simp only [obs₀, cochain.sub_comp, cocycle.mk_coe, cochain.add_comp,
    cochain.comp_assoc_of_third_is_zero_cochain, ← cochain.of_hom_comp, sq.w, L,
    δ_comp_of_second_is_zero_cochain _ _ _ (zero_add 1),
    eq₂, cochain.comp_zero, zero_add,
    eq₁, ← dφ g, φ, cocycle.δ_cochain_of_hom, sub_self],
end

@[simp]
lemma obs_comp :
  cochain.comp (obs sq l hpj : cochain B K 1) (cochain.of_hom j)
    (add_zero 1).symm = ↑(obs₀ sq l) :=
by apply cocycle.lift_to_kernel_comp

variables (w : cochain B K 0) (hw : δ 0 1 w = ↑(obs sq l hpj))
variable (j)

@[simp]
def F : cochain B X 0 := L sq l - cochain.comp w (cochain.of_hom j) (add_zero 0).symm

variable {j}
include hw

lemma dF :
  δ 0 1 (F j sq l w) =
    (z : cochain B A 1).comp (cochain.of_hom f) (add_zero 1).symm :=
by simp only [F, δ_sub, δ_comp_of_second_is_zero_cochain _ _ _ (zero_add 1),
  cocycle.δ_cochain_of_hom, cochain.comp_zero, zero_add, hw, obs_comp, obs₀,
  cocycle.mk_coe, sub_sub_cancel]

lemma lift_of_coboundary : comm_sq.lift_struct sq :=
{ l := twist.desc z (F j sq l w) f (zero_add 1) (dF sq l hpj w hw),
  fac_left' := by apply twist.inr_comp_desc,
  fac_right' := begin
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
