/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.twist_cocycle
import for_mathlib.category_theory.comm_sq_lift

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.preadditive

namespace algebra

namespace homology

namespace lifting

open hom_complex

variables {C : Type*} [category C] [abelian C]

variables {A B K X Y : cochain_complex C ℤ} {n : ℤ} {z : cocycle B A 1} {f : A ⟶ X} (g : twist z ⟶ Y) {p : X ⟶ Y} {j : K ⟶ X}
  (sq : comm_sq f (twist.ι z) p g) (l : Π q, comm_sq.lifts (sq.apply (homological_complex.eval C _ q)))
  (hpj : ∀ q, short_exact (j.f q) (p.f q))

def φ : cochain B Y 0 := twist.φ g (zero_add 1)
lemma dφ : δ 0 1 (φ g) = cochain.comp z.1 (cochain.of_hom (twist.γ g)) (add_zero 1).symm := twist.dφ g (zero_add 1)

variable {g}

def L : cochain B X 0 := cochain.of_homs (λ q, eq_to_hom (by { congr, linarith, }) ≫ biprod.inl ≫ (l q).l)

include sq l

@[simps]
def obs₀ : cocycle B X 1 :=
begin
  refine ⟨δ 0 1 (L sq l) - z.1.comp (cochain.of_hom f) (add_zero 1).symm, _⟩,
  have hz := z.2,
  rw cocycle.mem_iff 1 2 rfl at ⊢ hz,
  simp only [δ_sub, δδ, zero_sub, neg_eq_zero, δ_comp_cochain_of_hom, hz, cochain.zero_comp],
end

include hpj

@[simps]
def obs : cocycle B K 1 :=
begin
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
end

@[simp]
lemma obs_comp : cochain.comp (obs sq l hpj).1 (cochain.of_hom j) (add_zero 1).symm = (obs₀ sq l).1 :=
by apply cocycle.lift_to_kernel_comp

variables (w : cochain B K 0) (hw : δ 0 1 w = (obs sq l hpj).1)

include w hw

@[simp]
def F : cochain B X 0 := L sq l - w.comp (cochain.of_hom j) (add_zero 0).symm

lemma dF : δ 0 1 (F sq l hpj w hw) = z.1.comp (cochain.of_hom f) (add_zero 1).symm :=
by simp only [F, δ_sub, δ_comp_cochain_of_hom, hw, obs_comp, obs₀, sub_sub_cancel]

lemma lift_of_coboundary : comm_sq.lifts sq :=
{ l := twist.desc z f (zero_add 1) (F sq l hpj w hw) (dF sq l hpj w hw),
  fac_left := by apply twist.ι_desc,
  fac_right := begin
    ext q,
    { simp only [F, homological_complex.comp_f, twist.desc_f, cochain.sub_apply, cochain.comp₀, cochain.of_hom_eq,
        biprod.inl_desc_assoc, sub_comp, assoc,
        cochain.eval' 0 (q+1-1) q (by linarith) q q (by linarith) rfl w,
        cochain.eval' 0 (q+1-1) q (by linarith) q q (by linarith) rfl (L sq l)],
      have hl := (l q).fac_right,
      dsimp at hl,
      simp only [L, cochain.of_homs_eq, eq_to_hom_refl, id_comp, assoc, eq_to_hom_trans_assoc, hl,
        sub_eq_self, is_iso.comp_left_eq_zero, (hpj q).exact.w, comp_zero], },
    { simpa only [homological_complex.comp_f, twist.desc_f, biprod.inr_desc_assoc]
        using homological_complex.congr_hom sq.w q, },
  end, }

end lifting

end homology

end algebra
