/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebra.homology.termwise_split
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
def obs₀ : cocycle B X 1 :=
begin
  refine ⟨δ 0 1 (L sq l) - z.1.comp (cochain.of_hom f) (add_zero 1).symm, _⟩,
  have hz := z.2,
  rw cocycle.mem_iff 1 2 rfl at ⊢ hz,
  simp only [δ_sub, δδ, zero_sub, neg_eq_zero, δ_comp_cochain_of_hom, hz, cochain.zero_comp],
end

include hpj

def obs₁ : cocycle B K 1 :=
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

lemma obs₁_comp : cochain.comp (obs₁ sq l hpj).1 (cochain.of_hom j) (zero_add 1).symm = (obs₀ sq l).1 :=
by apply cocycle.lift_to_kernel_comp

end lifting

end homology

end algebra