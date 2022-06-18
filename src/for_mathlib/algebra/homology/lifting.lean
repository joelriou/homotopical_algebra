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

def obs₀ : cochain B X 1 := δ 0 1 (L sq l) - z.1.comp (cochain.of_hom f) (zero_add 1).symm

include sq l hpj

lemma test (a b : ℤ) (h : a =b) : a-b=0 := sub_eq_zero.mpr h

def obs : cochain B K 1 :=
begin
  refine (obs₀ sq l).lift_to_kernel _ hpj,
  dsimp only [obs₀],
  rw [cochain.sub_comp, ← δ_comp_cochain_of_hom _ _ _ (zero_add 1), sub_eq_zero, cochain.comp_assoc₀],
  have foo := twist.dφ g (zero_add 1),
  sorry,
/-  rw ← δ_comp_cochain_of_hom _ _ _ (zero_add 1),
  have eq : (L sq l).comp (cochain.of_hom p) (zero_add 0).symm = cochain.of_hom u :=
  begin
    sorry,
  end,
  simp only [eq, δ_cochain_of_hom],-/
end

lemma obs_comp : cochain.comp (obs sq l hpj) (cochain.of_hom j) (zero_add 1).symm = obs₀ sq l :=
by apply cochain.lift_to_kernel_comp

end lifting

end homology

end algebra