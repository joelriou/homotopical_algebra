/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.additive
import algebra.category.Group.abelian

noncomputable theory

open category_theory category_theory.preadditive category_theory.limits category_theory.category

universes v u

namespace algebra

namespace homology

class has_sign (α : Type*) [add_comm_group α] [has_one α] :=
(ε : α → ℤ) (hε : ∀ x, ε (x+1) = - ε x) (hε₀ : ε 0 = 1)

def ε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : α → ℤ := s.ε
def hε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε (x+1) = - ε x := by apply s.hε
def hε₀ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : ε (0 : α) = 1 := s.hε₀

variables {C : Type u} [category.{v} C] [preadditive C] {α : Type*} [add_comm_group α] [has_one α] [has_sign α]

lemma eq_to_hom_f {F G : chain_complex C α} (n : α) (φ : Π q, (F.X q ⟶ G.X (q+n))) (q q' : α) (h : q = q') :
φ q = eq_to_hom (by rw h) ≫ φ q' ≫ eq_to_hom (by rw h) :=
begin
  subst h,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

lemma eq_to_hom_d (F : chain_complex C α) (i j i' j' : α) (hi : i = i') (hj : j = j') :
  F.d i j = eq_to_hom (by rw hi) ≫ F.d i' j' ≫ eq_to_hom (by rw hj) :=
begin
  substs hi hj,
  simp only [eq_to_hom_refl, id_comp, comp_id],
end

lemma eq_to_hom_f' {F G : chain_complex C α} (φ : F ⟶ G) (n n' : α) (h : n=n') :
φ.f n = eq_to_hom (by rw h) ≫ φ.f n' ≫ eq_to_hom (by rw h) :=
begin
  subst h,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

@[simps]
def hom_complex (F G : chain_complex C α) : chain_complex AddCommGroup α :=
{ X := λ n, AddCommGroup.of (Π q, (F.X q ⟶ G.X (q+n))),
  d := λ n m, AddCommGroup.of_hom 
    { to_fun := λ f q, f q ≫ G.d (q+n) (q+m) + ε (n+1) • 
        F.d q (q+m-n) ≫ f _ ≫ eq_to_hom (by { congr' 1, apply sub_add_cancel,}),
      map_zero' := by tidy,
      map_add' := λ f g, begin
        ext q,
        simp only [pi.add_apply, add_comp, comp_add, smul_add],
        abel,
      end, },
  shape' := λ m n hmn, begin
    ext f q,
    dsimp at f ⊢,
    change ¬ (n+1) = m at hmn,
    rw [F.shape, G.shape, comp_zero, zero_comp, smul_zero, add_zero],
    { change ¬ (q+n)+1 = q+m,
      intro h,
      rw [add_assoc, add_right_inj] at h,
      exact hmn h, },
    { change ¬ (q+n-m)+1 = q,
      intro h,
      apply hmn,
      rw eq_sub_of_add_eq' h,
      abel, },
  end,
  d_comp_d' := λ i j k hij hjk, begin
    change j+1 = i at hij,
    change k+1 = j at hjk,
    substs hij hjk,
    ext f q,
    simp only [comp_apply],
    dsimp,
    simp only [sub_add_cancel, add_comp, category.assoc, homological_complex.d_comp_d, comp_zero,
      linear.smul_comp, zero_add, comp_add, linear.comp_smul,
      homological_complex.d_comp_d_assoc, zero_comp, smul_zero, add_zero],
    rw [hε, neg_zsmul, neg_add_eq_zero,
      eq_to_hom_d F q (q+(k+1)-(k+1+1)) q (q-1) rfl (by abel),
      eq_to_hom_d F q (q+k-(k+1)) q (q-1) rfl (by abel),
      eq_to_hom_d G ((q+k-(k+1)+(k+1+1))) (q+k-(k+1)+(k+1)) (q+(k+1)) (q+k) (by abel) (by abel),
      eq_to_hom_f (k+1+1) f (q+(k+1)-(k+1+1)) (q-1) (by abel),
      eq_to_hom_f (k+1+1) f (q+k-(k+1)) (q-1) (by abel)],
    simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id, id_comp],
  end, }

@[simp]
def hom_complex.Z (F G : chain_complex C α) (n : α) :
  add_subgroup ((hom_complex F G).X n) :=
add_monoid_hom.ker ((hom_complex F G).d n (n-1))

def e (F G : chain_complex C α) :
  (F ⟶ G) ≃+ hom_complex.Z F G 0 :=
{ to_fun := λ φ, begin
    refine ⟨λ q, φ.f q ≫ eq_to_hom (by abel), _⟩,
    dsimp only [hom_complex.Z],
    rw [add_monoid_hom.mem_ker],
    ext n,
    dsimp,
    simp only [eq_to_hom_d G (n+0) (n+(0-1)) n (n-1) (by abel) (by abel),
      eq_to_hom_d F n (n+(0-1)-0) n (n-1) (by abel) (by abel),
      eq_to_hom_f' φ (n+(0-1)-0) (n-1) (by abel), hε, hε₀],
    simp only [assoc, eq_to_hom_refl, eq_to_hom_trans_assoc, eq_to_hom_trans,
      comp_id, id_comp, neg_smul, one_zsmul, add_right_neg, φ.comm_assoc],
  end,
  inv_fun := λ ψ, begin
    refine ⟨λ n, ψ.1 n ≫ eq_to_hom (by abel), _⟩,
    sorry,
  end,
  left_inv := λ φ, begin
    ext n,
    dsimp,
    simp only [assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id],
  end,
  right_inv := λ ψ, begin
    ext n,
    dsimp,
    simp only [assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id],
  end,
  map_add' := λ φ₁ φ₂, begin
    ext q,
    dsimp,
    rw add_comp,
  end, }
end homology

end algebra