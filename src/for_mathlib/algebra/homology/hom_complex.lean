/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy
import algebra.homology.additive
import algebra.category.Group.abelian

noncomputable theory

open category_theory category_theory.preadditive category_theory.limits category_theory.category

universes v u

namespace algebra

namespace homology

class has_sign (α : Type*) [add_comm_group α] [has_one α] :=
(ε : α → ℤ) (hε : ∀ x y, ε (x+y) = ε x * ε y) (hε₁ : ε 1 = -1)

def ε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : α → ℤ := s.ε
lemma hε {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x y : α) : ε (x+y) = ε x * ε y := by apply s.hε
lemma hε₁ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : ε (1 : α) = -1 := s.hε₁
lemma hε' {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε (x+1) = - ε x := by rw [hε, hε₁, mul_neg, mul_one]
lemma hε₀ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] : ε (0 : α) = 1 :=
by simpa only [add_zero, hε₁, neg_mul, one_mul, neg_inj] using (hε (1 : α) 0).symm
lemma hε'' {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε (x-1) = - ε x :=
begin
  have eq := hε (x-1) 1,
  simp only [sub_add_cancel] at eq,
  simp only [eq, hε₁, mul_neg, mul_one, neg_neg],
end
lemma hε₂ {α : Type*} [add_comm_group α] [has_one α] [s : has_sign α] (x : α) : ε x * ε x = 1 :=
begin
  have eq := hε x (-x),
  simp only [add_right_neg, hε₀] at eq,
  cases int.eq_one_or_neg_one_of_mul_eq_one eq.symm,
  { rw [h, mul_one], },
  { rw [h, mul_neg, mul_one, neg_neg], },
end

variables {C : Type u} [category.{v} C] [preadditive C] {α : Type*} [add_comm_group α] [has_one α]

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

lemma eq_to_hom_f'' {F G : chain_complex C α} (φ : Π i j, F.X i ⟶ G.X j) (i j i' j' : α) (hi : i = i') (hj : j = j') :
  φ i j = eq_to_hom (by rw [hi]) ≫ φ i' j' ≫ eq_to_hom (by rw [hj]) :=
begin
  substs hi hj,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

@[simps]
def hom_complex (F G : chain_complex C α) [has_sign α] : chain_complex AddCommGroup α :=
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
    rw [hε', neg_zsmul, neg_add_eq_zero,
      eq_to_hom_d F q (q+(k+1)-(k+1+1)) q (q-1) rfl (by abel),
      eq_to_hom_d F q (q+k-(k+1)) q (q-1) rfl (by abel),
      eq_to_hom_d G ((q+k-(k+1)+(k+1+1))) (q+k-(k+1)+(k+1)) (q+(k+1)) (q+k) (by abel) (by abel),
      eq_to_hom_f (k+1+1) f (q+(k+1)-(k+1+1)) (q-1) (by abel),
      eq_to_hom_f (k+1+1) f (q+k-(k+1)) (q-1) (by abel)],
    simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id, id_comp],
  end, }

@[simp]
def hom_complex.Z (F G : chain_complex C α) (n : α) [has_sign α]:
  add_subgroup ((hom_complex F G).X n) :=
add_monoid_hom.ker ((hom_complex F G).d n (n-1))

@[simps]
def zero_cycle_of_hom {F G : chain_complex C α} (φ : F ⟶ G) [has_sign α] : hom_complex.Z F G 0 :=
begin
  refine ⟨λ q, φ.f q ≫ eq_to_hom (by abel), _⟩,
  dsimp only [hom_complex.Z],
  rw [add_monoid_hom.mem_ker],
  ext n,
  dsimp,
  simp only [eq_to_hom_d G (n+0) (n+(0-1)) n (n-1) (by abel) (by abel),
    eq_to_hom_d F n (n+(0-1)-0) n (n-1) (by abel) (by abel),
    eq_to_hom_f' φ (n+(0-1)-0) (n-1) (by abel), hε', hε₀],
  simp only [assoc, eq_to_hom_refl, eq_to_hom_trans_assoc, eq_to_hom_trans,
    comp_id, id_comp, neg_smul, one_zsmul, add_right_neg, φ.comm_assoc],
end

@[simps]
def zero_cycle_of_hom_equiv (F G : chain_complex C α) [has_sign α]:
  (F ⟶ G) ≃+ hom_complex.Z F G 0 :=
{ to_fun := λ φ, zero_cycle_of_hom φ,
  inv_fun := λ ψ, begin
    refine ⟨λ n, ψ.1 n ≫ eq_to_hom (by abel), _⟩,
    intros n m hnm,
    change m+1=n at hnm,
    subst hnm,
    have hψ₀ := ψ.2,
    dsimp only [hom_complex.Z] at hψ₀,
    rw add_monoid_hom.mem_ker at hψ₀,
    have hψ₁ := congr_fun hψ₀ (m+1),
    have eq : G.X (m+1+(0-1)) = G.X m := by { congr, abel, },
    have hψ₂ := congr_arg (λ g, g ≫ eq_to_hom eq) hψ₁,
    have h := eq_to_hom_f 0 ψ.1 (m+1+(0-1)-0) m (by abel),
    dsimp at hψ₂ ⊢ h,
    simp only [add_comp, h,
      eq_to_hom_d G (m+1+0) (m+1+(0-1)) (m+1) m (by abel) (by abel),
      eq_to_hom_d F (m+1) (m+1+(0-1)-0) (m+1) m (by abel) (by abel),
      zero_add, hε₁, neg_zsmul, one_zsmul, neg_comp, zero_comp] at hψ₂,
    rw [tactic.ring.add_neg_eq_sub, sub_eq_zero] at hψ₂,
    simpa only [assoc, eq_to_hom_refl, eq_to_hom_trans, eq_to_hom_trans_assoc,
      comp_id, id_comp] using hψ₂,
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

@[simps]
def bij_homotopies {F G : chain_complex C α} (f g : F ⟶ G) [has_sign α] :
  homotopy f g ≃ { z : (hom_complex F G).X 1 // (zero_cycle_of_hom f).1 = (hom_complex F G).d 1 0 z + (zero_cycle_of_hom g).1 } :=
{ to_fun := λ h, begin
    refine ⟨λ n, h.hom n (n+1), _⟩,
    ext n,
    dsimp,
    have comm := h.comm n,
    have h₁ : (complex_shape.down α).rel (n+1) n := rfl,
    have h₂ : (complex_shape.down α).rel n (n+0-1) := by { change (n+0-1)+1 = n, abel, },
    rw [d_next_eq _ h₂, prev_d_eq _ h₁] at comm,
    simp only [← cancel_mono (eq_to_hom (show G.X (n+0) = G.X n, by rw add_zero)), comm,
      add_zero, add_comp, assoc, homological_complex.d_comp_eq_to_hom,
      complex_shape.down_rel, add_left_inj, eq_to_hom_trans, eq_to_hom_refl, comp_id,
      linear.smul_comp, hε', hε₁, neg_neg, one_zsmul, id_comp,
      eq_to_hom_f'' h.hom (n+0-1) (n+0-1+1) (n+0-1) n rfl (by abel)],
    apply add_comm,
  end,
  inv_fun := λ z,
  { hom := λ i j, begin
      by_cases i+1 = j,
      { exact z.1 i ≫ eq_to_hom (by rw h), },
      { exact 0, }
    end,
    zero' := λ i j hij, begin
      change ¬ i+1=j at hij,
      split_ifs,
      refl,
    end,
    comm := λ n, begin
      have hz := congr_fun z.2 n,
      have hz' := eq_to_hom_f 1 z.1 (n+0-1) (n-1) (by abel),
      dsimp at hz hz',
      simp only [← cancel_mono (eq_to_hom (show G.X (n+0) = G.X n, by rw add_zero)),
        add_zero, assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id, add_comp,
        homological_complex.d_comp_eq_to_hom, complex_shape.down_rel, linear.smul_comp, hε', hε₁,
        neg_neg, one_zsmul] at hz,
      have h₁ : (complex_shape.down α).rel (n+1) n := rfl,
      have h₂ : (complex_shape.down α).rel n (n-1) := by { change (n-1)+1 = n, abel, },
      have h₃ : n-1+1=n := by abel,
      rw [d_next_eq _ h₂, prev_d_eq _ h₁],
      split_ifs,
      dsimp,
      simp only [hz, hz', comp_id, add_left_inj,
        eq_to_hom_d F n (n+0-1) n (n-1) rfl (by abel),
        assoc, eq_to_hom_refl, id_comp, eq_to_hom_trans_assoc, eq_to_hom_trans],
      apply add_comm,
    end, },
  left_inv := λ h, begin
    ext i j,
    dsimp,
    split_ifs with hij,
    { subst hij,
      simp only [eq_to_hom_refl, comp_id], },
    { rw h.zero i j hij, },
  end,
  right_inv := λ z, begin
    ext n,
    dsimp,
    split_ifs,
    { rw comp_id, },
    { exfalso,
      apply h,
      refl, },
  end, }

@[simps]
def hom_complex_functor_target_fixed (G : chain_complex C α) [has_sign α] : (chain_complex C α)ᵒᵖ ⥤ chain_complex AddCommGroup α :=
{ obj := λ F, hom_complex F.unop G,
  map := λ F₁ F₂ φ,
  { f := λ n, AddCommGroup.of_hom
    { to_fun := λ f q, φ.unop.f q ≫ f q,
      map_zero' := by { ext q, dsimp, rw comp_zero, },
      map_add' := λ f₁ f₂, by { ext q, dsimp, rw comp_add, }, },
    comm' := λ i j hij, begin
      ext f q,
      simp only [comp_apply],
      dsimp,
      simp only [assoc, comp_add, linear.comp_smul, homological_complex.hom.comm_assoc],
    end, },
  map_id' := λ F, begin
    ext n f q,
    dsimp,
    simp only [id_comp, id_apply],
  end,
  map_comp' := λ F₁ F₂ F₃ φ₁₂ φ₂₃, begin
    ext n f q,
    dsimp,
    simpa only [comp_apply, assoc],
  end, }

def hom_complex_left_homotopies {F₁ F₂ : chain_complex C α} {φ₁ φ₂ : F₁ ⟶ F₂} (h₁₂ : homotopy φ₁ φ₂)
  (G : chain_complex C α) [has_sign α] : homotopy ((hom_complex_functor_target_fixed G).map φ₁.op)
    ((hom_complex_functor_target_fixed G).map φ₂.op) :=
{ hom := λ i j, begin
    by_cases i+1=j,
    { exact AddCommGroup.of_hom
      { to_fun := λ f q, ε i • h₁₂.hom q (q+1) ≫ f (q+1) ≫ eq_to_hom (by { congr' 1, rw ← h, abel, }),
        map_zero' := begin
          ext q,
          dsimp,
          simp only [zero_comp, comp_zero, zsmul_zero],
        end,
        map_add' := λ f₁ f₂, begin
          ext q,
          dsimp,
          simp only [add_comp, comp_add, zsmul_add],
        end },    },
    { exact 0, },
  end,
  zero' := λ i j hij, begin
    change ¬ i+1=j at hij,
    split_ifs,
    refl,
  end,
  comm := λ n, begin
    ext f q,
    have h₁ : (complex_shape.down α).rel (n+1) n := rfl,
    have h₂ : (complex_shape.down α).rel n (n+0-1) := by { change (n+0-1)+1 = n, abel, },
    have h₃ : n+0-1+1=n := by abel,
    have h₄ : (complex_shape.down α).rel (q+1) q := rfl,
    have h₅ : (complex_shape.down α).rel q (q-1) := by { change (q-1)+1 = q, abel, },
    have h₆ := h₁₂.comm q,
    rw [prev_d_eq _ h₄, d_next_eq _ h₅] at h₆,
    rw [d_next_eq _ h₂, prev_d_eq _ h₁],
    dsimp,
    simp only [comp_apply],
    split_ifs,
    dsimp,
    simp only [h₆, hε', hε'', hε₂, assoc, add_comp, comp_add, zsmul_add, zsmul_comp, comp_zsmul, ← add_assoc, add_zero, add_left_inj,
      eq_to_hom_d F₁ q (q+n-(n+1)) q (q-1) rfl (by abel),
      eq_to_hom_f'' h₁₂.hom (q+n-(n+1)) (q+n-(n+1)+1) (q-1) q (by abel) (by abel),
      eq_to_hom_f n f (q+n-(n+1)+1) q (by abel),
      eq_to_hom_d F₂ (q+1) (q+1+(n+0-1)-n) (q+1) q rfl (by abel),
      eq_to_hom_f n f (q+1+(n+0-1)-n) q (by abel),
      eq_to_hom_d G (q+1+n) (q+1+(n+0-1)) (q+(n+1)) (q+n) (by abel) (by abel),
      eq_to_hom_trans, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp, comp_id, neg_neg, smul_smul, neg_mul_neg, one_smul],
    simp only [neg_smul],
    abel,
  end, }

end homology

end algebra
