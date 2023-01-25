/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.preadditive.projective
import algebra.homology.homological_complex
import category_theory.abelian.basic
import for_mathlib.algebra.homology.twist_cocycle
import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.basic
import for_mathlib.algebra.homology.homological_complex_biprod

noncomputable theory

open category_theory category_theory.category
open category_theory.limits algebraic_topology

open_locale zero_object

namespace category_theory

namespace limits

@[simps]
def is_zero.unique_up_to_iso {C : Type*} [category C]
  {X Y : C} (hX : is_zero X)
  (hY : is_zero Y) : X ≅ Y :=
is_initial.unique_up_to_iso hX.is_initial hY.is_initial

end limits

namespace projective

variables {C : Type*} [category C] [enough_projectives C] [has_zero_object C]

def over' (X : C) : C :=
begin
  by_cases is_zero X,
  { exact 0, },
  { exact (enough_projectives.presentation X).some.P, },
end
lemma over'_eq_zero (X : C) (hX : is_zero X) : over' X = 0 :=
begin
  dsimp [over'],
  split_ifs,
  refl,
end

lemma over'_eq (X : C) (hX : ¬is_zero X) : over' X = over X :=
begin
  dsimp [over'],
  split_ifs,
  refl,
end

def π' (X : C) : over' X ⟶ X :=
begin
  by_cases is_zero X,
  { let e : 0 ≅ X := limits.is_zero.unique_up_to_iso (is_zero_zero C) h,
    refine eq_to_hom (over'_eq_zero X h) ≫ e.hom, },
  { exact eq_to_hom (over'_eq X h) ≫ projective.π X, },
end

instance (X : C) : epi (π' X) :=
by { dsimp only [π'], split_ifs; apply epi_comp, }

instance (X : C) [has_zero_morphisms C] : projective (over' X) :=
begin
  dsimp [over'],
  split_ifs,
  { apply projective.zero_projective, },
  { exact projective.projective_over X,},
end

end projective

end category_theory

namespace cochain_complex

namespace minus

namespace projective_model_structure

variables {C : Type*} [category C] [abelian C] [enough_projectives C]

/-namespace CM5a

open cochain_complex.hom_complex


@[simps]
def P (L : cochain_complex C ℤ) : cochain_complex C ℤ :=
{ X := λ q, category_theory.projective.over' (L.X (q-1)),
  d := λ i j, 0,
  shape' := λ i j hij, rfl,
  d_comp_d' := λ i j k hij hjk, comp_zero, }

instance (L : cochain_complex C ℤ) (n : ℤ) : projective ((P L).X n) :=
by { dsimp [P], apply_instance, }

@[simps]
def Q (L : cochain_complex C ℤ) : cochain_complex C ℤ :=
twist (cocycle.of_hom (𝟙 (P L)))

instance Q_is_degreewise_projective (L : cochain_complex C ℤ) (n : ℤ) :
  projective ((Q L).X n) :=
by { dsimp only [Q, twist], apply_instance, }

@[simps]
def π (L : cochain_complex C ℤ) : Q L ⟶ L :=
begin
  refine twist.desc (cocycle.of_hom (𝟙 (P L))) (cochain.mk _) _ (neg_add_self 1) _,
  { exact (λ p q hpq, category_theory.projective.π' _ ≫ eq_to_hom (by { congr, linarith})), },
  { exact { f := λ i, category_theory.projective.π' _ ≫ L.d (i-1) i, }, },
  { ext,
    simp only [δ_v (-1) 0 rfl _ p p (add_zero p).symm (p-1) (p+1) rfl rfl,
      add_zero, zero_comp, cochain.mk_v, eq_to_hom_refl, comp_id, P_d,
      smul_zero, cocycle.of_hom_coe, cochain.id_comp, cochain.of_hom_v],
    },
end

lemma π_is_degreewise_epi (L : cochain_complex C ℤ) :
  projective_structure.arrow_classes.fib (π L) :=
begin
  intro n,
  have h : epi ((cochain.comp (twist.inl _ (show -(1 : ℤ)+1 = 0, by linarith))
    (cochain.of_hom (π L)) (add_zero (-1)).symm).v (n+1) n (by linarith)),
  { dsimp only [π, twist.desc, hom_complex.twist.desc_hom_as_cocycle],
    simp only [cocycle.cochain_of_hom_hom_of_eq_coe, twist.desc_cocycle_coe],
    rw twist.inl_comp_desc_cochain,
    dsimp,
    apply epi_comp, },
  simp only [cochain.comp_v _ _ (add_zero (-(1 : ℤ))).symm (n+1) n n
    (by linarith) (by linarith), cochain.of_hom_v] at h,
  simp only [twist.inl, cochain.mk, cochain.v, cochain.of_hom, cochain.of_homs,
    homological_complex.id_f, id_comp] at h,
  exact @epi_of_epi _ _ _ _ _ _ _ h,
end

@[simps]
def id_Q_homotopy_to_zero (L : cochain_complex C ℤ) :
  homotopy (𝟙 (Q L)) 0 :=
begin
  equiv_rw hom_complex.equiv_homotopy _ _,
  refine ⟨cochain.comp (twist.snd _ ) (twist.inl _ (by linarith)) (zero_add (-1)).symm, _⟩,
  dsimp only [Q],
  simpa only [add_zero, add_left_neg, eq_self_iff_true, δ_comp_of_first_is_zero_cochain,
    twist.δ_inl, cocycle.of_hom_coe, cochain.id_comp, cochain.of_hom_zero,
    twist.δ_snd _ (zero_add 1), ε_odd _ odd_neg_one, zsmul_neg, cochain.neg_comp, neg_zsmul,
    one_zsmul, neg_neg, twist.id_eq _ (show -(1 : ℤ)+1=0, by linarith) (zero_add 1),
    cochain.comp_id] using add_comm _ _,
end

variables {K L : cochain_complex C ℤ} (f : K ⟶ L)

include f
@[simps, nolint unused_arguments]
def obj := homological_complex.biprod K (Q L)

@[simps]
def i : K ⟶ obj f := homological_complex.biprod.inl

@[simps]
def p : obj f ⟶ L := homological_complex.biprod.desc f (π L)

@[simp, reassoc]
lemma fac : i f ≫ p f = f :=
by simp only [i, p, homological_complex.biprod.inl_desc]

lemma p_is_fib :
  projective_structure.arrow_classes.fib (p f) :=
begin
  intro n,
  have h : biprod.inr ≫ biprod.desc (f.f n) ((π L).f n) = (π L).f n := biprod.inr_desc _ _,
  haveI : epi ((π L).f n) := π_is_degreewise_epi L n,
  exact epi_of_epi_fac h,
end

lemma i_is_cof :
  projective_structure.arrow_classes.cof (i f) :=
begin
  intro n,
  apply preadditive.mono_with_projective_coker.of_biprod_inl,
end

def homotopy_equiv_i : homotopy_equiv K (obj f) :=
{ hom := i f,
  inv := homological_complex.biprod.fst,
  homotopy_hom_inv_id := by { simp only [i, homological_complex.biprod.inl_fst], },
  homotopy_inv_hom_id := begin
    symmetry,
    equiv_rw homotopy.equiv_sub_zero,
    dsimp only [obj, i],
    simpa only [zero_comp, comp_zero, id_comp, ← homological_complex.biprod.total,
      add_sub_cancel'] using ((id_Q_homotopy_to_zero L).comp_right
        homological_complex.biprod.inr).comp_left homological_complex.biprod.snd,
  end, }

lemma i_is_weq :
  projective_structure.arrow_classes.weq (i f) :=
(homotopy_equiv_i f).to_quasi_iso

lemma i_is_triv_cof :
  projective_structure.arrow_classes.triv_cof (i f) := ⟨i_is_cof f, i_is_weq f⟩

end CM5a

end projective_structure

end cochain_complex

namespace bounded_above_cochain_complex

namespace projective_model_structure

variables {C : Type*} [category C] [abelian C] [enough_projectives C]

namespace CM5a

variables {K L : bounded_above_cochain_complex C} (f : K ⟶ L)

open cochain_complex.projective_structure
include f

@[simps, nolint unused_arguments]
def obj : bounded_above_cochain_complex C := ⟨CM5a.obj f,
begin
  apply cochain_complex.is_bounded_above.of_biprod,
  { exact K.2, },
  { apply cochain_complex.hom_complex.twist.is_bounded_above,
    all_goals {
      cases L.2 with l hl,
      use (l+1),
      intros i hi,
      dsimp,
      rw category_theory.projective.over'_eq_zero, swap,
      { apply hl,
        linarith, },
      apply is_zero_zero, }, },
end⟩

@[simps]
def i : K ⟶ obj f := CM5a.i f

@[simps]
def p : obj f ⟶ L := CM5a.p f

lemma fac : i f ≫ p f = f := CM5a.fac f

lemma p_is_fib : arrow_classes.fib (p f) := CM5a.p_is_fib f

lemma i_is_triv_cof : arrow_classes.triv_cof (i f) := CM5a.i_is_triv_cof f

end CM5a-/

lemma CM5a' {X Z : minus C} (f : X ⟶ Z) (n : ℤ) [X.obj.is_strictly_le n]
  [Z.obj.is_strictly_le n] : ∃ (Y : minus C)
  (hY : Y.obj.is_strictly_le n) (i : X ⟶ Y) (p : Y ⟶ Z)
  (hi : (arrow_classes C).triv_cof i) (hp : (arrow_classes C).fib p), i ≫ p = f := sorry

lemma CM5a : (arrow_classes C).CM5a :=
λ X Z f, begin
  obtain ⟨nX, hX⟩ := X.property,
  obtain ⟨nZ, hZ⟩ := Z.property,
  haveI := hX,
  haveI := hZ,
  let n := max nX nZ,
  haveI : X.obj.is_strictly_le n := is_strictly_le_of_le _ _ _ (le_max_left _ _),
  haveI : Z.obj.is_strictly_le n := is_strictly_le_of_le _ _ _ (le_max_right _ _),
  obtain ⟨Y, hY, i, p, hi, hp, fac⟩ := CM5a' f n,
  exact ⟨Y, i, hi, p, hp, fac⟩,
end

end projective_model_structure

end minus

end cochain_complex
