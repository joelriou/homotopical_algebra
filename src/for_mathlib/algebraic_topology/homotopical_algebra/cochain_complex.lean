/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.model_category
import category_theory.abelian.basic
import category_theory.preadditive.projective
import algebra.homology.homological_complex
import algebra.homology.quasi_iso
import for_mathlib.category_theory.limits.kernel_functor
import for_mathlib.algebra.homology.twist_cocycle
import tactic.linarith

noncomputable theory

open category_theory category_theory.limits category_theory.category
open algebraic_topology cochain_complex.hom_complex

open_locale zero_object

variables (C : Type*) [category C] [abelian C]

namespace cochain_complex

@[derive category]
def Cminus := { K : cochain_complex C ℤ // K.is_bounded_above }

namespace Cminus

variable {C}

@[simps]
def mk (K : cochain_complex C ℤ) (hK : K.is_bounded_above) : Cminus C := ⟨K, hK⟩

def homology_functor (i : ℤ) : Cminus C ⥤ C := induced_functor _ ⋙ homology_functor _ _ i

def eval (i : ℤ) : Cminus C ⥤ C := induced_functor _ ⋙ homological_complex.eval _ _ i

namespace projective_structure

variable (C)

def arrow_classes : category_with_fib_cof_weq (Cminus C) :=
{ weq := λ w, quasi_iso w.hom,
  fib := λ w, ∀ n, epi (w.hom.f n),
  cof := λ w, ∀ n, mono (w.hom.f n) ∧ (projective (cokernel (w.hom.f n))), }

variable {C}

def CM2 : (arrow_classes C).CM2 :=
{ of_comp := λ X Y Z f g (hf : quasi_iso f) (hg : quasi_iso g), begin
    haveI := hf,
    haveI := hg,
    exact quasi_iso_comp f g,
  end,
  of_comp_left := λ X Y Z f g (hf : quasi_iso f) (hfg : quasi_iso (f ≫ g)), begin
    haveI := hf,
    haveI := hfg,
    convert quasi_iso_of_comp_left f g,
  end,
  of_comp_right := λ X Y Z f g (hg : quasi_iso g) (hfg : quasi_iso (f ≫ g)), begin
    haveI := hg,
    haveI := hfg,
    convert quasi_iso_of_comp_right f g,
  end, }

def CM3 : (arrow_classes C).CM3 :=
{ weq := λ X₁ X₂ Y₁ Y₂ f g hfg hg, ⟨λ n, begin
    have hfg' := is_retract.imp_of_functor (homology_functor n).map_arrow
      (arrow.mk f) (arrow.mk g) hfg,
    apply arrow_class.is_stable_by_retract.for_isomorphisms _ _ hfg',
    apply hg.1,
  end⟩,
  cof := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, begin
    split,
    { exact arrow_class.is_stable_by_retract.for_monomorphisms _ _
      (is_retract.imp_of_functor (eval n).map_arrow _ _ hfg) (hg n).1, },
    { exact projective.of_retract (is_retract.imp_of_functor
      ((eval n).map_arrow ⋙ limits.cokernel_functor C) _ _ hfg) (hg n).2, },
  end,
  fib := λ X₁ X₂ Y₁ Y₂ f g hfg hg n, arrow_class.is_stable_by_retract.for_epimorphisms _ _
      (is_retract.imp_of_functor (eval n).map_arrow _ _ hfg) (hg n), }

def CM4 : (arrow_classes C).CM4 := sorry

variable [enough_projectives C]

namespace CM5a

def P (L : Cminus C) (q : ℤ) : C :=
begin
  by_cases is_zero (L.1.X q),
  { exact 0, },
  { exact projective.over (L.1.X q), },
end

instance (L : Cminus C) (q : ℤ) : projective (P L q) :=
begin
  dsimp [P],
  split_ifs,
  { apply projective.zero_projective, },
  { apply projective.projective_over, },
end

lemma P_eq (L : Cminus C) (q : ℤ) (hq : ¬(is_zero (L.1.X q))) :
  P L q = projective.over (L.1.X q) :=
begin
  dsimp [P],
  split_ifs,
  { exfalso, exact hq h, },
  { refl, },
end

lemma P_eq_zero (L : Cminus C) (q : ℤ) (hq : is_zero (L.1.X q)) :
  P L q = 0 :=
begin
  dsimp [P],
  split_ifs,
  { refl, },
  { exfalso, exact h hq, },
end

lemma P_is_initial (L : Cminus C) (q : ℤ) (hq : is_zero (L.1.X q)) :
  is_initial (P L q) :=
begin
  rw P_eq_zero L q hq,
  apply is_zero.is_initial,
  apply is_zero_zero,
end

def is_zero.unique_up_to_iso {X Y : C} (hX : is_zero X) (hY : is_zero Y) : X ≅ Y :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := by { rw is_zero.iff_id_eq_zero at hX, rw [hX, comp_zero], },
  inv_hom_id' := by { rw is_zero.iff_id_eq_zero at hY, rw [hY, comp_zero], }, }

def P_π (L : Cminus C) (q : ℤ) : P L q ⟶ L.1.X q :=
begin
  by_cases is_zero (L.1.X q),
  { have e : 0 ≅ L.1.X q := is_zero.unique_up_to_iso
      (is_zero_zero C) h, swap,
    exact eq_to_hom (P_eq_zero L q h) ≫ e.hom, },
  { exact eq_to_hom (P_eq L q h) ≫ projective.π (L.1.X q), },
end

lemma P_π_eq_to_hom (L : Cminus C) (q₁ q₂ : ℤ) (hq : q₁ = q₂) :
  P_π L q₁ = eq_to_hom (by rw hq) ≫ P_π L q₂ ≫ eq_to_hom (by rw hq) :=
by { subst hq, simp only [eq_to_hom_refl, comp_id, id_comp], }

@[simps]
def KP (L : Cminus C) : Cminus C := Cminus.mk
{ X := λ q, P L (q-1),
  d := λ i j, 0,
  shape' := λ i j hij, rfl,
  d_comp_d' := λ i j k hij hjk, comp_zero, }
begin
  cases L.2 with r hr,
  use r+1,
  intros i hi,
  dsimp,
  rw P_eq_zero L,
  { apply is_zero_zero, },
  { apply hr,
    linarith, },
end

instance (L : Cminus C) (q : ℤ) : epi (P_π L q) :=
by { dsimp only [P_π], split_ifs; apply epi_comp, }

def twistP (L : Cminus C) : Cminus C :=
⟨twist (cocycle.of_hom (𝟙 (KP L).1)), twist.is_bounded_above _ (KP L).2 (KP L).2⟩

def π (L : Cminus C) : twistP L ⟶ L :=
begin
  refine twist.desc (cocycle.of_hom (𝟙 (KP L).1)) (cochain.mk _) _ (neg_add_self 1) _ ,
  { exact (λ p q hpq, P_π L _ ≫ eq_to_hom (by {congr' 1, linarith})), },
  { exact
    { f := λ i, P_π L (i-1) ≫ L.1.d (i-1) i,
      comm' := λ i j hij, begin
        change i+1=j at hij,
        dsimp [KP],
        simp only [assoc, homological_complex.d_comp_d, comp_zero, zero_comp],
      end, }, },
  { ext,
    dsimp [KP],
    simp only [δ_v (-1) 0 rfl _ p p (add_zero p).symm (p-1) (p+1) rfl rfl,
      add_zero, zero_comp, cochain.mk_v, eq_to_hom_refl, comp_id,
      smul_zero, cochain.id_comp, cochain.of_hom_v], },
end

example : 2+2=4 := rfl

instance (L : Cminus C) (q : ℤ) : epi ((π L).f q) :=
begin
  haveI : epi (biprod.inl ≫ (π L).f q),
  { have eq : biprod.inl ≫ (π L).f q = eq_to_hom (by { dsimp, congr, linarith }) ≫ P_π L q,
    { dsimp [π, twist.desc_cochain, twist.fst, twist.snd, cochain.mk, cochain.v,
        cochain.of_hom, cochain.of_homs, cochain.comp],
      simp only [id_comp, assoc, add_zero, preadditive.comp_add, biprod.inl_fst_assoc, biprod.inl_snd_assoc, zero_comp,
        P_π_eq_to_hom L (q+(0 - -1)-1) q (by linarith), eq_to_hom_trans, eq_to_hom_refl,
        eq_to_hom_trans_assoc, comp_id], },
    rw eq,
    apply epi_comp, },
  exact epi_of_epi biprod.inl ((π L).f q),
end

instance : preadditive (Cminus C) := sorry
instance : has_binary_biproducts (Cminus C) := sorry

end CM5a

lemma CM5a : (arrow_classes C).CM5a := λ X Z f,
begin
  let Y := CM5a.twistP Z,
  let i : X ⟶ X ⊞ Y := biprod.inl,
  let p : X ⊞ Y ⟶ Z := biprod.desc f (CM5a.π Z),
  let j : Y ⟶ X ⊞ Y := biprod.inr,
  have hip : i ≫ p = f := biprod.inl_desc _ _,
  refine ⟨X ⊞ Y, i, _, p, _, hip⟩,
  { sorry, },
  { intro,
    dsimp,
    have hjp : j ≫ p = CM5a.π Z := biprod.inr_desc _ _,
    have hjp' : j.f n ≫ p.f n = (CM5a.π Z).f n,
    { rw [← hjp, ← homological_complex.comp_f],
      refl, },
    haveI : epi (j.f n ≫ p.f n),
    { rw hjp',
      apply_instance, },
    exact epi_of_epi (j.f n) (p.f n), },
end

def CM5 : (arrow_classes C).CM5 := ⟨CM5a, sorry⟩

variable (C)

@[simps]
def projective_structure : model_category (Cminus C) :=
{ to_category_with_fib_cof_weq := arrow_classes C,
  CM1axiom := sorry,
  CM2axiom := CM2,
  CM3axiom := CM3,
  CM4axiom := CM4,
  CM5axiom := CM5, }

instance : model_category (Cminus C) := projective_structure C

end projective_structure

end Cminus

end cochain_complex
