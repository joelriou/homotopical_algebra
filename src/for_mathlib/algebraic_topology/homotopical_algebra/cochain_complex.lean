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
open algebraic_topology algebra.homology.hom_complex

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

namespace CM5a

variable [enough_projectives C]

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

def KP (L : Cminus C) : Cminus C := Cminus.mk
{ X := λ q, P L q,
  d := λ i j, 0,
  shape' := λ i j hij, rfl,
  d_comp_d' := λ i j k hij hjk, comp_zero, }
begin
  cases L.2 with r hr,
  use r,
  intros i hi,
  dsimp,
  rw P_eq_zero L i (hr i hi),
  apply is_zero_zero,
end

instance (L : Cminus C) (q : ℤ) : epi (P_π L q) :=
by { dsimp only [P_π], split_ifs; apply epi_comp, }

def KP' (L : Cminus C) : Cminus C :=
Cminus.mk (twist (cocycle.of_hom (𝟙 (KP L).1))) (twist.is_bounded_above _ (KP L).2 (KP L).2)

#exit
Cminus.mk
(twist (cochain.of_hom (𝟙 (KP L).1)))
begin
  sorry
end


def KPX (L : Cminus C) (q : ℤ) := (P L (q-1)) ⊞ (P L q)
@[simp]
def KPd₁ (L : Cminus C) (n m : ℤ) (h : n+1=m) : KPX L n ⟶ KPX L m :=
biprod.desc 0 (biprod.lift (eq_to_hom (by { congr, linarith, })) 0)

def KPX_bound (L : Cminus C) : ∃ (r : ℤ), ∀ i, r<i → nonempty (is_initial (KPX L i)) :=
begin
  cases L.2 with r hr,
  use r+1,
  intros i hi,
  exact nonempty.intro
  { desc := λ s, 0,
    fac' := λ s j, by { cases j, cases j, },
    uniq' := λ s m j, begin
      dsimp at m,
      apply is_initial.hom_ext,
      exact
      { desc := λ s, 0,
        fac' := λ s k, by { cases k, cases k, },
        uniq' := λ s m hm, begin
          ext1;
          exact is_initial.hom_ext (P_is_initial L _ (nonempty.intro (hr _ (by linarith)).some)) _ _,
        end, },
    end, },
end


#exit

@[simps]
def KP (L : Cminus C) : Cminus C :=
⟨{ X := λ q, (P L (q-1)) ⊞ (P L q),
  d := λ n m, begin
    by_cases n+1 = m,
    { exact KPd₁ L n m h, },
    { exact 0, }
  end,
  shape' := λ n m hnm, begin
    split_ifs,
    { exfalso, exact hnm h, },
    { refl, },
  end,
  d_comp_d' := λ i j k hij hjk, begin
    change i+1 = j at hij,
    change j+1 = k at hjk,
    substs hij hjk,
    simp only [eq_self_iff_true, dif_pos],
    dsimp only [KPd₁],
    ext1,
    { simp only [biprod.inl_desc_assoc, zero_comp, comp_zero], },
    { simp only [biprod.inr_desc_assoc, biprod.lift_desc, comp_zero, zero_comp, add_zero], },
  end }, KPX_bound L⟩

def KPπ (L : Cminus C) : KP L ⟶ L :=
{ f := λ q, biprod.desc (P_π L (q-1) ≫ L.1.d (q-1) q) (P_π L q),
  comm' := λ q q' hqq', begin
    change q+1=q' at hqq',
    have h : q = q'-1 := by linarith,
    subst h,
    dsimp only [KP],
    ext,
    { simp only [KPd₁, biprod.inl_desc_assoc, assoc, homological_complex.d_comp_d, comp_zero, sub_add_cancel, eq_self_iff_true,
        eq_to_hom_refl, dite_eq_ite, if_true, zero_comp], },
    { simp only [KPd₁, biprod.inr_desc_assoc, sub_add_cancel, eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true,
        biprod.lift_desc, id_comp, zero_comp, add_zero], },
  end, }

instance : preadditive (Cminus C) := sorry
instance : has_binary_biproducts (Cminus C) := sorry

end CM5a

lemma CM5a : (arrow_classes C).CM5a := λ X Y f,
begin
  sorry,
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
