/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.additive
import category_theory.limits.shapes.biproducts

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {ι : Type*} {V : Type*} [category V] [preadditive V]
variable {c : complex_shape ι}

namespace homological_complex

variables (X Y : homological_complex V c) [∀ i, has_binary_biproduct (X.X i) (Y.X i)]
variables {Z Z': homological_complex V c} (f₁ : X ⟶ Z) (f₂ : Y ⟶ Z) (g₁ : Z' ⟶ X) (g₂ : Z' ⟶ Y)

@[simps]
def biprod : homological_complex V c :=
{ X := λ i, X.X i ⊞ Y.X i,
  d := λ i j, biprod.desc (biprod.lift (X.d i j) 0) (biprod.lift 0 (Y.d i j)),
  shape' := λ i j hij, begin
    ext,
    { simp only [biprod.inl_desc, biprod.lift_fst, comp_zero, zero_comp, X.shape i j hij], },
    { simp only [biprod.inl_desc, biprod.lift_snd, comp_zero, zero_comp], },
    { simp only [biprod.inr_desc, biprod.lift_fst, comp_zero, zero_comp], },
    { simp only [Y.shape i j hij, biprod.inr_desc, biprod.lift_snd, comp_zero, zero_comp], },
  end, }

namespace biprod

variables {X Y}

@[simps] def inl : X ⟶ biprod X Y := { f := λ i, biprod.inl, }
@[simps] def inr : Y ⟶ biprod X Y := { f := λ i, biprod.inr, }
@[simps] def fst : biprod X Y ⟶ X := { f := λ i, biprod.fst, }
@[simps] def snd : biprod X Y ⟶ Y := { f := λ i, biprod.snd, }

@[simp, reassoc] def inl_fst : (inl : X ⟶ biprod X Y) ≫ fst = 𝟙 _ := by tidy
@[simp, reassoc] def inl_snd : (inl : X ⟶ biprod X Y) ≫ snd = 0   := by tidy
@[simp, reassoc] def inr_fst : (inr : Y ⟶ biprod X Y) ≫ fst = 0   := by tidy
@[simp, reassoc] def inr_snd : (inr : Y ⟶ biprod X Y) ≫ snd = 𝟙 _ := by tidy

@[simps] def desc : biprod X Y ⟶ Z := { f := λ i, biprod.desc (f₁.f i) (f₂.f i), }
@[simp, reassoc] lemma inl_desc : inl ≫ desc f₁ f₂ = f₁ := by tidy
@[simp, reassoc] lemma inr_desc : inr ≫ desc f₁ f₂ = f₂ := by tidy

@[simps] def lift : Z' ⟶ biprod X Y := { f := λ i, biprod.lift (g₁.f i) (g₂.f i), }
@[simp, reassoc] lemma lift_fst : lift g₁ g₂ ≫ fst = g₁ := by tidy
@[simp, reassoc] lemma lift_snd : lift g₁ g₂ ≫ snd = g₂ := by tidy

@[ext]
lemma hom_ext (f₁ f₂ : Z' ⟶ biprod X Y) (h₁ : f₁ ≫ biprod.fst = f₂ ≫ biprod.fst)
  (h₂ : f₁ ≫ biprod.snd = f₂ ≫ biprod.snd ) : f₁ = f₂ :=
by { ext i, exacts [congr_hom h₁ i, congr_hom h₂ i], }

@[ext]
lemma hom_ext' (f₁ f₂ : biprod X Y ⟶ Z) (h₁ : biprod.inl ≫ f₁= biprod.inl ≫ f₂)
  (h₂ : biprod.inr ≫ f₁ = biprod.inr ≫ f₂) : f₁ = f₂ :=
by { ext i, exacts [congr_hom h₁ i, congr_hom h₂ i], }

@[simp, reassoc]
lemma lift_desc : lift g₁ g₂ ≫ desc f₁ f₂ = g₁ ≫ f₁ + g₂ ≫ f₂ := by tidy

end biprod

end homological_complex
