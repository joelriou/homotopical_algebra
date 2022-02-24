/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.basic
import algebraic_topology.homotopical_algebra.model_category
import category_theory.quotient
import category_theory.path_category

open category_theory

namespace category_theory

universes v u

variables {C : Type u} [category.{v} C] (W : hom_class C)

include W

structure preloc := (as : C)

instance : quiver (preloc W) := { hom := λ A B,  (A.as ⟶ B.as) ⊕ (W B.as A.as : Type v) }

variable (W)

def R₁ := Σ (T : C × C × C), (T.1 ⟶ T.2.1) × (T.2.1 ⟶ T.2.2)
def R₂ := Σ (T : C × C), (W T.1 T.2 : Type v)
def R₃ := R₂ W
def ρ₁ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : R₁ W := ⟨⟨X, ⟨Y, Z⟩⟩, ⟨f, g⟩⟩
def ρ₂₃ {X Y : C} (g : X ⟶ Y) (hg : W X Y g) : R₂ W := ⟨⟨X,Y⟩, ⟨g, hg⟩⟩

def F := Σ (D : paths (preloc W) × paths (preloc W)), (D.1 ⟶ D.2) × (D.1 ⟶ D.2)

def φ (X : C) : paths (preloc W) := paths.of.obj { as := X }

def ψ₁ {X Y : C} (f : X ⟶ Y) : φ W X ⟶ φ W Y := paths.of.map (sum.inl f)
def ψ₂ {X Y : C} (g : X ⟶ Y) (hg : W X Y g): φ W Y ⟶ φ W X := paths.of.map (sum.inr ⟨g, hg⟩)

def relations₀ : C → F W := by { intro X, exact ⟨⟨⟨X⟩, ⟨X⟩⟩, ⟨ψ₁ W (𝟙 _), 𝟙 _⟩⟩, }
def relations₁ : R₁ W → F W :=
by { rintro ⟨⟨X,⟨Y,Z⟩⟩, ⟨f,g⟩⟩, exact ⟨⟨⟨X⟩, ⟨Z⟩⟩, ⟨ψ₁ W (f ≫ g), ψ₁ W f ≫ ψ₁ W g⟩⟩, }
def relations₂ : R₂ W → F W :=
by { rintro ⟨⟨X, Y⟩, ⟨w, hw⟩⟩, exact ⟨⟨⟨X⟩, ⟨X⟩⟩, ⟨ψ₁ W w ≫ ψ₂ W w hw, 𝟙 _⟩⟩, }
def relations₃ : R₃ W → F W :=
by { rintro ⟨⟨X, Y⟩, ⟨w, hw⟩⟩, exact ⟨⟨⟨Y⟩, ⟨Y⟩⟩, ⟨ψ₂ W w hw ≫ ψ₁ W w, 𝟙 _⟩⟩, }

variable {W}
def belongs_to {A B : paths (preloc W)} (f g : A ⟶ B) {D : Type*} (relations : D → F W) : Prop :=
∃ (r : D), relations r = ⟨⟨A, B⟩, ⟨f, g⟩⟩

variable (W)
def relations : hom_rel (paths (preloc W)) :=
λ X Y f g, belongs_to f g (relations₀ W) ∨ belongs_to f g (relations₁ W) ∨
  belongs_to f g (relations₂ W) ∨ belongs_to f g (relations₃ W)

def localization := category_theory.quotient (relations W)

instance : category (localization W) := (infer_instance : category (category_theory.quotient (relations W)))

def Q : C ⥤ localization W :=
{ obj := λ X, (quotient.functor (relations W)).obj (φ W X),
  map := λ X Y f, (quotient.functor (relations W)).map (ψ₁ W f),
  map_id' := λ X, begin
    apply quotient.sound (relations W),
    exact or.inl ⟨X, rfl⟩,
  end,
  map_comp' := λ X Y Z f g, begin
    apply quotient.sound (relations W),
    exact or.inr (or.inl (⟨ρ₁ W f g, rfl⟩)),
  end }

variable {W}

def Winv {X Y : C} (g : X ⟶ Y) (hg : W X Y g) : (Q W).obj Y ⟶ (Q W).obj X :=
(quotient.functor (relations W)).map (ψ₂ W g hg)

omit W

lemma congr_obj {D₁ D₂ : Type*} [category D₁] [category D₂] {F G : D₁ ⥤ D₂}
(h : F = G) : ∀ X : D₁, F.obj X = G.obj X :=
by { intro X, rw h, }

theorem localisation_is_localisation : is_localization (Q W) W :=
{ inverts_W := begin
    intros X Y g hg,
    refine ⟨_⟩,
    use Winv g hg,
    dsimp only [Winv],
    split,
    { erw ← (quotient.functor (relations W)).map_comp (ψ₁ W g) (ψ₂ W g hg),
      apply quotient.sound (relations W),
      exact or.inr (or.inr (or.inl ⟨ρ₂₃ W g hg, rfl⟩)), },
    { erw ← (quotient.functor (relations W)).map_comp (ψ₂ W g hg) (ψ₁ W g),
      apply quotient.sound (relations W),
      exact or.inr (or.inr (or.inr ⟨ρ₂₃ W g hg, rfl⟩)), },
  end,
  universal₁ := sorry,
  universal₂ := λ D, begin
    introI,
    intros G' G'' h,
    apply functor.ext,
    { rintros ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ f,
      sorry, },
    { rintro ⟨⟨X⟩⟩,
      convert congr_obj h X, },
  end }

end category_theory
