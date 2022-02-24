/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

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

def R₁ := Σ (T : C × C), (W T.1 T.2 : Type v)
def R₂ := R₁ W
def R₃ := Σ (T : C × C × C), (T.1 ⟶ T.2.1) × (T.2.1 ⟶ T.2.2)

def F := Σ (D : paths (preloc W) × paths (preloc W)), (D.1 ⟶ D.2) × (D.1 ⟶ D.2)

def φ (X : C) : paths (preloc W) := paths.of.obj { as := X }

def ψ₁ {X Y : C} (f : X ⟶ Y) : φ W X ⟶ φ W Y := paths.of.map (sum.inl f)
def ψ₂ {X Y : C} (g : X ⟶ Y) (hg : W X Y g): φ W Y ⟶ φ W X := paths.of.map (sum.inr ⟨g, hg⟩)

def relations₁ : R₁ W → F W :=
by { rintro ⟨⟨X, Y⟩, ⟨w, hw⟩⟩, exact ⟨⟨⟨X⟩, ⟨X⟩⟩, ⟨ψ₁ W w ≫ ψ₂ W w hw, 𝟙 _⟩⟩, }
def relations₂ : R₂ W → F W :=
by { rintro ⟨⟨X, Y⟩, ⟨w, hw⟩⟩, exact ⟨⟨⟨Y⟩, ⟨Y⟩⟩, ⟨ψ₂ W w hw ≫ ψ₁ W w, 𝟙 _⟩⟩, }
def relations₃ : R₃ W → F W :=
by { rintro ⟨⟨X,⟨Y,Z⟩⟩, ⟨f,g⟩⟩, exact ⟨⟨⟨X⟩, ⟨Z⟩⟩, ⟨ψ₁ W f ≫ ψ₁ W g, ψ₁ W (f ≫ g)⟩⟩, }


end category_theory
