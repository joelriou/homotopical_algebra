/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category

open category_theory
open category_theory.category
open opposite

variables {C C' D : Type*} [category C] [category C'] [category D]

namespace quiver.hom

def is_inverted_by {X Y : C} (f : X ⟶ Y) (F : C ⥤ D) : Prop := is_iso (F.map f)

end quiver.hom

namespace hom_class

def is_inverted_by (W : hom_class C) (F : C ⥤ D) : Prop :=
∀ (X Y : C) (f : X ⟶ Y), W X Y f → f.is_inverted_by F

end hom_class

namespace category_theory

structure is_localization (F : C ⥤ C') (W : hom_class C) : Prop :=
  (inverts_W : W.is_inverted_by F)
  (universal₁ : ∀ {D : Type*} [category D] (G : C ⥤ D), W.is_inverted_by G → ∃ (G' : C' ⥤ D), G = F ⋙ G')
  (universal₂ : ∀ {D : Type*} [category D] (G' G'' : C' ⥤ D), F ⋙ G' = F ⋙ G'' → G' = G'')

def localization_wrt_isomorphisms : is_localization (𝟭 C) hom_class.isomorphisms :=
{ inverts_W := λ X Y f hf, hf,
  universal₁ := λ D hD G hG, by { use G, rw functor.id_comp, },
  universal₂ := λ D hD G' G'' h, by simpa [functor.id_comp] using h }

end category_theory
