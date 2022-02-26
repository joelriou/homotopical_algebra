/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow_class
import category_theory.equivalence
import category_theory.eq_to_hom

open category_theory
open category_theory.category
open opposite

universes v' u'
variables {C C'' D : Type*} [category C] [category C''] [category D]
variables {C' : Type u'} [category.{v'} C']

namespace category_theory
namespace arrow

def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

end arrow

namespace arrow_class

def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : arrow C), f ∈ W → f.is_inverted_by F

end arrow_class

lemma functor.assoc {C D E F : Type*} [category C] [category D]
  [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl

structure is_localization (F : C ⥤ C') (W : arrow_class C) :=
  (inverts_W : W.is_inverted_by F)
  (lift : Π {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G), C' ⥤ D)
  (fac : ∀ {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G), G = F ⋙ lift G hG)
  (uniq : ∀ {D : Type*} [category D] (G' G'' : C' ⥤ D), F ⋙ G' = F ⋙ G'' → G' = G'')

def localization_wrt_isomorphisms : is_localization (𝟭 C) arrow_class.isomorphisms :=
{ inverts_W := λ f hf, hf,
  lift := λ D hD G hG, G,
  fac := λ D hD H hG, by rw functor.id_comp,
  uniq := λ D hD G' G'' h, by simpa [functor.id_comp] using h, }

def localization_is_ess_unique {W : arrow_class C} {F₁ : C ⥤ C'} {F₂ : C ⥤ C''}
  (L₁ : is_localization F₁ W) (L₂ : is_localization F₂ W) : C' ≌ C'' :=
{ functor := L₁.lift F₂ L₂.inverts_W,
  inverse := L₂.lift F₁ L₁.inverts_W,
  unit_iso := eq_to_iso begin
    apply L₁.uniq,
    rw [← functor.assoc, ← L₁.fac F₂ L₂.inverts_W, ← L₂.fac F₁ L₁.inverts_W, functor.comp_id],
  end,
  counit_iso := eq_to_iso begin
    apply L₂.uniq,
    rw [← functor.assoc, ← L₂.fac F₁ L₁.inverts_W, ← L₁.fac F₂ L₂.inverts_W, functor.comp_id],
  end,
  functor_unit_iso_comp' := begin
    intro X,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans, eq_to_hom_refl],
  end }

namespace is_localization

end is_localization

end category_theory
