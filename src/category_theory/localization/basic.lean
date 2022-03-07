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

universes v₁ v₂ v₃ u₁ u₂ u₃

variables {C : Type u₁} [category.{v₁} C]
variables {D D' : Type u₂} [category.{v₂} D] [category.{v₂} D']

namespace category_theory

namespace arrow

def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

end arrow

namespace arrow_class

def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : W), f.1.is_inverted_by F

end arrow_class

lemma functor.assoc {C D E F : Type*} [category C] [category D]
  [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl

structure is_localization_fixed_target (W : arrow_class C) (F : C ⥤ D)  (E : Type u₃) [category.{v₃} E] :=
  (inverts_W : W.is_inverted_by F)
  (lift : Π (G : C ⥤ E) (hG : W.is_inverted_by G), D ⥤ E)
  (fac : ∀ (G : C ⥤ E) (hG : W.is_inverted_by G), G = F ⋙ lift G hG)
  (uniq : ∀ (G₁ G₂ : D ⥤ E), F ⋙ G₁ = F ⋙ G₂ → G₁ = G₂)


/-



def localization_wrt_isomorphisms (E : Type u₃) [category.{v₃} E] :
  is_localization_fixed_target E (𝟭 C) arrow_class.isomorphisms :=
{ inverts_W := λ w, w.2,
  lift := λ G hG, G,
  fac := λ G hG, by rw functor.id_comp,
  uniq := λ G₁ G₂ h, by simpa [functor.id_comp] using h, }

def localization_is_ess_unique {W : arrow_class C} (F₁ : C ⥤ D) (F₂ : C ⥤ D')
  (L₁ : is_localization_fixed_target D' F₁ W) (L₂ : is_localization_fixed_target D F₂ W)
  (L₁' : is_localization_fixed_target D F₁ W) (L₂' : is_localization_fixed_target D' F₂ W) : D ≌ D' :=
{ functor := L₁.lift F₂ L₂.inverts_W,
  inverse := L₂.lift F₁ L₁.inverts_W,
  unit_iso := eq_to_iso begin
    apply L₁'.uniq,
    rw [← functor.assoc, ← L₁.fac F₂ L₂.inverts_W, ← L₂.fac F₁ L₁.inverts_W, functor.comp_id],
  end,
  counit_iso := eq_to_iso begin
    apply L₂'.uniq,
    rw [← functor.assoc, ← L₂.fac F₁ L₁.inverts_W, ← L₁.fac F₂ L₂.inverts_W, functor.comp_id],
  end,
  functor_unit_iso_comp' := begin
    intro X,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans, eq_to_hom_refl],
  end }-/



end category_theory
