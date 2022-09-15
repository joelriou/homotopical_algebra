/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.localization.construction2

noncomputable theory

open category_theory.category

namespace category_theory


namespace functor

section

variables {C D : Type*} [category C] [category D] (F : C ⥤ D) [full F] [faithful F]

@[simp]
lemma preimage_iso_refl (X : C) : F.preimage_iso (iso.refl (F.obj X)) = iso.refl X :=
begin
  ext,
  apply F.map_injective,
  simp only [preimage_iso_hom, iso.refl_hom, preimage_id],
end

@[simp]
lemma preimage_iso_symm {X Y : C} (e : F.obj X ≅ F.obj Y) :
  F.preimage_iso e.symm = (F.preimage_iso e).symm :=
begin
  ext,
  apply F.map_injective,
  simp only [preimage_iso_hom, iso.symm_hom, map_comp, image_preimage, iso.hom_inv_id, map_id],
end

@[simp]
lemma preimage_iso_trans {X Y Z : C} (e : F.obj X ≅ F.obj Y) (f : F.obj Y ≅ F.obj Z) :
  F.preimage_iso (e.trans f) = (F.preimage_iso e).trans (F.preimage_iso f) :=
begin
  ext,
  apply F.map_injective,
  simp only [preimage_iso_hom, iso.trans_hom, map_comp, image_preimage],
end

end

end functor


variables {C D : Type*} [category C] [category D]
variables (L : C ⥤ D) (W : morphism_property C)
variables (E : Type*) [category E]

namespace functor

class is_localization :=
(inverts_W : W.is_inverted_by L)
(is_equivalence : is_equivalence (localization.construction.lift L inverts_W))

instance Q_is_localization : W.Q.is_localization W :=
{ inverts_W := W.Q_inverts,
  is_equivalence := begin
    suffices : localization.construction.lift W.Q W.Q_inverts = 𝟭 _,
    { rw this, apply_instance, },
    apply localization.construction.uniq,
    simpa only [localization.construction.fac],
  end, }

end functor

namespace localization

variable [L.is_localization W]
include L W

def as_localization : L.is_localization W := infer_instance

lemma inverts_W : W.is_inverted_by L := (as_localization _ _).inverts_W

instance is_equivalence_from_model := (as_localization L W).is_equivalence

def equivalence_from_model : W.localization ≌ D :=
(localization.construction.lift L (inverts_W L W)).as_equivalence

def whiskering_left_functor : (D ⥤ E) ⥤ W.functors_inverting E :=
full_subcategory.lift _ ((whiskering_left _ _ E).obj L)
  (morphism_property.is_inverted_by.of_comp W L (as_localization L W).inverts_W)

@[simps]
def functor_equivalence₀ : (D ⥤ E) ≌ (W.functors_inverting E) :=
(equivalence.congr_left (equivalence_from_model L W).symm).trans
  (construction.whiskering_left_equivalence W E)

lemma functor_equivalence₀_functor_iso :
  (functor_equivalence₀ L W E).functor ≅ whiskering_left_functor L W E :=
nat_iso.of_components (λ F, eq_to_iso begin
  ext,
  change (W.Q ⋙ (localization.construction.lift L (inverts_W L W))) ⋙ F = L ⋙ F,
  rw construction.fac,
end)
begin
  intros F₁ F₂ τ,
  ext X,
  dsimp [whiskering_left_functor, whisker_left],
  erw [nat_trans.comp_app, nat_trans.comp_app],
  simp only [functor_equivalence₀_functor_map_app],
  dsimp [equivalence_from_model, morphism_property.Q],
  erw [eq_to_hom_app, eq_to_hom_app, eq_to_hom_refl, eq_to_hom_refl, comp_id, id_comp],
  all_goals
  { change (W.Q ⋙ (localization.construction.lift L (inverts_W L W))) ⋙ _ = L ⋙ _,
    rw construction.fac, },
end

instance : is_equivalence (whiskering_left_functor L W E) :=
is_equivalence.of_iso (functor_equivalence₀_functor_iso L W E) (is_equivalence.of_equivalence _)

def functor_equivalence : (D ⥤ E) ≌ (W.functors_inverting E) :=
(whiskering_left_functor L W E).as_equivalence

end localization

namespace functor

namespace is_localization

variables {L W}

def whiskering_left_functor' (h : L.is_localization W) (E : Type*) [category E] :
  (D ⥤ E) ⥤ (C ⥤ E) := (whiskering_left C D E).obj L

@[simp]
def whiskering_left_functor'_obj (h : L.is_localization W) {E : Type*} [category E]
  (F : D ⥤ E) : (h.whiskering_left_functor' E).obj F = L ⋙ F := rfl

lemma whiskering_left_functor'_eq (h : L.is_localization W) (E : Type*) [category E] :
  h.whiskering_left_functor' E =
    localization.whiskering_left_functor L W E ⋙ induced_functor _ := rfl

instance (h : L.is_localization W) (E : Type*) [category E] :
  full (h.whiskering_left_functor' E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

instance (h : L.is_localization W) (E : Type*) [category E] :
  faithful (h.whiskering_left_functor' E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

end is_localization

end functor

namespace localization

variables [L.is_localization W] {E}
include L W

/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class lifting (F : C ⥤ E) (F' : D ⥤ E) := (iso : L ⋙ F' ≅ F)

namespace lifting

variables {L W}

def F {F : C ⥤ E} {F' : D ⥤ E} (h : lifting L W F F') : W.functors_inverting E :=
⟨F, begin
  rw ← morphism_property.is_inverted_by.iff_of_iso W h.iso,
  exact morphism_property.is_inverted_by.of_comp W L (as_localization L W).inverts_W F',
end⟩

variables (L W)

def fac (F : C ⥤ E) (F' : D ⥤ E) [h : lifting L W F F'] : L ⋙ F' ≅ F := h.iso

def uniq (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [h₁ : lifting L W F F'₁] [h₂ : lifting L W F F'₂] :
  F'₁ ≅ F'₂ :=
((as_localization L W).whiskering_left_functor' E).preimage_iso (h₁.iso.trans h₂.iso.symm)

lemma uniq_refl (F : C ⥤ E) (F' : D ⥤ E) [h : lifting L W F F'] :
  uniq L W F F' F' = iso.refl F' :=
begin
  dsimp only [uniq],
  simpa only [iso.self_symm_id] using functor.preimage_iso_refl _ _,
end

lemma uniq_symm (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [h₁ : lifting L W F F'₁] [h₂ : lifting L W F F'₂] :
  (uniq L W F F'₁ F'₂).symm = uniq L W F F'₂ F'₁ :=
by { erw ← functor.preimage_iso_symm, congr' 1, }

lemma uniq_trans (F : C ⥤ E) (F'₁ F'₂ F'₃ : D ⥤ E)
  [h₁ : lifting L W F F'₁] [h₂ : lifting L W F F'₂] [h₃ : lifting L W F F'₃] :
  uniq L W F F'₁ F'₂ ≪≫ uniq L W F F'₂ F'₃ = uniq L W F F'₁ F'₃ :=
begin
  erw ← functor.preimage_iso_trans,
  congr' 1,
  simp only [iso.trans_assoc, iso.symm_self_id_assoc],
end

end lifting

variables {W E}

def lift (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  D ⥤ E :=
(functor_equivalence L W E).inverse.obj ⟨F, hF⟩

instance lift_is_lifting (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D)
  [hL : L.is_localization W] : lifting L W F (lift F hF L) :=
⟨(induced_functor _).map_iso ((functor_equivalence L W E).counit_iso.app ⟨F, hF⟩)⟩

@[simps]
def fac (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  L ⋙ lift F hF L ≅ F :=
lifting.fac _ W _ _

end localization

end category_theory
