/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.localization.predicate

noncomputable theory

open category_theory.category

namespace category_theory

class Comm_sq {C₁ C₂ D₁ D₂ : Type*} [category C₁]  [category C₂]  [category D₁]  [category D₂]
  (F : C₁ ⥤ C₂) (G₁ : C₁ ⥤ D₁) (G₂ : C₂ ⥤ D₂) (F' : D₁ ⥤ D₂) :=
(iso : G₁ ⋙ F' ≅ F ⋙ G₂)

namespace localization

section

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁]  [category C₂]  [category D₁]  [category D₂]
  {I : C₁ ⥤ C₂} {I' : D₁ ⥤ D₂} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  (h : Comm_sq I L₁ L₂ I')
  (W₁ : morphism_property C₁) (W₂ : morphism_property C₂)
  [L₁.is_localization W₁] [L₂.is_localization W₂]
  (R : C₂ ⥤ D₁) (R' : D₂ ⥤ D₁) [hR : lifting L₂ W₂ R R']
  (η : R ⋙ I' ≅ L₂)
  (ε : I ⋙ R ≅ L₁)

include h W₁ hR ε η

def lifting_equivalence : D₁ ≌ D₂ :=
begin
  refine (equivalence.mk I' R' _ _),
  { haveI : lifting L₁ W₁ (I ⋙ L₂) I' := ⟨h.iso⟩,
    let e : (I ⋙ L₂) ⋙ R' ≅ L₁,
    { calc (I ⋙ L₂) ⋙ R' ≅ I ⋙ L₂ ⋙ R' : functor.associator _ _ _
      ... ≅ I ⋙ R : iso_whisker_left _ (lifting.iso _ W₂ _ _)
      ... ≅ L₁ : ε, },
    haveI : lifting L₁ W₁ L₁ (I' ⋙ R') := lifting.of_isos _ _ e (iso.refl _),
    exact lifting.uniq L₁ W₁ L₁ _ _, },
  { haveI : lifting L₂ W₂ L₂ (R' ⋙ I') := lifting.of_isos _ _ η (iso.refl _),
    exact lifting.uniq L₂ W₂ L₂ _ _, },
end

lemma lifting_equivalence_counit_iso_app (X : C₂) :
  (lifting_equivalence h W₁ W₂ R R' η ε).counit_iso.app (L₂.obj X) =
  I'.map_iso ((lifting.iso L₂ W₂ R R').app X) ≪≫ η.app X :=
begin
  ext,
  dsimp [lifting_equivalence, equivalence.mk],
  simp only [lifting.uniq_hom_app, lifting.of_isos_iso, iso.refl_symm,
    lifting.comp_right_iso, iso.trans_hom, iso_whisker_left_hom,
    iso.refl_hom, whisker_left_id', iso_whisker_right_hom, id_comp,
    nat_trans.comp_app, whisker_right_app, lifting.id_iso,
    functor.right_unitor_inv_app, comp_id],
end

def lifting_is_equivalence : is_equivalence I' :=
is_equivalence.of_equivalence (lifting_equivalence h W₁ W₂ R R' η ε)

end

end localization

end category_theory
