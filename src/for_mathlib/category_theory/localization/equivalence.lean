/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.localization.predicate

noncomputable theory

open category_theory.category

namespace category_theory

namespace morphism_property

variables {C : Type*} [category C]

def iso_closure (P : morphism_property C) : morphism_property C :=
λ X₁ X₂ f, ∃ (Y₁ Y₂ : C) (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (f' : Y₁ ⟶ Y₂) (hf' : P f'),
  comm_sq f e₁.hom e₂.hom f'

lemma subset_iso_closure (P : morphism_property C) : P ⊆ P.iso_closure :=
λ X Y f hf, ⟨X, Y, iso.refl X, iso.refl Y, f, hf, comm_sq.mk (by simp)⟩

lemma iso_closure_respects_iso (P : morphism_property C) : P.iso_closure.respects_iso :=
begin
  split,
  { intros A X₁ X₂ e f hf,
    rcases hf with ⟨Y₁, Y₂, e₁, e₂, f', hf', sq⟩,
    exact ⟨Y₁, Y₂, e ≪≫ e₁, e₂, f', hf', comm_sq.mk (by simp [sq.w])⟩, },
  { intros X₁ X₂ Z e f hf,
    rcases hf with ⟨Y₁, Y₂, e₁, e₂, f', hf', sq⟩,
    exact ⟨Y₁, Y₂, e₁, e.symm ≪≫ e₂, f', hf', comm_sq.mk (by simp [sq.w])⟩, },
end

def inverse_image' {D : Type*} [category D] (P : morphism_property D) (F : C ⥤ D) :
  morphism_property C := (P.inverse_image F).iso_closure

end morphism_property

class Comm_sq {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  (F : C₁ ⥤ C₂) (G₁ : C₁ ⥤ D₁) (G₂ : C₂ ⥤ D₂) (F' : D₁ ⥤ D₂) :=
(iso : G₁ ⋙ F' ≅ F ⋙ G₂)

namespace localization

section

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
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

section

variables {C₁ C₂ D : Type*} [category C₁] [category C₂] [category D]
  (L₁ : C₁ ⥤ D) (W₁ : morphism_property C₁) (L₂ : C₂ ⥤ D) (W₂ : morphism_property C₂)
  (E : C₂ ≌ C₁) (hW₁ : W₁ ⊆ W₂.inverse_image' E.inverse) (hW₂ : W₂.is_inverted_by L₂)
  [L₁.is_localization W₁] (iso : E.functor ⋙ L₁ ≅ L₂)

include iso hW₁ hW₂

def functor.is_localization.of_equivalence' :
  L₂.is_localization W₂ :=
begin
  have h₁ : W₂.is_inverted_by L₂ := hW₂,
  have h₂ : W₁.is_inverted_by (E.inverse ⋙ W₂.Q) := λ X₁ X₂ f hf, begin
    rcases hW₁ f hf with ⟨Y₁, Y₂, e₁, e₂, f', hf', sq⟩,
    dsimp,
    have eq := sq.w,
    rw [← cancel_mono (e₂.inv), assoc, e₂.hom_inv_id, comp_id, assoc] at eq,
    rw eq,
    simp only [functor.map_comp],
    haveI := localization.inverts_W W₂.Q W₂ _ hf',
    apply_instance,
  end,
  let I' := localization.construction.lift L₂ h₁,
  let C : Comm_sq E.functor W₂.Q L₁ I' := ⟨localization.lifting.iso W₂.Q W₂ L₂ I' ≪≫ iso.symm⟩,
  let iso₁ : (E.inverse ⋙ W₂.Q) ⋙ I' ≅ L₁,
  { calc (E.inverse ⋙ W₂.Q) ⋙ I' ≅ E.inverse ⋙ (W₂.Q ⋙ I') : functor.associator _ _ _
    ... ≅ E.inverse ⋙ (E.functor ⋙ L₁) : iso_whisker_left _ C.iso
    ... ≅ (E.inverse ⋙ E.functor) ⋙ L₁ : (functor.associator _ _ _).symm
    ... ≅ 𝟭 _ ⋙ L₁ : iso_whisker_right E.counit_iso _
    ... ≅ L₁ : functor.left_unitor _, },
  let iso₂ : E.functor ⋙ E.inverse ⋙ W₂.Q ≅ W₂.Q,
  { calc E.functor ⋙ E.inverse ⋙ W₂.Q ≅ (E.functor ⋙ E.inverse) ⋙ W₂.Q :
      (functor.associator _ _ _).symm
    ... ≅ 𝟭 _ ⋙ W₂.Q : iso_whisker_right E.unit_iso.symm _
    ... ≅ W₂.Q : functor.left_unitor _, },
  exact
  { inverts_W := h₁,
    is_equivalence := localization.lifting_is_equivalence C W₂ W₁ (E.inverse ⋙ W₂.Q)
      (localization.lift (E.inverse ⋙ W₂.Q) h₂ L₁) iso₁ iso₂, }
end

end

section

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  (E : C₁ ≌ C₂) (E' : D₁ ≌ D₂) {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  (H : Comm_sq E.functor L₁ L₂ E'.functor)
  (W₁ : morphism_property C₁) (W₂ : morphism_property C₂)
  (hW₁ : W₁.is_inverted_by L₁)
  (hW₂ : W₂ ⊆ W₁.inverse_image' E.inverse)
  [L₂.is_localization W₂]

include H hW₁ hW₂

def functor.is_localization.of_equivalence'' : L₁.is_localization W₁ :=
begin
  haveI : (E.functor ⋙ L₂).is_localization W₁,
  { refine functor.is_localization.of_equivalence' L₂ W₂ (E.functor ⋙ L₂)
      W₁ E hW₂ _ (iso.refl _),
    rw ← morphism_property.is_inverted_by.iff_of_iso W₁ H.iso,
    exact morphism_property.is_inverted_by.of_comp _ _ hW₁ _, },
  haveI := functor.is_localization.of_iso W₁ H.iso.symm,
  refine functor.is_localization.of_equivalence (L₁ ⋙ E'.functor) W₁ L₁ E'.symm _,
  calc (L₁ ⋙ E'.functor) ⋙ E'.symm.functor ≅ L₁ ⋙ E'.functor ⋙ E'.symm.functor :
    functor.associator _ _ _
  ... ≅ L₁ ⋙ 𝟭 D₁ : iso_whisker_left _ E'.unit_iso.symm
  ... ≅ L₁ : functor.right_unitor _,
end

end

end category_theory
