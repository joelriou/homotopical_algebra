/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.functor_misc
import category_theory.localization.predicate
import for_mathlib.category_theory.morphism_property_misc

noncomputable theory

open category_theory.category category_theory

namespace category_theory

structure Comm_sq {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  (F : C₁ ⥤ C₂) (G₁ : C₁ ⥤ D₁) (G₂ : C₂ ⥤ D₂) (F' : D₁ ⥤ D₂) :=
(iso [] : G₁ ⋙ F' ≅ F ⋙ G₂)

namespace Comm_sq

variables {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
  [category C₁] [category C₂] [category C₃] [category C₄]
  [category D₁] [category D₂] [category D₃] [category D₄]

@[simps]
def horiz_refl {C D : Type*} [category C] [category D]
  (F : C ⥤ D) : Comm_sq (𝟭 C) F F (𝟭 D) := ⟨iso.refl _⟩

def horiz_comp
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} {G : C₂ ⥤ C₃} {G' : D₂ ⥤ D₃}
  (H₁₂ : Comm_sq F L₁ L₂ F') (H₂₃ : Comm_sq G L₂ L₃ G') :
  Comm_sq (F ⋙ G) L₁ L₃ (F' ⋙ G') :=
⟨calc L₁ ⋙ F' ⋙ G' ≅ (L₁ ⋙ F') ⋙ G' : (functor.associator _ _ _).symm
  ... ≅ (F ⋙ L₂) ⋙ G' : iso_whisker_right H₁₂.iso _
  ... ≅ F ⋙ (L₂ ⋙ G') : functor.associator _ _ _
  ... ≅ F ⋙ (G ⋙ L₃) : iso_whisker_left _ H₂₃.iso
  ... ≅ (F ⋙ G) ⋙ L₃ : (functor.associator _ _ _).symm⟩

@[simp]
lemma horiz_comp_iso_hom_app
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} {G : C₂ ⥤ C₃} {G' : D₂ ⥤ D₃}
  (H₁₂ : Comm_sq F L₁ L₂ F') (H₂₃ : Comm_sq G L₂ L₃ G') (X₁ : C₁):
  (H₁₂.horiz_comp H₂₃).iso.hom.app X₁ =
    G'.map (H₁₂.iso.hom.app X₁) ≫ H₂₃.iso.hom.app (F.obj X₁) :=
by { dsimp [horiz_comp], simp only [id_comp, comp_id], }

@[simp]
lemma horiz_comp_iso_inv_app
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} {G : C₂ ⥤ C₃} {G' : D₂ ⥤ D₃}
  (H₁₂ : Comm_sq F L₁ L₂ F') (H₂₃ : Comm_sq G L₂ L₃ G') (X₁ : C₁):
  (H₁₂.horiz_comp H₂₃).iso.inv.app X₁ =
    H₂₃.iso.inv.app (F.obj X₁) ≫ G'.map (H₁₂.iso.inv.app X₁) :=
by { dsimp [horiz_comp], simp only [comp_id, id_comp], }

@[simp]
lemma horiz_comp_refl_iso {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂}
  (H : Comm_sq F L₁ L₂ F') : (H.horiz_comp (horiz_refl L₂)).iso = H.iso :=
by { ext X, rw horiz_comp_iso_hom_app, apply comp_id, }

@[simp]
lemma refl_horiz_comp_iso {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂}
  (H : Comm_sq F L₁ L₂ F') : ((horiz_refl L₁).horiz_comp H).iso = H.iso :=
by { ext X, rw horiz_comp_iso_hom_app, dsimp, rw [F'.map_id, id_comp], }

lemma horiz_comp_assoc_iso
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄}
  {F : C₁ ⥤ C₂} {F' : D₁ ⥤ D₂} {G : C₂ ⥤ C₃} {G' : D₂ ⥤ D₃} {K : C₃ ⥤ C₄} {K' : D₃ ⥤ D₄}
  (H₁₂ : Comm_sq F L₁ L₂ F') (H₂₃ : Comm_sq G L₂ L₃ G') (H₃₄ : Comm_sq K L₃ L₄ K') :
  ((H₁₂.horiz_comp H₂₃).horiz_comp H₃₄).iso = (H₁₂.horiz_comp (H₂₃.horiz_comp H₃₄)).iso :=
by { ext X, simpa only [horiz_comp_iso_hom_app, functor.map_comp, assoc, functor.comp_map], }

end Comm_sq

variables {C D : Type*} [category C] [category D]
variables (L : C ⥤ D) (W : morphism_property C)
variables (E : Type*) [category E]

namespace functor

/-class is_localization : Prop :=
(inverts : W.is_inverted_by L)
(nonempty_is_equivalence : nonempty (is_equivalence (localization.construction.lift L inverts)))

instance Q_is_localization : W.Q.is_localization W :=
{ inverts := W.Q_inverts,
  nonempty_is_equivalence := begin
    suffices : localization.construction.lift W.Q W.Q_inverts = 𝟭 _,
    { apply nonempty.intro, rw this, apply_instance, },
    apply localization.construction.uniq,
    simpa only [localization.construction.fac],
  end, }-/

end functor

namespace localization

/-structure strict_universal_property_fixed_target :=
(inverts : W.is_inverted_by L)
(lift : Π (F : C ⥤ E) (hF : W.is_inverted_by F), D ⥤ E)
(fac : Π (F : C ⥤ E) (hF : W.is_inverted_by F), L ⋙ lift F hF = F)
(uniq : Π (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂)

def strict_universal_property_fixed_target.for_Q : strict_universal_property_fixed_target W.Q W E :=
{ inverts := W.Q_inverts,
  lift := construction.lift,
  fac := construction.fac,
  uniq := construction.uniq, }

def strict_universal_property_fixed_target.for_id (hW : W ⊆ morphism_property.isomorphisms C):
  strict_universal_property_fixed_target (𝟭 C) W E :=
{ inverts := λ X Y f hf, hW f hf,
  lift := λ F hF, F,
  fac := λ F hF, by { cases F, refl, },
  uniq := λ F₁ F₂ eq, by { cases F₁, cases F₂, exact eq, }, }-/

end localization

namespace functor
/-
variables (h₁ : localization.strict_universal_property_fixed_target L W D)
  (h₂ : localization.strict_universal_property_fixed_target L W W.localization)

namespace is_localization.mk'

lemma unit_eq :
  𝟭 W.localization = localization.construction.lift L h₁.inverts ⋙ h₂.lift W.Q W.Q_inverts :=
begin
  apply localization.construction.uniq,
  rw [← functor.assoc, localization.construction.fac, h₂.fac, functor.comp_id],
end

lemma counit_eq :
  h₂.lift W.Q W.Q_inverts ⋙ localization.construction.lift L h₁.inverts = 𝟭 D :=
begin
  apply h₁.uniq,
  rw [← functor.assoc, h₂.fac, localization.construction.fac, functor.comp_id],
end

def equivalence : W.localization ≌ D :=
{ functor := localization.construction.lift L h₁.inverts,
  inverse := h₂.lift W.Q W.Q_inverts,
  unit_iso := eq_to_iso (unit_eq L W h₁ h₂),
  counit_iso := eq_to_iso (counit_eq L W h₁ h₂),
  functor_unit_iso_comp' := λ X, by simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map,
    eq_to_hom_trans, eq_to_hom_refl], }

def equivalence_obj_equiv' : W.localization ≃ D :=
{ to_fun := (is_localization.mk'.equivalence L W h₁ h₂).functor.obj,
  inv_fun := (is_localization.mk'.equivalence L W h₁ h₂).inverse.obj,
  left_inv := congr_obj (unit_eq L W h₁ h₂).symm,
  right_inv := congr_obj (counit_eq L W h₁ h₂), }

lemma obj_bijective : function.bijective L.obj :=
((localization.construction.obj_equiv W).trans (equivalence_obj_equiv' L W h₁ h₂)).bijective

end is_localization.mk'

lemma is_localization.mk' :
  is_localization L W :=
{ inverts := h₁.inverts,
  nonempty_is_equivalence :=
    nonempty.intro (is_equivalence.of_equivalence (is_localization.mk'.equivalence L W h₁ h₂)), }
-/
end functor

namespace localization

variable [L.is_localization W]
include L W

/-lemma inverts : W.is_inverted_by L := (as_localization _ _).inverts-/

@[simps]
def iso_of_hom' {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
begin
  haveI : is_iso (L.map f) := inverts L W f hf,
  exact as_iso (L.map f),
end

/-instance : is_equivalence (localization.construction.lift L (inverts L W)) :=
(as_localization L W).nonempty_is_equivalence.some

def equivalence_from_model : W.localization ≌ D :=
(localization.construction.lift L (inverts L W)).as_equivalence

def Q_comp_equivalence_from_model_functor_iso :
  W.Q ⋙ (equivalence_from_model L W).functor ≅ L := eq_to_iso (construction.fac _ _)

def comp_equivalence_from_model_inverse_iso :
  L ⋙ (equivalence_from_model L W).inverse ≅ W.Q :=
begin
  let α := Q_comp_equivalence_from_model_functor_iso L W,
  calc L ⋙ (equivalence_from_model L W).inverse ≅ _ : iso_whisker_right α.symm _
  ... ≅ W.Q ⋙ ((equivalence_from_model L W).functor ⋙ (equivalence_from_model L W).inverse) :
    functor.associator _ _ _
  ... ≅ W.Q ⋙ 𝟭 _ : iso_whisker_left _ ((equivalence_from_model L W).unit_iso.symm)
  ... ≅ W.Q : functor.right_unitor _,
end

lemma ess_surj : ess_surj L :=
⟨λ X, ⟨(construction.obj_equiv W).inv_fun ((equivalence_from_model L W).inverse.obj X),
    nonempty.intro ((Q_comp_equivalence_from_model_functor_iso L W).symm.app _ ≪≫
    (equivalence_from_model L W).counit_iso.app X)⟩⟩

def whiskering_left_functor : (D ⥤ E) ⥤ W.functors_inverting E :=
full_subcategory.lift _ ((whiskering_left _ _ E).obj L)
  (morphism_property.is_inverted_by.of_comp W L (inverts L W ))

instance : is_equivalence (whiskering_left_functor L W E) :=
begin
  refine is_equivalence.of_iso _ (is_equivalence.of_equivalence
    ((equivalence.congr_left (equivalence_from_model L W).symm).trans
    (construction.whiskering_left_equivalence W E))),
  refine nat_iso.of_components (λ F, eq_to_iso begin
    ext,
    change (W.Q ⋙ (localization.construction.lift L (inverts L W))) ⋙ F = L ⋙ F,
    rw construction.fac,
  end)
  (λ F₁ F₂ τ, begin
    ext X,
    dsimp [equivalence_from_model, whisker_left, construction.whiskering_left_equivalence,
      construction.whiskering_left_equivalence.functor, whiskering_left_functor,
      morphism_property.Q],
    erw [nat_trans.comp_app, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_app,
      eq_to_hom_refl, eq_to_hom_refl, comp_id, id_comp],
    all_goals
    { change (W.Q ⋙ (localization.construction.lift L (inverts L W))) ⋙ _ = L ⋙ _,
      rw construction.fac, },
  end),
end

def functor_equivalence : (D ⥤ E) ≌ (W.functors_inverting E) :=
(whiskering_left_functor L W E).as_equivalence-/

section

variables (E)

--include hL
/-@[nolint unused_arguments]
def whiskering_left_functor' :
  (D ⥤ E) ⥤ (C ⥤ E) := (whiskering_left C D E).obj L

lemma whiskering_left_functor'_eq :
  whiskering_left_functor' L W E =
    localization.whiskering_left_functor L W E ⋙ induced_functor _ := rfl

variable {E}

@[simp]
def whiskering_left_functor'_obj
  (F : D ⥤ E) : (whiskering_left_functor' L W E).obj F = L ⋙ F := rfl

instance : full (whiskering_left_functor' L W E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

instance : faithful (whiskering_left_functor' L W E) :=
by { rw whiskering_left_functor'_eq, apply_instance, }

lemma nat_trans_ext {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
  (h : ∀ (X : C), τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' :=
begin
  haveI : category_theory.ess_surj L := ess_surj L W,
  ext Y,
  rw [← cancel_epi (F₁.map (L.obj_obj_preimage_iso Y).hom), τ.naturality, τ'.naturality, h],
end

/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall say that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class lifting (F : C ⥤ E) (F' : D ⥤ E) := (iso [] : L ⋙ F' ≅ F)

section

def lift_nat_trans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [h₂ : lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
(whiskering_left_functor' L W E).preimage ((lifting.iso L W F₁ F₁').hom ≫ τ ≫ (lifting.iso L W F₂ F₂').inv)

@[simp]
lemma lift_nat_trans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) (X : C) :
  (lift_nat_trans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
    (lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ ((lifting.iso L W F₂ F₂')).inv.app X :=
congr_app (functor.image_preimage (whiskering_left_functor' L W E) _) X

@[simp, reassoc]
lemma comp_lift_nat_trans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E)
  [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂'] [h₃ : lifting L W F₃ F₃']
  (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
  lift_nat_trans L W F₁ F₂ F₁' F₂' τ ≫ lift_nat_trans L W F₂ F₃ F₂' F₃' τ' =
  lift_nat_trans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
nat_trans_ext L W _ _
  (λ X, by simp only [nat_trans.comp_app, lift_nat_trans_app, assoc, iso.inv_hom_id_app_assoc])

@[simp]
lemma lift_nat_trans_id (F : C ⥤ E) (F' : D ⥤ E) [h : lifting L W F F'] :
  lift_nat_trans L W F F F' F' (𝟙 F) = 𝟙 F' :=
nat_trans_ext L W _ _
  (λ X, by simpa only [lift_nat_trans_app, nat_trans.id_app, id_comp, iso.hom_inv_id_app])

@[simps]
def lift_nat_iso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E)
  [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂']
  (e : F₁ ≅ F₂) : F₁' ≅ F₂' :=
{ hom := lift_nat_trans L W F₁ F₂ F₁' F₂' e.hom,
  inv := lift_nat_trans L W F₂ F₁ F₂' F₁' e.inv, }

end-/

variable {E}

namespace lifting

def uniq (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂] :
  F'₁ ≅ F'₂ := lift_nat_iso L W F F F'₁ F'₂ (iso.refl F)

@[simp]
lemma uniq_hom_app (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂]
  (X : C) : (uniq L W F F'₁ F'₂).hom.app (L.obj X) = (iso L W F F'₁).hom.app X ≫ (iso L W F F'₂).inv.app X :=
begin
  dsimp only [uniq],
  simp only [lift_nat_iso_hom, iso.refl_hom, lift_nat_trans_app, nat_trans.id_app, id_comp],
end

@[simp]
lemma uniq_inv_app (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂]
  (X : C) : (uniq L W F F'₁ F'₂).inv.app (L.obj X) = (iso L W F F'₂).hom.app X ≫ (iso L W F F'₁).inv.app X :=
begin
  dsimp only [uniq],
  simp only [lift_nat_iso_inv, iso.refl_inv, lift_nat_trans_app, nat_trans.id_app, id_comp],
end

variables (L W)

/-@[simps]
instance comp_right {E' : Type*} [category E'] (F : C ⥤ E) (F' : D ⥤ E) [lifting L W F F']
  (G : E ⥤ E') : lifting L W (F ⋙ G) (F' ⋙ G) :=
⟨iso_whisker_right (iso L W F F') G⟩

@[simps]
instance id : lifting L W L (𝟭 D) :=
⟨functor.right_unitor L⟩

@[simps]
def of_isos {F₁ F₂ : C ⥤ E} {F'₁ F'₂ : D ⥤ E} (e : F₁ ≅ F₂) (e' : F'₁ ≅ F'₂)
  [lifting L W F₁ F'₁] : lifting L W F₂ F'₂ :=
⟨iso_whisker_left L e'.symm ≪≫ iso L W F₁ F'₁ ≪≫ e⟩-/

omit L

instance (F : C ⥤ D) (hF : W.is_inverted_by F) : lifting W.Q W F (construction.lift F hF) :=
⟨eq_to_iso (construction.fac F hF)⟩

end lifting

section

omit L W

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁]
  [category D₂] {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {F G : C₁ ⥤ C₂} {F' G' : D₁ ⥤ D₂}
  (hF : Comm_sq F L₁ L₂ F') (hG : Comm_sq G L₁ L₂ G') (W₁ : morphism_property C₁)
  [L₁.is_localization W₁] (τ : F ⟶ G)

include hF hG W₁ τ

def lift_nat_trans' : F' ⟶ G' :=
begin
  letI : lifting L₁ W₁ (F ⋙ L₂) F' := ⟨hF.iso⟩,
  letI : lifting L₁ W₁ (G ⋙ L₂) G' := ⟨hG.iso⟩,
  exact lift_nat_trans L₁ W₁ (F ⋙ L₂) (G ⋙ L₂) F' G' (τ ◫ (𝟙 L₂)),
end

@[simp]
lemma lift_nat_trans'_app (X₁ : C₁) : (lift_nat_trans' hF hG W₁ τ).app (L₁.obj X₁) =
  hF.iso.hom.app X₁ ≫ L₂.map (τ.app X₁) ≫ hG.iso.inv.app X₁ :=
begin
  dsimp only [lift_nat_trans'],
  rw lift_nat_trans_app,
  dsimp,
  rw id_comp,
end

omit hG τ

@[simp]
lemma lift_nat_trans'_id : lift_nat_trans' hF hF W₁ (𝟙 F) = 𝟙 F' :=
nat_trans_ext L₁ W₁ _ _ (λ X, begin
  rw [lift_nat_trans'_app, nat_trans.id_app, L₂.map_id],
  dsimp,
  rw id_comp,
  apply iso.hom_inv_id_app,
end)

omit hF

@[simp, reassoc]
lemma comp_lift_nat_trans' {F₁ F₂ F₃ : C₁ ⥤ C₂} {F₁' F₂' F₃' : D₁ ⥤ D₂}
  (H₁ : Comm_sq F₁ L₁ L₂ F₁') (H₂ : Comm_sq F₂ L₁ L₂ F₂') (H₃ : Comm_sq F₃ L₁ L₂ F₃')
  (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
  lift_nat_trans' H₁ H₂ W₁ τ ≫ lift_nat_trans' H₂ H₃ W₁ τ' =
    lift_nat_trans' H₁ H₃ W₁ (τ ≫ τ') :=
nat_trans_ext L₁ W₁ _ _ (λ X, by simp only [nat_trans.comp_app, lift_nat_trans'_app,
  assoc, iso.inv_hom_id_app_assoc, functor.map_comp])

include hF hG

@[simps]
def lift_nat_iso' (e : F ≅ G) : F' ≅ G' :=
{ hom := lift_nat_trans' hF hG W₁ e.hom,
  inv := lift_nat_trans' hG hF W₁ e.inv, }

end

section

omit L W

variables {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [category C₁] [category C₂] [category C₃]
  [category D₁] [category D₂] [category D₃]
  {F₁ G₁ : C₁ ⥤ C₂} {F₂ G₂ : C₂ ⥤ C₃}
  {F'₁ G'₁ : D₁ ⥤ D₂} {F'₂ G'₂ : D₂ ⥤ D₃}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  (H₁₂ : Comm_sq F₁ L₁ L₂ F'₁) (H₂₃ : Comm_sq F₂ L₂ L₃ F'₂)
  (K₁₂ : Comm_sq G₁ L₁ L₂ G'₁) (K₂₃ : Comm_sq G₂ L₂ L₃ G'₂)
  (W₁ : morphism_property C₁) (W₂ : morphism_property C₂)
  [L₁.is_localization W₁] [L₂.is_localization W₂]
  (τ : F₁ ⟶ G₁) (τ' : F₂ ⟶ G₂)

lemma hcomp_lift_nat_trans' :
  lift_nat_trans' H₁₂ K₁₂ W₁ τ ◫ lift_nat_trans' H₂₃ K₂₃ W₂ τ' =
    lift_nat_trans' (H₁₂.horiz_comp H₂₃) (K₁₂.horiz_comp K₂₃) W₁ (τ ◫ τ') :=
nat_trans_ext L₁ W₁ _ _ (λ X, begin
  simp only [lift_nat_trans'_app, nat_trans.hcomp_app, assoc, G'₂.map_comp],
  rw ← nat_trans.naturality_assoc,
  erw lift_nat_trans'_app,
  simp only [assoc, Comm_sq.horiz_comp_iso_hom_app, Comm_sq.horiz_comp_iso_inv_app,
    functor.map_comp],
  erw ← K₂₃.iso.inv.naturality_assoc,
  refl,
end)

end

variables {W E}

/-def lift (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  D ⥤ E :=
(functor_equivalence L W E).inverse.obj ⟨F, hF⟩

instance lift_is_lifting (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D)
  [hL : L.is_localization W] : lifting L W F (lift F hF L) :=
⟨(induced_functor _).map_iso ((functor_equivalence L W E).counit_iso.app ⟨F, hF⟩)⟩

@[simps]
def fac (F : C ⥤ E) (hF : W.is_inverted_by F) (L : C ⥤ D) [hL : L.is_localization W] :
  L ⋙ lift F hF L ≅ F :=
lifting.iso _ W _ _-/

end

section

variables {D₁ D₂ : Type*} [category D₁] [category D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  [h₁ : L₁.is_localization W] [h₂ : L₂.is_localization W]

include h₁ h₂
omit L

def uniq_equivalence : D₁ ≌ D₂ :=
(equivalence_from_model L₁ W).symm.trans (equivalence_from_model L₂ W)

def comp_uniq_equivalence_functor_iso :
  L₁ ⋙ (uniq_equivalence W L₁ L₂).functor ≅ L₂ :=
calc L₁ ⋙ (uniq_equivalence W L₁ L₂).functor ≅ (L₁ ⋙
  (equivalence_from_model L₁ W).inverse) ⋙ (equivalence_from_model L₂ W).functor : by refl
... ≅ W.Q ⋙ (equivalence_from_model L₂ W).functor :
  iso_whisker_right (comp_equivalence_from_model_inverse_iso L₁ W) _
... ≅ L₂ : Q_comp_equivalence_from_model_functor_iso L₂ W

end

end localization

namespace functor

namespace is_localization

def of_equivalence {E : Type*} [category E] (L' : C ⥤ E) (eq : D ≌ E)
  [L.is_localization W] (e : L ⋙ eq.functor ≅ L') : L'.is_localization W :=
begin
  have h : W.is_inverted_by L',
  { rw ← morphism_property.is_inverted_by.iff_of_iso W e,
    exact morphism_property.is_inverted_by.of_comp W L (localization.inverts L W) eq.functor, },
  let F₁ := localization.construction.lift L (localization.inverts L W),
  let F₂ := localization.construction.lift L' h,
  letI : localization.lifting W.Q W (L ⋙ eq.functor) F₂ :=
    localization.lifting.of_isos W.Q W e.symm (iso.refl F₂),
  let e : F₁ ⋙ eq.functor ≅ F₂ := localization.lifting.uniq W.Q W (L ⋙ eq.functor) _ _,
  exact
  { inverts := h,
    nonempty_is_equivalence := nonempty.intro (is_equivalence.of_iso e infer_instance) },
end

/-def of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.is_localization W] : L₂.is_localization W :=
begin
  have h : W.is_inverted_by L₂ := λ X Y f hf,
    by simpa only [is_iso_map_iff_of_nat_iso e.symm] using localization.inverts L₁ W f hf,
  let F₁ := localization.construction.lift L₁ (localization.inverts L₁ W),
  let F₂ := localization.construction.lift L₂ h,
  haveI : localization.lifting W.Q W L₁ F₂ :=
    localization.lifting.of_isos W.Q W e.symm (iso.refl F₂),
  exact
  { inverts := h,
    nonempty_is_equivalence := nonempty.intro
      (is_equivalence.of_iso (localization.lifting.uniq W.Q W L₁ F₁ F₂) infer_instance), },
end-/

end is_localization

end functor

namespace localization

lemma id_is_localization (hW : W ⊆ morphism_property.isomorphisms C):
  (𝟭 C).is_localization W :=
functor.is_localization.mk' _ _
  (strict_universal_property_fixed_target_id _ _ hW)
  (strict_universal_property_fixed_target_id _ _ hW)


instance identity_functor_is_localization' :
  (𝟭 C).is_localization (morphism_property.isomorphisms C) :=
functor.is_localization.mk' _ _
  (strict_universal_property_fixed_target_id _ _ (λ X Y f hf, hf))
  (strict_universal_property_fixed_target_id _ _ (λ X Y f hf, hf))

end localization

namespace localization

variables {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [category C₁] [category C₂] [category C₃]
  [category D₁] [category D₂] [category D₃]
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F'₁₂ : D₁ ⥤ D₂} {F'₂₃ : D₂ ⥤ D₃}
  {F₁₃ : C₁ ⥤ C₃} {F'₁₃ : D₁ ⥤ D₃}
  {G₁₂ : C₁ ⥤ C₂} {G₂₃ : C₂ ⥤ C₃} {G'₁₂ : D₁ ⥤ D₂} {G'₂₃ : D₂ ⥤ D₃}
  {G₁₃ : C₁ ⥤ C₃} {G'₁₃ : D₁ ⥤ D₃}
  (H₁₂ : Comm_sq F₁₂ L₁ L₂ F'₁₂) (H₂₃ : Comm_sq F₂₃ L₂ L₃ F'₂₃)
  (H₁₃ : Comm_sq F₁₃ L₁ L₃ F'₁₃)
  (K₁₂ : Comm_sq G₁₂ L₁ L₂ G'₁₂) (K₂₃ : Comm_sq G₂₃ L₂ L₃ G'₂₃)
  (K₁₃ : Comm_sq G₁₃ L₁ L₃ G'₁₃)
  (e : F₁₂ ⋙ F₂₃ ≅ F₁₃)
  (e' : G₁₂ ⋙ G₂₃ ≅ G₁₃)
  (W₁ : morphism_property C₁) (W₂ : morphism_property C₂)
  [L₁.is_localization W₁]

include H₁₂ H₂₃ H₁₃ e W₁ W₂

def lifting_comp_iso : F'₁₂ ⋙ F'₂₃ ≅ F'₁₃ :=
begin
  letI : lifting L₁ W₁ (F₁₃ ⋙ L₃) F'₁₃ := ⟨H₁₃.iso⟩,
  letI : lifting L₁ W₁ (F₁₃ ⋙ L₃) (F'₁₂ ⋙ F'₂₃) := ⟨(H₁₂.horiz_comp H₂₃).iso ≪≫ iso_whisker_right e _⟩,
  exact lifting.uniq L₁ W₁ (F₁₃ ⋙ L₃) _ _,
end

@[simp]
def lifting_comp_iso_hom : (lifting_comp_iso H₁₂ H₂₃ H₁₃ e W₁ W₂).hom =
  lift_nat_trans' (H₁₂.horiz_comp H₂₃) H₁₃ W₁ e.hom :=
begin
  apply nat_trans_ext L₁ W₁,
  intro X,
  dsimp only [lifting_comp_iso],
  simp only [lifting.uniq_hom_app, iso.trans_hom, iso_whisker_right_hom, nat_trans.comp_app,
    whisker_right_app, assoc, lift_nat_trans'_app],
end

@[simp]
def lifting_comp_iso_inv : (lifting_comp_iso H₁₂ H₂₃ H₁₃ e W₁ W₂).inv =
  lift_nat_trans' H₁₃ (H₁₂.horiz_comp H₂₃) W₁ e.inv :=
begin
  apply nat_trans_ext L₁ W₁,
  intro X,
  dsimp only [lifting_comp_iso],
  simp only [lifting.uniq_inv_app, iso.trans_inv, iso_whisker_right_inv, nat_trans.comp_app,
    whisker_right_app, lift_nat_trans'_app],
end

variables (τ₁₂ : F₁₂ ⟶ G₁₂) (τ₂₃ : F₂₃ ⟶ G₂₃) (τ₁₃ : F₁₃ ⟶ G₁₃)
  (comm_τ : (τ₁₂ ◫ τ₂₃) ≫ e'.hom = e.hom ≫ τ₁₃)

include comm_τ

lemma lifting_comp_iso_nat_trans_compatibility [L₂.is_localization W₂] :
  (lift_nat_trans' H₁₂ K₁₂ W₁ τ₁₂ ◫ lift_nat_trans' H₂₃ K₂₃ W₂ τ₂₃) ≫
    (lifting_comp_iso K₁₂ K₂₃ K₁₃ e' W₁ W₂).hom =
  (lifting_comp_iso H₁₂ H₂₃ H₁₃ e W₁ W₂).hom ≫ lift_nat_trans' H₁₃ K₁₃ W₁ τ₁₃ :=
by simp only [lifting_comp_iso_hom, comp_lift_nat_trans', hcomp_lift_nat_trans', ← comm_τ]

end localization

end category_theory
