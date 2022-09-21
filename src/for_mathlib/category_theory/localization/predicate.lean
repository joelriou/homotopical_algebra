/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.category_theory.localization.construction2

noncomputable theory

open category_theory.category category_theory

namespace category_theory

namespace functor

lemma assoc {C₁ C₂ C₃ C₄ : Type*} [category C₁] [category C₂] [category C₃] [category C₄]
  (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄) :
  (F₁ ⋙ F₂) ⋙ F₃ = F₁ ⋙ F₂ ⋙ F₃ := by refl

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

@[simp]
lemma image_preimage_iso {X Y : C} (e : F.obj X ≅ F.obj Y) : F.map_iso (F.preimage_iso e) = e :=
by tidy

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

structure strict_universal_property_fixed_target :=
(inverts_W : W.is_inverted_by L)
(lift : Π (F : C ⥤ E) (hF : W.is_inverted_by F), D ⥤ E)
(fac : Π (F : C ⥤ E) (hF : W.is_inverted_by F), L ⋙ lift F hF = F)
(uniq : Π (F₁ F₂ : D ⥤ E) (h : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂)

def strict_universal_property_fixed_target.for_Q : strict_universal_property_fixed_target W.Q W E :=
{ inverts_W := W.Q_inverts,
  lift := construction.lift,
  fac := construction.fac,
  uniq := construction.uniq, }

end localization

namespace functor

variables (h₁ : localization.strict_universal_property_fixed_target L W D)
  (h₂ : localization.strict_universal_property_fixed_target L W W.localization)

namespace is_localization.mk'

lemma unit_eq :
  𝟭 W.localization = localization.construction.lift L h₁.inverts_W ⋙ h₂.lift W.Q W.Q_inverts :=
begin
  apply localization.construction.uniq,
  rw [← functor.assoc, localization.construction.fac, h₂.fac, functor.comp_id],
end

lemma counit_eq :
  h₂.lift W.Q W.Q_inverts ⋙ localization.construction.lift L h₁.inverts_W = 𝟭 D :=
begin
  apply h₁.uniq,
  rw [← functor.assoc, h₂.fac, localization.construction.fac, functor.comp_id],
end

def equivalence : W.localization ≌ D :=
{ functor := localization.construction.lift L h₁.inverts_W,
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

def is_localization.mk' :
  is_localization L W :=
{ inverts_W := h₁.inverts_W,
  is_equivalence := is_equivalence.of_equivalence (is_localization.mk'.equivalence L W h₁ h₂), }

end functor

namespace localization

variable [L.is_localization W]
include L W

def as_localization : L.is_localization W := infer_instance

lemma inverts_W : W.is_inverted_by L := (as_localization _ _).inverts_W

@[simps]
def iso_of_W {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
begin
  haveI : is_iso (L.map f) := inverts_W L W f hf,
  exact as_iso (L.map f),
end

instance is_equivalence_from_model := (as_localization L W).is_equivalence

def equivalence_from_model : W.localization ≌ D :=
(localization.construction.lift L (inverts_W L W)).as_equivalence

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

section

variables [hL : L.is_localization W] (E)

include hL
@[nolint unused_arguments]
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

omit hL

/-- When `L : C ⥤ D` is a localization functor for `W : morphism_property C` and
`F : C ⥤ E` is a functor, we shall that `F' : D ⥤ E` lifts `F` if the obvious diagram
is commutative up to an isomorphism. -/
class lifting (F : C ⥤ E) (F' : D ⥤ E) := (iso [] : L ⋙ F' ≅ F)

namespace lifting

/-def F {F : C ⥤ E} {F' : D ⥤ E} (h : lifting L W F F') : W.functors_inverting E :=
⟨F, begin
  rw ← morphism_property.is_inverted_by.iff_of_iso W (lifting.iso L W F F'),
  exact morphism_property.is_inverted_by.of_comp W L (as_localization L W).inverts_W F',
end⟩-/

variables (L W)

def uniq (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂] :
  F'₁ ≅ F'₂ :=
(whiskering_left_functor' L W E).preimage_iso ((iso L W F F'₁).trans (iso L W F F'₂).symm)

lemma uniq_refl (F : C ⥤ E) (F' : D ⥤ E) [lifting L W F F'] :
  uniq L W F F' F' = iso.refl F' :=
begin
  dsimp only [uniq],
  simpa only [iso.self_symm_id] using functor.preimage_iso_refl _ _,
end

lemma uniq_symm (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂] :
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

lemma uniq_whiskering (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁]
  [lifting L W F F'₂] :
  iso_whisker_left L (uniq L W F F'₁ F'₂) = (iso L W F F'₁).trans (iso L W F F'₂).symm :=
functor.image_preimage_iso _ _

lemma uniq_app (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂]
  (X : C) : (uniq L W F F'₁ F'₂).app (L.obj X) = (iso L W F F'₁).app X ≪≫ (iso L W F F'₂).symm.app X :=
congr_arg (λ (e : ((_ : C ⥤ E) ≅ _)), e.app X) (uniq_whiskering L W F F'₁ F'₂)

@[simp]
lemma uniq_hom_app (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂]
  (X : C) : (uniq L W F F'₁ F'₂).hom.app (L.obj X) = (iso L W F F'₁).hom.app X ≫ (iso L W F F'₂).inv.app X :=
begin
  change ((uniq L W F F'₁ F'₂).app (L.obj X)).hom = _,
  simpa only [uniq_app],
end

@[simp]
lemma uniq_inv_app (F : C ⥤ E) (F'₁ F'₂ : D ⥤ E) [lifting L W F F'₁] [lifting L W F F'₂]
  (X : C) : (uniq L W F F'₁ F'₂).inv.app (L.obj X) = (iso L W F F'₂).hom.app X ≫ (iso L W F F'₁).inv.app X :=
begin
  change ((uniq L W F F'₁ F'₂).app (L.obj X)).inv = _,
  simpa only [uniq_app],
end

@[simps]
instance comp_right {E' : Type*} [category E'] (F : C ⥤ E) (F' : D ⥤ E) [lifting L W F F']
  (G : E ⥤ E') : lifting L W (F ⋙ G) (F' ⋙ G) :=
⟨iso_whisker_right (iso L W F F') G⟩

@[simps]
instance id : lifting L W L (𝟭 D) :=
⟨functor.right_unitor L⟩

@[simps]
def of_isos {F₁ F₂ : C ⥤ E} {F'₁ F'₂ : D ⥤ E} (e : F₁ ≅ F₂) (e' : F'₁ ≅ F'₂)
  [lifting L W F₁ F'₁] : lifting L W F₂ F'₂ :=
⟨iso_whisker_left L e'.symm ≪≫ iso L W F₁ F'₁ ≪≫ e⟩

omit L

instance (F : C ⥤ D) (hF : W.is_inverted_by F) : lifting W.Q W F (construction.lift F hF) :=
⟨eq_to_iso (construction.fac F hF)⟩

end lifting

lemma nat_trans_ext {F₁ F₂ : D ⥤ E} (τ τ' : F₁ ⟶ F₂)
  (h : ∀ (X : C), τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' :=
begin
  haveI : category_theory.ess_surj L := ess_surj L W,
  ext Y,
  rw [← cancel_epi (F₁.map (L.obj_obj_preimage_iso Y).hom), τ.naturality, τ'.naturality, h],
end

def lift_nat_trans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [h₂ : lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
(whiskering_left_functor' L W E).preimage ((lifting.iso L W F₁ F₁').hom ≫ τ ≫ (lifting.iso L W F₂ F₂').inv)

@[simp]
lemma comp_lift_nat_trans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E)
  [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂'] [h₃ : lifting L W F₃ F₃']
  (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
  lift_nat_trans L W F₁ F₂ F₁' F₂' τ ≫ lift_nat_trans L W F₂ F₃ F₂' F₃' τ' =
  lift_nat_trans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
begin
  dsimp only [lift_nat_trans],
  simp only [← preimage_comp, assoc, iso.inv_hom_id_assoc],
end

@[simp]
lemma lift_nat_trans_id (F : C ⥤ E) (F' : D ⥤ E) [h : lifting L W F F'] :
  lift_nat_trans L W F F F' F' (𝟙 F) = 𝟙 F' :=
begin
  dsimp only [lift_nat_trans],
  simp only [id_comp, iso.hom_inv_id, preimage_id],
end

def lift_nat_iso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : lifting L W F₁ F₁'] [h₂ : lifting L W F₂ F₂']
  (e : F₁ ≅ F₂) : F₁' ≅ F₂' :=
{ hom := lift_nat_trans L W F₁ F₂ F₁' F₂' e.hom,
  inv := lift_nat_trans L W F₂ F₁ F₂' F₁' e.inv, }

@[simp]
lemma lift_nat_trans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [lifting L W F₁ F₁']
  [lifting L W F₂ F₂'] (τ : F₁ ⟶ F₂) (X : C) :
  (lift_nat_trans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
    (lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ ((lifting.iso L W F₂ F₂')).inv.app X :=
congr_app (functor.image_preimage (whiskering_left_functor' L W E) _) X

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
lifting.iso _ W _ _

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
    exact morphism_property.is_inverted_by.of_comp W L (localization.inverts_W L W) eq.functor, },
  let F₁ := localization.construction.lift L (localization.inverts_W L W),
  let F₂ := localization.construction.lift L' h,
  letI : localization.lifting W.Q W (L ⋙ eq.functor) F₂ :=
    localization.lifting.of_isos W.Q W e.symm (iso.refl F₂),
  let e : F₁ ⋙ eq.functor ≅ F₂ := localization.lifting.uniq W.Q W (L ⋙ eq.functor) _ _,
  exact
  { inverts_W := h,
    is_equivalence := is_equivalence.of_iso e infer_instance, },
end

end is_localization

end functor

end category_theory
