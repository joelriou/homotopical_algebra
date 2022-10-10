import category_theory.monoidal.End

noncomputable theory

namespace category_theory

open category

section

variables {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃]
  {F F' : C₁ ⥤ C₂} (G : C₂ ⥤ C₃) [full G] [faithful G]

@[simps]
lemma nat_trans.equiv_hcomp_id_of_fully_faithful :
  (F ⟶ F') ≃ (F ⋙ G ⟶ F' ⋙ G) :=
{ to_fun := λ τ, τ ◫ 𝟙 G,
  inv_fun := λ τ,
  { app := λ X, G.preimage (τ.app X),
    naturality' := λ X Y f, G.map_injective
      (by simpa only [functor.map_comp, functor.image_preimage] using τ.naturality f), },
  left_inv := by tidy,
  right_inv := by tidy, }

@[simps]
def nat_iso.equiv_hcomp_refl_of_fully_faithful :
  (F ≅ F') ≃ (F ⋙ G ≅ F' ⋙ G) :=
{ to_fun := λ e, nat_iso.hcomp e (iso.refl G),
  inv_fun := λ e,
  { hom := (nat_trans.equiv_hcomp_id_of_fully_faithful G).inv_fun e.hom,
    inv := (nat_trans.equiv_hcomp_id_of_fully_faithful G).inv_fun e.inv,
    hom_inv_id' := begin
      ext X,
      apply G.map_injective,
      simpa only [equiv.inv_fun_as_coe, nat_trans.comp_app,
        nat_trans.equiv_hcomp_id_of_fully_faithful_symm_apply_app, functor.map_comp,
        functor.image_preimage, iso.hom_inv_id_app, nat_trans.id_app, functor.map_id],
    end,
    inv_hom_id' := begin
      ext X,
      apply G.map_injective,
      simpa only [equiv.inv_fun_as_coe, nat_trans.comp_app,
        nat_trans.equiv_hcomp_id_of_fully_faithful_symm_apply_app, functor.map_comp,
        functor.image_preimage, iso.inv_hom_id_app, nat_trans.id_app, functor.map_id],
    end, },
  left_inv := λ e, begin
    ext X,
    apply G.map_injective,
    simp only [equiv.inv_fun_as_coe, nat_trans.equiv_hcomp_id_of_fully_faithful_symm_apply_app,
      functor.image_preimage, nat_iso.hcomp, iso.refl_hom, nat_trans.hcomp_id_app],
  end,
  right_inv := λ e, begin
    ext X,
    simp only [nat_iso.hcomp, equiv.inv_fun_as_coe, iso.refl_hom, nat_trans.hcomp_id_app,
      nat_trans.equiv_hcomp_id_of_fully_faithful_symm_apply_app, functor.image_preimage],
  end, }

end

namespace shift

namespace compatibility

local attribute [instance, reducible] endofunctor_monoidal_category

variables {C D₁ D₂ : Type*} [category C] [category D₁] [category D₂]
  [monoidal_category C]
  (S₁ : monoidal_functor C (D₁ ⥤ D₁))
  (S₂ : monoidal_functor C (D₂ ⥤ D₂))
  (F : D₁ ⥤ D₂)

include F S₁ S₂

@[simp]
def comm_shift (a : C) := S₁.obj a ⋙ F ≅ F ⋙ S₂.obj a

namespace comm_shift

@[simps]
def unit : comm_shift S₁ S₂ F (𝟙_ C) :=
iso_whisker_right S₁.ε_iso.symm F ≪≫ F.left_unitor ≪≫
  F.right_unitor.symm ≪≫ iso_whisker_left F S₂.ε_iso

variables {S₁ S₂ F}

@[simps]
def change {a b : C} (e : comm_shift S₁ S₂ F a) (f : a ≅ b) :
  comm_shift S₁ S₂ F b :=
iso_whisker_right (S₁.map_iso f.symm) _ ≪≫ e ≪≫ iso_whisker_left _ (S₂.map_iso f)

@[simp]
lemma change_refl {a : C} (e : comm_shift S₁ S₂ F a) :
  e.change (iso.refl a) = e := by tidy

@[simp]
lemma change_comp {a b c : C} (e : comm_shift S₁ S₂ F a) (f : a ≅ b) (g : b ≅ c) :
  (e.change f).change g = e.change (f ≪≫ g) := by tidy

variables (S₁ S₂ F)

@[simps]
def change_equiv {a b : C} (f : a ≅ b) :
  comm_shift S₁ S₂ F a ≃ comm_shift S₁ S₂ F b :=
{ to_fun := λ e, e.change f,
  inv_fun := λ e, e.change f.symm,
  left_inv := by tidy,
  right_inv := by tidy, }

lemma change_injective {a b : C} (f : a ≅ b) :
  function.injective (λ (e : comm_shift S₁ S₂ F a), e.change f) :=
(change_equiv S₁ S₂ F f).injective

variables {S₁ S₂ F}

@[simps]
def comp {a b : C} (e₁ : comm_shift S₁ S₂ F a) (e₂ : comm_shift S₁ S₂ F b) :
  comm_shift S₁ S₂ F (a ⊗ b) :=
iso_whisker_right (S₁.μ_iso a b).symm F ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left _ e₂ ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right e₁ _ ≪≫ functor.associator _ _ _ ≪≫ iso_whisker_left _ (S₂.μ_iso a b)

lemma comp_unit {a : C } (e : comm_shift S₁ S₂ F a) :
  e.comp (unit _ _ _) = e.change (ρ_ a).symm :=
begin
  ext X,
  dsimp [comp, unit],
  simp only [id_comp, assoc, μ_inv_hom_app_assoc, ← F.map_comp_assoc,
    ε_inv_app_obj, obj_zero_map_μ_app, ε_hom_inv_app_assoc],
end

lemma unit_comp {a : C} (e : comm_shift S₁ S₂ F a) :
  (unit _ _ _).comp e = e.change (λ_ a).symm :=
begin
  apply change_injective S₁ S₂ F (λ_ a),
  simp only [change_comp, iso.symm_self_id, change_refl],
  ext X,
  dsimp [comp, unit, functor.comp],
  simp only [id_comp, assoc, obj_ε_app, μ_inv_hom_app_assoc,
    map_inv_hom_app, comp_id, ← nat_trans.naturality, (S₂.obj a).map_comp,
    ← F.map_comp_assoc, obj_ε_inv_app, μ_inv_hom_app_assoc,
    map_inv_hom_app, F.map_id, id_comp],
end

lemma comp_assoc {a b c : C} (e₁ : comm_shift S₁ S₂ F a) (e₂ : comm_shift S₁ S₂ F b)
  (e₃ : comm_shift S₁ S₂ F c) :
  (e₁.comp e₂).comp e₃ = (e₁.comp (e₂.comp e₃)).change (α_ _ _ _).symm :=
begin
  ext X,
  dsimp [comp],
  simpa only [id_comp, obj_μ_app, μ_naturality_assoc, assoc, μ_inv_hom_app, comp_id,
    ← cancel_epi (F.map ((S₁.μ_iso (a ⊗ b) c).hom.app X)), (S₂.obj c).map_comp,
    ← F.map_comp_assoc, iso.hom_inv_id_app, F.map_id, monoidal_functor.μ_iso_hom,
    ← obj_μ_inv_app, μ_hom_inv_app] using (e₃.hom.naturality_assoc _ _).symm,
end

@[simps]
def comp_cancel {a b : C} (e₁ : comm_shift S₁ S₂ F (a ⊗ b)) (e₂ : comm_shift S₁ S₂ F b)
  [is_equivalence (S₂.obj b)] :
  comm_shift S₁ S₂ F a :=
(nat_iso.equiv_hcomp_refl_of_fully_faithful (S₂.obj b)).symm
(functor.associator _ _ _ ≪≫ iso_whisker_left _ e₂.symm ≪≫
    (functor.associator _ _ _).symm ≪≫ iso_whisker_right (S₁.μ_iso a b) _ ≪≫
    e₁ ≪≫ iso_whisker_left F (S₂.μ_iso a b).symm ≪≫ (functor.associator _ _ _).symm)

@[simps]
def comp_equiv {b : C} (f : comm_shift S₁ S₂ F b) [is_equivalence (S₂.obj b)] (a : C) :
  comm_shift S₁ S₂ F a ≃ comm_shift S₁ S₂ F (a ⊗ b) :=
{ to_fun := λ e, e.comp f,
  inv_fun := λ e, e.comp_cancel f,
  left_inv := λ e, begin
    apply (nat_iso.equiv_hcomp_refl_of_fully_faithful (S₂.obj b)).injective,
    simp only [comp_cancel, equiv.apply_symm_apply],
    ext X,
    simp only [nat_iso.hcomp, iso.trans_hom, iso_whisker_left_hom, iso.symm_hom,
      iso_whisker_right_hom, monoidal_functor.μ_iso_hom,
      nat_trans.comp_app, functor.associator_hom_app, whisker_left_app,
      functor.associator_inv_app, whisker_right_app,
      comp_hom_app, comp_id, assoc, μ_hom_inv_app, id_comp, iso.refl_hom,
      nat_iso.equiv_hcomp_refl_of_fully_faithful_apply, nat_trans.hcomp_id_app,
      ← F.map_comp_assoc, F.map_id, f.inv_hom_id_app_assoc],
    apply comp_id,
  end,
  right_inv := λ e, begin
    ext X,
    simp only [comp_hom_app, comp_cancel_hom,  whisker_right_app, id_comp,
      nat_trans.equiv_hcomp_id_of_fully_faithful_symm_apply_app, nat_trans.comp_app,
      functor.associator_hom_app, whisker_left_app, functor.associator_inv_app,
      functor.image_preimage, assoc, μ_inv_hom_app, iso.hom_inv_id_app_assoc,
      ← F.map_comp_assoc, F.map_id],
    apply comp_id,
  end, }

end comm_shift

end compatibility

end shift

end category_theory
