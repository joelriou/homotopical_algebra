import for_mathlib.category_theory.localization.predicate

noncomputable theory

namespace category_theory

namespace localization

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  (L₁ : C₁ ⥤ D₁) (W₁ : morphism_property C₁) [L₁.is_localization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : morphism_property C₂) [L₂.is_localization W₂]
  {G' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁}
  [h₁ : lifting L₁ W₁ (G ⋙ L₂) G'] [h₂ : lifting L₂ W₂ (F ⋙ L₁) F']

include adj W₁ W₂ h₁ h₂

def adjunction : G' ⊣ F' := adjunction.mk_of_unit_counit
begin
  let e₁ : (G ⋙ L₂) ⋙ F' ≅ (G ⋙ F) ⋙ L₁ := iso_whisker_left G h₂.iso,
  let e₂ : (F ⋙ L₁) ⋙ G' ≅ (F ⋙ G) ⋙ L₂ := iso_whisker_left F h₁.iso,
  letI : lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    lifting.of_isos L₁ W₁ e₁ (iso.refl (G' ⋙ F')),
  letI : lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    lifting.of_isos L₂ W₂ e₂ (iso.refl (F' ⋙ G')),
  exact
  { unit := lift_nat_trans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
      ((functor.left_unitor L₁).inv ≫ nat_trans.hcomp adj.unit (𝟙 L₁)),
    counit := lift_nat_trans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂)
      (nat_trans.hcomp adj.counit (𝟙 L₂) ≫ (functor.left_unitor L₂).hom),
    left_triangle' := nat_trans_ext L₁ W₁ _ _ (λ X₁, begin
      sorry,
    end),
    right_triangle' := nat_trans_ext L₂ W₂ _ _ (λ X₂, begin
      sorry,
    end) },
end

end localization

end category_theory
