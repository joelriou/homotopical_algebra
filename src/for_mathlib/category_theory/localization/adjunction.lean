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
  haveI : lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') := ⟨sorry⟩,
  haveI : lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') := ⟨sorry⟩,
  exact
  { unit := lift_nat_trans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
      ((functor.left_unitor L₁).inv ≫ nat_trans.hcomp adj.unit (𝟙 L₁)),
    counit := lift_nat_trans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂)
      (nat_trans.hcomp adj.counit (𝟙 L₂) ≫ (functor.left_unitor L₂).hom),
    left_triangle' := sorry,
    right_triangle' := sorry, },
end

end localization

end category_theory
