import for_mathlib.category_theory.localization.predicate

noncomputable theory

namespace category_theory

open category

namespace localization

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  (L₁ : C₁ ⥤ D₁) (W₁ : morphism_property C₁) [L₁.is_localization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : morphism_property C₂) [L₂.is_localization W₂]
  (G' : D₁ ⥤ D₂) (F' : D₂ ⥤ D₁)

include adj

def adjunction [lifting L₁ W₁ (G ⋙ L₂) G'] [lifting L₂ W₂ (F ⋙ L₁) F'] :
  G' ⊣ F' := adjunction.mk_of_unit_counit
begin
  let α₁ := lifting.iso L₂ W₂ (F ⋙ L₁) F',
  let α₂ := lifting.iso L₁ W₁ (G ⋙ L₂) G',
  let e₁ : (G ⋙ L₂) ⋙ F' ≅ (G ⋙ F) ⋙ L₁ := iso_whisker_left G α₁,
  let e₂ : (F ⋙ L₁) ⋙ G' ≅ (F ⋙ G) ⋙ L₂ := iso_whisker_left F α₂,
  letI : lifting L₁ W₁ ((G ⋙ F) ⋙ L₁) (G' ⋙ F') :=
    lifting.of_isos L₁ W₁ e₁ (iso.refl (G' ⋙ F')),
  letI : lifting L₂ W₂ ((F ⋙ G) ⋙ L₂) (F' ⋙ G') :=
    lifting.of_isos L₂ W₂ e₂ (iso.refl (F' ⋙ G')),
  let ε := lift_nat_trans L₁ W₁ L₁ ((G ⋙ F) ⋙ L₁) (𝟭 D₁) (G' ⋙ F')
    ((functor.left_unitor L₁).inv ≫ nat_trans.hcomp adj.unit (𝟙 L₁)),
  let η := lift_nat_trans L₂ W₂ ((F ⋙ G) ⋙ L₂) L₂ (F' ⋙ G') (𝟭 D₂)
      (nat_trans.hcomp adj.counit (𝟙 L₂) ≫ (functor.left_unitor L₂).hom),
  have hε : ∀ (X₁ : C₁), ε.app (L₁.obj X₁) = L₁.map (adj.unit.app X₁) ≫
    α₁.inv.app (G.obj X₁) ≫ F'.map (α₂.inv.app X₁),
  { intro X₁,
    rw lift_nat_trans_app,
    dsimp,
    simp only [id_comp, comp_id], },
  have hη : ∀ (X₂ : C₂), η.app (L₂.obj X₂) = G'.map (α₁.hom.app X₂) ≫
    α₂.hom.app (F.obj X₂) ≫ L₂.map (adj.counit.app X₂),
  { intro X₂,
    rw lift_nat_trans_app,
    dsimp,
    simp only [id_comp, comp_id, assoc], },
  exact
  { unit := ε,
    counit := η,
    left_triangle' := nat_trans_ext L₁ W₁ _ _ (λ X₁, begin
      have eq := congr_app adj.left_triangle X₁,
      dsimp at ⊢ eq,
      erw [id_comp, hε, G'.map_comp, G'.map_comp, assoc, assoc, η.naturality, hη, assoc, assoc],
      slice_lhs 2 3 { erw [← G'.map_comp, α₁.inv_hom_id_app, G'.map_id], },
      erw [assoc, assoc, id_comp, α₂.hom.naturality_assoc, ← L₂.map_comp_assoc, eq,
        L₂.map_id, id_comp, α₂.hom_inv_id_app],
      refl,
    end),
    right_triangle' := nat_trans_ext L₂ W₂ _ _ (λ X₂, begin
      have eq := congr_app adj.right_triangle X₂,
      dsimp at ⊢ eq,
      erw [id_comp, hη, F'.map_comp, F'.map_comp, ← ε.naturality_assoc, hε, assoc, assoc],
      slice_lhs 4 5 { erw [← F'.map_comp, α₂.inv_hom_id_app, F'.map_id], },
      erw [id_comp, ← α₁.inv.naturality, ← L₁.map_comp_assoc, eq,
        L₁.map_id, id_comp, α₁.hom_inv_id_app],
      refl,
    end) },
end

@[simp]
lemma adjunction_unit_app [lifting L₁ W₁ (G ⋙ L₂) G'] [lifting L₂ W₂ (F ⋙ L₁) F'] (X₁ : C₁) :
  (adjunction adj L₁ W₁ L₂ W₂ G' F').unit.app (L₁.obj X₁) =
    L₁.map (adj.unit.app X₁) ≫ (lifting.iso L₂ W₂ (F ⋙ L₁) F').inv.app (G.obj X₁) ≫
    F'.map ((lifting.iso L₁ W₁ (G ⋙ L₂) G').inv.app X₁) :=
begin
  dsimp only [adjunction, adjunction.mk_of_unit_counit],
  rw lift_nat_trans_app,
  dsimp,
  simp only [id_comp, comp_id],
end

@[simp]
lemma adjunction_counit_app [lifting L₁ W₁ (G ⋙ L₂) G'] [lifting L₂ W₂ (F ⋙ L₁) F'] (X₂ : C₂) :
  (adjunction adj L₁ W₁ L₂ W₂ G' F').counit.app (L₂.obj X₂) =
    G'.map (((lifting.iso L₂ W₂ (F ⋙ L₁) F')).hom.app X₂) ≫
      (lifting.iso L₁ W₁ (G ⋙ L₂) G').hom.app (F.obj X₂) ≫ L₂.map (adj.counit.app X₂) :=
begin
  dsimp only [adjunction, adjunction.mk_of_unit_counit],
  rw lift_nat_trans_app,
  dsimp,
  simp only [id_comp, comp_id, assoc],
end

end localization

end category_theory
