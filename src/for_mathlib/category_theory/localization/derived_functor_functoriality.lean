import for_mathlib.category_theory.localization.derived_functor

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace structured_arrow

variables {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [category C₁] [category C₂]
  [category C₃] [category D₁] [category D₂] [category D₃]
  {P₁ : C₁ ⥤ D₁} {P₂ : C₂ ⥤ D₂} {P₃ : C₃ ⥤ D₃}
  {A : C₁ ⥤ C₂} {B : D₁ ⥤ D₂} {A' : C₂ ⥤ C₃} {B' : D₂ ⥤ D₃}
  (τ : P₁ ⋙ B ⟶ A ⋙ P₂) (τ' : P₂ ⋙ B' ⟶ A' ⋙ P₃) (Y : D₁)

@[simps]
def whisker :
  structured_arrow Y P₁ ⥤ structured_arrow (B.obj Y) P₂ :=
{ obj := λ X, structured_arrow.mk (B.map X.hom ≫ τ.app X.right),
  map := λ X X' f, structured_arrow.hom_mk (A.map f.right) begin
    dsimp,
    simp only [← structured_arrow.w f, category.assoc, B.map_comp],
    erw τ.naturality,
    refl,
  end, }

-- unnecessary
@[simps]
def whisker_comp_iso
  (τ'' : P₁ ⋙ (B ⋙ B') ⟶ (A ⋙ A') ⋙ P₃)
  (hτ : τ'' = (functor.associator P₁ B B').inv ≫ whisker_right τ B' ≫
    (functor.associator A P₂ B').hom ≫ whisker_left A τ' ≫ (functor.associator A A' P₃).inv) :
  whisker τ Y ⋙ whisker τ' (B.obj Y) ≅
    whisker τ'' Y :=
nat_iso.of_components (λ X, structured_arrow.iso_mk (iso.refl _) begin
  dsimp,
  simp only [hτ, functor.map_comp, assoc, functor.map_id, comp_id, nat_trans.comp_app, functor.associator_inv_app,
    whisker_right_app, functor.associator_hom_app, whisker_left_app, id_comp],
end) (by tidy)

instance full_whisker [full A] [faithful B] [is_iso τ] : full (whisker τ Y) :=
functor.full_of_surjective _ (λ X₁ X₂ f, begin
  refine ⟨structured_arrow.hom_mk (A.preimage f.right) (B.map_injective _), _⟩,
  { have eq := structured_arrow.w f,
    dsimp at eq,
    erw [B.map_comp, ← cancel_mono (τ.app X₂.right), ← eq, assoc, assoc, τ.naturality],
    dsimp,
    simp only [functor.image_preimage], },
  { ext,
    dsimp,
    simp, },
end)

instance faithful_whisker [faithful A] : faithful (whisker τ Y) :=
⟨λ X₁ X₂ f₁ f₂ hf, begin
  ext,
  exact A.map_injective ((structured_arrow.proj _ _).congr_map hf),
end⟩

instance ess_surj [ess_surj A] [full B] [is_iso τ] : ess_surj (whisker τ Y) :=
⟨λ X, ⟨structured_arrow.mk (B.preimage (X.hom ≫
  P₂.map (A.obj_obj_preimage_iso X.right).inv ≫ (inv τ).app _)),
  ⟨structured_arrow.iso_mk (A.obj_obj_preimage_iso X.right) begin
    dsimp,
    simp only [nat_iso.is_iso_inv_app, functor.image_preimage, assoc, is_iso.inv_hom_id, comp_id,
      ← P₂.map_comp, iso.inv_hom_id, P₂.map_id],
  end⟩⟩⟩

instance is_equivalence_whisker
  [is_iso τ] [is_equivalence A] [full B] [faithful B] : is_equivalence (whisker τ Y) :=
begin
  haveI : ess_surj A := -- `ess_surj_of_is_equivalence` should be an instance
    ⟨λ X, ⟨(is_equivalence.inverse A).obj X, ⟨is_equivalence.counit_iso.app X⟩⟩⟩,
  apply equivalence.of_fully_faithfully_ess_surj,
end

end structured_arrow

namespace functor

namespace is_right_derived_functor

section

variables {C D D' H : Type*} [category C] [category D] [category D'] [category H]
  {F : C ⥤ D} (RF : H ⥤ D) {L : C ⥤ H} (α : F ⟶ L ⋙ RF) (e : D ≌ D')
  (W : morphism_property C) [L.is_localization W]

lemma of_equivalence_comp_right [RF.is_right_derived_functor α]
  (β : F ⋙ e.functor ⟶ L ⋙ RF ⋙ e.functor)
  (hβ : β = whisker_right α e.functor ≫ (functor.associator _ _ _).hom) :
  (RF ⋙ e.functor).is_right_derived_functor β :=
begin
  let e' : (whiskering_left C H D).obj L ⋙ (whiskering_right C D D').obj e.functor ≅
    (whiskering_right H D D').obj e.functor ⋙ (whiskering_left C H D').obj L :=
    nat_iso.of_components (λ X, iso.refl _) (by tidy),
  exact ⟨⟨limits.is_initial.of_iso (limits.is_initial.is_initial_obj (structured_arrow.whisker e'.hom F) (structured_arrow.mk α)
    (is_right_derived_functor.is_initial α).some)
    (structured_arrow.iso_mk (iso.refl _) (by { rw hβ, tidy, }))⟩⟩,
end

instance of_equivalence_comp_right' [RF.is_right_derived_functor α] (G : D ⥤ D')
  [is_equivalence G] :
  (RF ⋙ G).is_right_derived_functor (whisker_right α G ≫ (functor.associator _ _ _).hom) :=
of_equivalence_comp_right RF α (as_equivalence G) _ rfl

instance has_right_derived_functor_equivalence_comp_right (G : D ⥤ D')
  [is_equivalence G] [F.has_right_derived_functor W] :
  (F ⋙ G).has_right_derived_functor W :=
is_right_derived_functor.has_right_derived_functor (F ⋙ G)
  (F.right_derived_functor W.Q W ⋙ G) W.Q
  (whisker_right (F.right_derived_functor_α W.Q W) G ≫ (functor.associator _ _ _).hom) W

end

section

-- of_equivalence_comp_left
-- data : categories C, C', H, H', functor C' ⥤ D...

end
end is_right_derived_functor

end functor

end category_theory
