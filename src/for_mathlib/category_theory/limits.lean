import category_theory.adjunction.basic
import category_theory.limits.has_limits
import category_theory.limits.preserves.basic

noncomputable theory

namespace category_theory

open category

lemma adjunction.compatibility {C D : Type*} [category C] [category D]
  {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) {X : C} {Y : D}
  (f : G.obj X ⟶ Y) : G.map (adj.unit.app X) ≫ (F ⋙ G).map f ≫ adj.counit.app Y = f :=
by simp only [functor.comp_map, adjunction.counit_naturality, adjunction.left_triangle_components_assoc]

section

variables {C₁ C₂ D₁ D₂ : Type*} [category C₁] [category C₂]
  [category D₁] [category D₂] {G₁ : C₁ ⥤ D₁} {F₁ : D₁ ⥤ C₁}
  {G₂ : C₂ ⥤ D₂} {F₂ : D₂ ⥤ C₂}
  (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂)
  {L : C₁ ⥤ C₂} {L' : D₁ ⥤ D₂}

include adj₁ adj₂

def adjunction.adjoint_nat_trans_equiv :
  (L ⋙ G₂ ⟶ G₁ ⋙ L') ≃ (F₁ ⋙ L ⟶ L' ⋙ F₂) :=
{ to_fun := λ τ, begin
    let α := 𝟙 (F₁ ⋙ L) ◫ adj₂.unit,
    let β := (𝟙 F₁) ◫ τ ◫ (𝟙 F₂),
    let γ := adj₁.counit ◫ 𝟙 (L' ⋙ F₂),
    exact α ≫ β ≫ γ,
  end,
  inv_fun := λ τ', begin
    let α := adj₁.unit ◫ (𝟙 (L ⋙ G₂)),
    let β := (𝟙 G₁) ◫ τ' ◫ (𝟙 G₂),
    let γ := 𝟙 (G₁ ⋙ L') ◫ adj₂.counit,
    exact α ≫ β ≫ γ,
  end,
  left_inv := λ τ, begin
    ext X,
    dsimp,
    simp only [id_comp, functor.map_id, comp_id, assoc, functor.map_comp,
      adjunction.counit_naturality, adjunction.counit_naturality_assoc,
      adjunction.left_triangle_components_assoc],
    erw τ.naturality_assoc,
    dsimp,
    rw [← L'.map_comp, adj₁.left_triangle_components, L'.map_id,
      comp_id],
  end,
  right_inv := λ τ', begin
    ext Y,
    dsimp,
    simp only [functor.map_id, id_comp, assoc, functor.map_comp,
      adjunction.unit_naturality_assoc, adjunction.right_triangle_components_assoc],
    erw ← τ'.naturality,
    dsimp,
    rw [← L.map_comp_assoc, adj₁.right_triangle_components, L.map_id, id_comp],
  end, }

@[simp]
lemma adjunction.adjoint_nat_trans_equiv_app (τ : L ⋙ G₂ ⟶ G₁ ⋙ L') (Y₁ : D₁) :
  (adjunction.adjoint_nat_trans_equiv adj₁ adj₂ τ).app Y₁ =
    adj₂.unit.app (L.obj (F₁.obj Y₁)) ≫
      F₂.map (τ.app (F₁.obj Y₁)) ≫
      F₂.map (L'.map (adj₁.counit.app Y₁)) :=
begin
  dsimp [adjunction.adjoint_nat_trans_equiv],
  simp only [functor.map_id, comp_id, id_comp],
end

@[simp]
lemma adjunction.adjoint_nat_trans_equiv_symm_app (τ : F₁ ⋙ L ⟶ L' ⋙ F₂) (X₁ : C₁) :
  ((adjunction.adjoint_nat_trans_equiv adj₁ adj₂).symm τ).app X₁ =
  G₂.map (L.map (adj₁.unit.app X₁)) ≫
      G₂.map (τ.app (G₁.obj X₁)) ≫ adj₂.counit.app (L'.obj (G₁.obj X₁)) :=
begin
  dsimp [adjunction.adjoint_nat_trans_equiv],
  simp only [id_comp, functor.map_id, comp_id],
end

end

def functor.comp_const {C D : Type*} [category C] [category D]
  (F : C ⥤ D) (J : Type*) [category J] :
  F ⋙ (functor.const J) ≅ (functor.const J) ⋙ (whiskering_right J C D).obj F :=
nat_iso.of_components (λ X, nat_iso.of_components (λ j, iso.refl _) (by tidy)) (by tidy)

namespace limits

section

variables {J : Type*} {C : Type*} [category J] [category C]
  {F : (J ⥤ C) ⥤ C} (adj : functor.const J ⊣ F)

include adj

lemma is_limit_of_is_iso_adj {X : J ⥤ C} (c : cone X)
  (h : is_iso ((adj.hom_equiv _ _) c.π)) : is_limit c :=
begin
  haveI := h,
  exact
  { lift := λ s, (adj.hom_equiv _ _) s.π ≫ inv ((adj.hom_equiv _ _) c.π),
    fac' := λ s, begin
      suffices : (functor.const J).map ((adj.hom_equiv s.X X) s.π ≫ inv ((adj.hom_equiv c.X X) c.π)) ≫ c.π = s.π,
      { exact nat_trans.congr_app this, },
      apply (adj.hom_equiv _ _).injective,
      rw [adjunction.hom_equiv_naturality_left, assoc, is_iso.inv_hom_id, comp_id],
    end,
    uniq' := λ s m hm, begin
      rw [← cancel_mono ((adj.hom_equiv c.X X) c.π), assoc, is_iso.inv_hom_id, comp_id],
      apply (adj.hom_equiv _ _).symm.injective,
      simp only [adjunction.hom_equiv_naturality_left_symm, equiv.symm_apply_apply],
      ext j,
      exact hm j,
    end, },
end

lemma is_iso_adj_of_is_limit {X : J ⥤ C} {c : cone X} (hc : is_limit c) :
  is_iso ((adj.hom_equiv _ _) c.π) :=
begin
  refine is_iso.mk ⟨hc.lift (cone.mk (F.obj X) (adj.counit.app X)), _, _⟩,
  { apply hc.hom_ext,
    intro j,
    simpa only [adjunction.hom_equiv_unit, assoc, is_limit.fac, id_comp]
      using nat_trans.congr_app (adj.compatibility c.π) j, },
  { apply (adj.hom_equiv _ _).symm.injective,
    rw [adjunction.hom_equiv_naturality_left_symm, equiv.symm_apply_apply,
      adjunction.hom_equiv_counit, functor.map_id],
    ext j,
    rw id_comp,
    apply hc.fac, },
end

@[simps]
def limit_cone_of_adj (X : J ⥤ C) : limit_cone X :=
⟨cone.mk (F.obj X) (adj.counit.app X), is_limit_of_is_iso_adj adj _ (by tidy)⟩

lemma has_limits_of_shape_of_adj : has_limits_of_shape J C :=
⟨λ X, ⟨nonempty.intro (limit_cone_of_adj adj X)⟩⟩

end

section

variables {C₁ C₂ J : Type*} [category C₁] [category C₂] [category J]
  {F₁ : (J ⥤ C₁) ⥤ C₁} {F₂ : (J ⥤ C₂) ⥤ C₂} (adj₁ : functor.const J ⊣ F₁)
  (adj₂ : functor.const J ⊣ F₂) (L : C₁ ⥤ C₂)

include adj₁ adj₂

@[simp]
def limit_comparison_of_adj : F₁ ⋙ L ⟶ (whiskering_right J _ _).obj L ⋙ F₂ :=
(adjunction.adjoint_nat_trans_equiv adj₁ adj₂)(L.comp_const J).hom

lemma preserves_limit_of_adj (X : J ⥤ C₁)
  (hX : is_iso ((limit_comparison_of_adj adj₁ adj₂ L).app X)) : preserves_limit X L :=
begin
  refine preserves_limit_of_preserves_limit_cone (limit_cone_of_adj adj₁ X).is_limit _,
  refine is_limit_of_is_iso_adj adj₂ _ _,
  convert hX,
  apply (adj₂.hom_equiv _ _).symm.injective,
  ext j,
  dsimp [limit_cone_of_adj, functor.map_cone],
  rw [equiv.symm_apply_apply, cones.functoriality_obj_π_app,
    adjunction.adjoint_nat_trans_equiv_app, whiskering_right_obj_map, ← assoc,
    adjunction.hom_equiv_naturality_right_symm, nat_trans.comp_app, whisker_right_app,
    adjunction.hom_equiv_naturality_right_symm, adjunction.hom_equiv_counit,
    adjunction.left_triangle_components],
  dsimp [functor.comp_const],
  simp only [id_comp],
end

lemma preserves_limits_of_shape_of_adj
  [is_iso (limit_comparison_of_adj adj₁ adj₂ L)] : preserves_limits_of_shape J L :=
⟨λ X, preserves_limit_of_adj adj₁ adj₂ L X infer_instance⟩

end

end limits

end category_theory
