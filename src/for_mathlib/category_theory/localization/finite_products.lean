import for_mathlib.category_theory.localization.products
import for_mathlib.category_theory.localization.adjunction
import for_mathlib.category_theory.finite_products

noncomputable theory

universes v v' u u'

namespace category_theory

namespace limits

def is_limit_postcompose {J C : Type*} [category J] [category C] {F₁ F₂ : J ⥤ C}
  (e : F₁ ≅ F₂) {c : cone F₁} (hc : is_limit c) : is_limit ((cones.postcompose e.hom).obj c) :=
{ lift := λ s, hc.lift ((cones.postcompose e.inv).obj s),
  fac' := λ s j, begin
    simp only [cones.postcompose_obj_π, nat_trans.comp_app, is_limit.fac_assoc, category.assoc, iso.inv_hom_id_app,
  category.comp_id],
  end,
  uniq' := λ s m w, hc.hom_ext (λ j, begin
    simp only [cones.postcompose_obj_π, nat_trans.comp_app] at w,
    simp only [← cancel_mono (e.hom.app j), w, category.assoc, is_limit.fac,
      cones.postcompose_obj_π, nat_trans.comp_app, iso.inv_hom_id_app, category.comp_id],
  end), }

end limits

open limits category

variables {C : Type u} {D : Type u'} [category.{v} C] [category.{v'} D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]

namespace morphism_property

lemma isomorphisms.is_inverted_by (F : C ⥤ D) :
  (morphism_property.isomorphisms C).is_inverted_by F := λ X Y f hf,
begin
  rw morphism_property.isomorphisms.iff at hf,
  haveI := hf,
  apply_instance,
end

def stable_under_limits_of_shape (W : morphism_property C) (J : Type*) [category J] : Prop :=
∀ (X₁ X₂ : J ⥤ C) (c₁ : cone X₁) (c₂ : cone X₂) (h₁ : is_limit c₁) (h₂ : is_limit c₂)
  (f : X₁ ⟶ X₂) (hf : Π (j : J), W (nat_trans.app f j)), W (h₂.lift (cone.mk _ (c₁.π ≫ f)))

abbreviation stable_under_products_of_shape (W : morphism_property C) (J : Type*) : Prop :=
W.stable_under_limits_of_shape (discrete J)

@[simps]
def stable_under_products_of_shape.iso_aux {J D : Type*} [category D]
  (X : discrete J ⥤ D) (c : cone X) (hc : is_limit c)
  [has_product (λ j, X.obj (discrete.mk j))] :
  c.X ≅ ∏ (λ j, X.obj (discrete.mk j)) :=
{ hom := pi.lift (λ j, c.π.app (discrete.mk j)),
  inv := hc.lift (cone.mk (∏ (λ j, X.obj (discrete.mk j)))
    { app := by { rintro ⟨j⟩, exact pi.π _ j, },
    naturality' := begin
      rintro ⟨j₁⟩ ⟨j₂⟩ f,
      have h := discrete.eq_of_hom f,
      dsimp at h,
      subst h,
      simp only [subsingleton.elim f (𝟙 _), discrete.functor_map_id, id_comp, comp_id],
    end, }),
  hom_inv_id' := hc.hom_ext begin
    rintro ⟨j⟩,
    simp only [id_comp, assoc, is_limit.fac, limit.lift_π, fan.mk_π_app],
  end,
  inv_hom_id' := begin
    ext j,
    discrete_cases,
    simp only [id_comp, assoc, limit.lift_π, fan.mk_π_app, is_limit.fac],
  end, }

lemma stable_under_products_of_shape.mk (W : morphism_property C) (J : Type*)
  (hW₀ : W.respects_iso) [has_products_of_shape J C]
  (hW : ∀ (X₁ X₂ : J → C) (f : Π j, X₁ j ⟶ X₂ j) (hf : Π (j : J), W (f j)),
    W (pi.map f)) : W.stable_under_products_of_shape J :=
λ X₁ X₂ c₁ c₂ hc₁ hc₂ f hf, begin
  let Y₁ := λ j, X₁.obj (discrete.mk j),
  let Y₂ := λ j, X₂.obj (discrete.mk j),
  let φ : Π j, Y₁ j ⟶ Y₂ j := λ j, f.app (discrete.mk j),
  have hf' := hW Y₁ Y₂ φ (λ j, (hf (discrete.mk j))),
  refine (hW₀.arrow_mk_iso_iff _).mpr hf',
  refine arrow.iso_mk (stable_under_products_of_shape.iso_aux X₁ c₁ hc₁)
    (stable_under_products_of_shape.iso_aux X₂ c₂ hc₂) _,
  ext j,
  discrete_cases,
  dsimp,
  simp only [limit.lift_map, limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app,
    fan.mk_π_app, discrete.nat_trans_app, assoc, is_limit.fac],
end

class stable_under_finite_products (W : morphism_property C) : Prop :=
(condition [] : ∀ (J : Type) [finite J], stable_under_products_of_shape W J)

abbreviation stable_under_binary_products (W : morphism_property C) :=
  W.stable_under_products_of_shape walking_pair

namespace stable_under_products_of_shape

variable {W}

lemma lim_map {J : Type*} (h : W.stable_under_products_of_shape J) {X Y : discrete J ⥤ C}
  (f : X ⟶ Y) [has_products_of_shape J C]
  (hf : ∀ j, W (f.app (discrete.mk j))) : W (lim.map f) :=
h X Y _ _ (limit.is_limit X) (limit.is_limit Y) f
  (by { rintro ⟨j⟩, exact hf j, })

end stable_under_products_of_shape

end morphism_property

namespace localization

include L W

@[protected]
lemma has_products_of_shape (J : Type) [finite J] [W.contains_identities]
  [has_products_of_shape J C] (hW : W.stable_under_products_of_shape J) :
  has_products_of_shape J D :=
begin
  let G : C ⥤ _ := functor.const (discrete J),
  let F : ((discrete J) ⥤ C) ⥤ C := lim,
  let adj : G ⊣ F := const_lim_adj,
  let L' := (whiskering_right (discrete J) C D).obj L,
  let G' : D ⥤ _ := functor.const (discrete J),
  let W' := morphism_property.functor_category W (discrete J),
  have hF : W'.is_inverted_by (F ⋙ L),
  { intros X Y f hf,
    dsimp,
    exact localization.inverts L W (F.map f) (hW.lim_map f (λ j, hf (discrete.mk j))), },
  let F' := localization.lift (F ⋙ L) hF L',
  haveI : lifting L W (G ⋙ L') G' := ⟨L.comp_const (discrete J)⟩,
  exact has_limits_of_shape_of_adj (adj.localization L W L' W' G' F'),
end

@[protected]
lemma has_finite_products [W.contains_identities]
  [has_finite_products C] [W.stable_under_finite_products] :
  has_finite_products D :=
⟨λ n, by { exact localization.has_products_of_shape L W (fin n)
  (morphism_property.stable_under_finite_products.condition W (fin n)), }⟩

@[protected]
def preserves_products_of_shape (J : Type) [finite J] [W.contains_identities]
  [has_products_of_shape J C] (hW : W.stable_under_products_of_shape J) :
  preserves_limits_of_shape (discrete J) L :=
begin
  let G : C ⥤ _ := functor.const (discrete J),
  let F : ((discrete J) ⥤ C) ⥤ C := lim,
  let adj : G ⊣ F := const_lim_adj,
  let L' := (whiskering_right (discrete J) C D).obj L,
  let G' : D ⥤ _ := functor.const (discrete J),
  let W' := morphism_property.functor_category W (discrete J),
  have hF : W'.is_inverted_by (F ⋙ L),
  { intros X Y f hf,
    dsimp,
    exact localization.inverts L W (F.map f) (hW.lim_map f (λ j, hf (discrete.mk j))), },
  let F' := localization.lift (F ⋙ L) hF L',
  letI : lifting L W (G ⋙ L') G' := ⟨L.comp_const (discrete J)⟩,
  let adj' := adj.localization L W L' W' G' F',
  have h : ∀ (X : discrete J ⥤ C), adj.unit.app (F.obj X) ≫ F.map (adj.counit.app X) = 𝟙 (F.obj X),
  { intro X,
    exact adj.right_triangle_components, },
  haveI : ∀ (X : discrete J ⥤ C), is_iso ((limit_comparison_of_adj adj adj' L).app X),
  { intro X,
    dsimp only [limit_comparison_of_adj],
    simp only [adjunction.adjoint_nat_trans_equiv_app, adjunction.localization_unit_app, assoc,
      whiskering_right_obj_map, ← F'.map_comp, iso.inv_hom_id_app_assoc],
    erw [← nat_trans.naturality, ← assoc, ← L.map_comp],
    rw adj.right_triangle_components,
    apply_instance, },
  haveI : is_iso (limit_comparison_of_adj adj adj' L) := nat_iso.is_iso_of_is_iso_app _,
  exact preserves_limits_of_shape_of_adj adj adj' L,
end

instance localization_has_finite_products [W.contains_identities] [has_finite_products C]
  [W.stable_under_finite_products] : has_finite_products W.localization :=
  localization.has_finite_products W.Q W

instance [W.contains_identities] [has_finite_products C]
  [W.stable_under_finite_products] (J : Type) [finite J] :
  preserves_limits_of_shape (discrete J) W.Q :=
localization.preserves_products_of_shape W.Q W J
  (morphism_property.stable_under_finite_products.condition W J)

end localization

end category_theory
