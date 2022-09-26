import category_theory.preadditive.additive_functor
import for_mathlib.category_theory.localization.finite_products
import for_mathlib.category_theory.group_object

noncomputable theory

namespace category_theory

open limits

namespace localization

variables {C D : Type*} [category C] [category D] [preadditive C]
  (L : C ⥤ D) (W : morphism_property C) [morphism_property.contains_identities W]
  (hW : Π (J : Type) [finite J], W.stable_under_products_of_shape J)
  [hL : L.is_localization W]

include hL hW

@[protected]
lemma preadditive [limits.has_finite_products C] : preadditive D :=
begin
  haveI : has_finite_products D := localization.has_finite_products L W hW,
  haveI : ∀ (J : Type) [fintype J], preserves_limits_of_shape (discrete J) L :=
    by { intro J, introI, exact localization.preserves_products_of_shape L W J (hW J), },
  let F := preadditive.to_add_comm_group_object C ⋙ L.map_add_comm_group_object,
  have hF : W.is_inverted_by F := λ X Y f hf, begin
    haveI : is_iso ((add_comm_group_object.forget D).map (F.map f)),
    { change is_iso (L.map f),
      exact localization.inverts L W f hf, },
    exact is_iso_of_reflects_iso (F.map f) (add_comm_group_object.forget D),
  end,
  refine add_comm_group_object.preadditive_of (localization.lift F hF L) _,
  haveI : lifting L W (F ⋙ add_comm_group_object.forget D) (𝟭 D) := ⟨iso.refl _⟩,
  exact lifting.uniq L W (F ⋙ add_comm_group_object.forget D)
    (lift F hF L ⋙ add_comm_group_object.forget D) (𝟭 D),
end

lemma additive [preadditive D] [limits.has_finite_products C] : functor.additive L :=
begin
  haveI : has_finite_products D := localization.has_finite_products L W hW,
  haveI : ∀ (J : Type) [fintype J], preserves_limits_of_shape (discrete J) L :=
    by { intro J, introI, exact localization.preserves_products_of_shape L W J (hW J), },
  exact functor.additive_of_preserves_binary_products L,
end

end localization

end category_theory
