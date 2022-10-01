import category_theory.preadditive.additive_functor
import for_mathlib.category_theory.localization.finite_products
import for_mathlib.category_theory.group_object

noncomputable theory

namespace category_theory

open limits

namespace localization

variables {C D : Type*} [category C] [category D] [preadditive C]
  (L : C ⥤ D) (W : morphism_property C)

variables [morphism_property.contains_identities W]
  [hW : W.stable_under_finite_products]
  [hL : L.is_localization W] [limits.has_finite_products C]


include hL hW

@[protected]
lemma preadditive : preadditive D :=
begin
  haveI : has_finite_products D := localization.has_finite_products L W,
  haveI : ∀ (J : Type) [fintype J], preserves_limits_of_shape (discrete J) L :=
    by { intro J, introI, exact localization.preserves_products_of_shape L W J
      (hW.condition J), },
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

lemma additive [preadditive D] : functor.additive L :=
begin
  haveI : has_finite_products D := localization.has_finite_products L W,
  haveI : ∀ (J : Type) [fintype J], preserves_limits_of_shape (discrete J) L :=
    by { intro J, introI, exact localization.preserves_products_of_shape L W J (hW.condition J), },
  exact functor.additive_of_preserves_binary_products L,
end

omit hL

instance : preadditive W.localization := localization.preadditive W.Q W

instance : functor.additive W.Q := localization.additive W.Q W

instance : has_zero_object W.localization :=
⟨⟨terminal _, begin
  split,
  { intro Y,
    refine nonempty.intro ⟨⟨0⟩, λ a, _⟩,
    have eq : 𝟙 (terminal W.localization) = 0 := subsingleton.elim _ _,
    rw [← category.id_comp a, ← category.id_comp default, eq, zero_comp, zero_comp], },
  { exact λ Y, nonempty.intro ⟨⟨0⟩, λ a, subsingleton.elim _ _⟩, },
end⟩⟩

end localization

end category_theory
