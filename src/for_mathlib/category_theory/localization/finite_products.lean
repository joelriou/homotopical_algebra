import for_mathlib.category_theory.localization.products
import for_mathlib.category_theory.localization.adjunction
import for_mathlib.category_theory.finite_products

noncomputable theory

universes v v' u

namespace category_theory

open limits category

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]

lemma morphism_property.isomorphisms.is_inverted_by (F : C ⥤ D) :
  (morphism_property.isomorphisms C).is_inverted_by F := λ X Y f hf,
begin
  rw morphism_property.isomorphisms.iff at hf,
  haveI := hf,
  apply_instance,
end

def morphism_property.stable_under_binary_product (W : morphism_property C)
  [has_binary_products C] : Prop :=
  ∀ ⦃X₁ X₂ Y₁ Y₂ : C⦄ (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (hf₁ : W f₁) (hf₂ : W f₂),
    W (limits.prod.map f₁ f₂)

namespace localization

include L W

@[protected]
lemma has_terminal [has_terminal C] : has_terminal D :=
begin
  haveI := is_left_adjoint_const_of_has_terminal C unit.star,
  let G := (functor.const C).obj (discrete.mk unit.star),
  have hG : W.is_inverted_by G := λ X Y f hf, infer_instance,
  let F := right_adjoint G,
  let adj : G ⊣ F := is_left_adjoint.adj,
  let G' := (functor.const D).obj (discrete.mk unit.star),
  let F' := localization.lift F (morphism_property.isomorphisms.is_inverted_by F) (𝟭 _) ⋙ L,
  haveI : lifting L W (G ⋙ 𝟭 (discrete unit)) G' :=
    ⟨nat_iso.of_components (λ X, iso.refl _) (λ X Y f, subsingleton.elim _ _)⟩,
  haveI : is_left_adjoint G' :=
    ⟨_, adj.localization L W (𝟭 _) (morphism_property.isomorphisms _) G' F'⟩,
  exact (has_terminal_of_is_left_adjoint_const D) unit.star,
end

omit L

instance construction.has_terminal [has_terminal C] : has_terminal W.localization :=
localization.has_terminal W.Q W

include L

@[protected]
lemma has_binary_products [W.contains_identities] [has_binary_products C]
  (hW : W.stable_under_binary_product) : has_binary_products D :=
begin
  let G := functor.diag C,
  let F : C × C ⥤ C := uncurry.obj prod.functor,
  let adj : G ⊣ F := (is_left_adjoint_diag_of_has_binary_products C).adj,
  have hF : (W.prod W).is_inverted_by (F ⋙ L),
  { rintros ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩ ⟨hf₁, hf₂⟩,
    dsimp,
    simp only [limits.prod.map_map, comp_id, id_comp],
    exact localization.inverts L W _ (hW f₁ f₂ hf₁ hf₂), },
  let G' := functor.diag D,
  haveI : (L.prod L).is_localization (W.prod W) := prod_is_localization _ _ _ _,
  let F' := localization.lift (F ⋙ L) hF (L.prod L),
  haveI : lifting L W (G ⋙ L.prod L) G' := ⟨iso.refl _⟩,
  haveI : is_left_adjoint G' := ⟨_, adj.localization L W (L.prod L) (W.prod W) G' F'⟩,
  exact has_binary_products_of_is_left_adjoint_diag D,
end

lemma has_finite_products [W.contains_identities] [has_finite_products C]
  (hW : W.stable_under_binary_product) : has_finite_products D :=
begin
  haveI : has_terminal D := localization.has_terminal L W,
  haveI : has_binary_products D := localization.has_binary_products L W hW,
  exact has_finite_products_of_has_binary_products D,
end

end localization

end category_theory
