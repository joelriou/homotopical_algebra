import for_mathlib.category_theory.localization.products
import for_mathlib.category_theory.localization.adjunction
import for_mathlib.category_theory.finite_products

noncomputable theory

universes v v' u

namespace category_theory

open limits category

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]

namespace morphism_property

lemma isomorphisms.is_inverted_by (F : C ⥤ D) :
  (morphism_property.isomorphisms C).is_inverted_by F := λ X Y f hf,
begin
  rw morphism_property.isomorphisms.iff at hf,
  haveI := hf,
  apply_instance,
end

def stable_under_products_of_shape (W : morphism_property C) (J : Type*) : Prop :=
(∀ (X₁ X₂ : J → C) (c₁ : fan X₁) (c₂ : fan X₂) (h₁ : is_limit c₁) (h₂ : is_limit c₂)
  (f : Π j, X₁ j ⟶ X₂ j) (hf : ∀ j, W (f j)), W (h₂.lift (fan.mk c₁.X (λ j, c₁.proj j ≫ f j))))

def stable_under_finite_products (W : morphism_property C) : Prop :=
∀ (J : Type) [fintype J], stable_under_products_of_shape W J

abbreviation stable_under_binary_products (W : morphism_property C) :=
  W.stable_under_products_of_shape walking_pair

namespace stable_under_binary_product

lemma prod_map (h : W.stable_under_binary_products) ⦃X₁ X₂ Y₁ Y₂ : C⦄
  [has_binary_product X₁ X₂] [has_binary_product Y₁ Y₂]
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (hf₁ : W f₁) (hf₂ : W f₂) : W (limits.prod.map f₁ f₂) :=
begin
  convert h (pair_function X₁ X₂) (pair_function Y₁ Y₂) _ _ (prod_is_prod X₁ X₂)
    (prod_is_prod Y₁ Y₂) (by { rintro (_|_), exacts [f₁, f₂], })
      (by { rintro (_|_), exacts [hf₁, hf₂], }),
  apply binary_fan.is_limit.hom_ext (prod_is_prod Y₁ Y₂),
  { dsimp [prod_is_prod, iso.refl],
    simp only [limits.prod.map_fst, assoc],
    erw [id_comp, is_limit.fac],
    refl, },
  { dsimp [prod_is_prod, iso.refl],
    simp only [limits.prod.map_snd, assoc],
    erw [id_comp, is_limit.fac],
    refl, },
end

end stable_under_binary_product

namespace stable_under_products_of_shape

variable {W}

lemma pi_map {J : Type*} (h : W.stable_under_products_of_shape J) {X Y : J → C}
  (f : Π j, X j ⟶ Y j) [has_products_of_shape J C]
  (hf : ∀ j, W (f j)) : W (pi.map f) :=
begin
  convert h X Y _ _ (limit.is_limit _) (limit.is_limit _) f hf,
  ext j,
  cases j,
  simpa only [lim_map_π, limit.is_limit_lift, limit.lift_π],
end

end stable_under_products_of_shape

end morphism_property

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

lemma has_products_of_shape (J : Type) [fintype J] [W.contains_identities]
  [has_products_of_shape J C] (hW : W.stable_under_products_of_shape J) :
  has_products_of_shape J D :=
begin
  let G := functor.pi.diag C J,
  let F := (pi_equivalence_functors_from_discrete C J).functor ⋙ lim,
  let adj : G ⊣ F := (is_left_adjoint_of_has_limits_of_shape_discrete C J).adj,
  let W' : morphism_property (Π (j : J), C) := morphism_property.pi (λ j, W),
  have hF : W'.is_inverted_by (F ⋙ L),
  { intros X Y f hf,
    dsimp,
    suffices : is_iso (L.map (pi.map f)),
    { convert this,
      ext j,
      cases j,
      refl, },
    exact localization.inverts L W _ (hW.pi_map f hf), },
  let L' := functor.pi_ (λ (j : J), L),
  let G' := functor.pi.diag D J,
  let F' := localization.lift (F ⋙ L) hF L',
  haveI : lifting L W (G ⋙ L') G' := ⟨iso.refl _⟩,
  haveI : is_left_adjoint G' := ⟨_, adj.localization L W L' W' G' F'⟩,
  exact has_limits_of_shape_discrete_of_is_left_adjoint_diag D J,
end

lemma has_finite_products [W.contains_identities] [has_finite_products C]
  (hW : ∀ (J : Type) [fintype J], W.stable_under_products_of_shape J) :
  has_finite_products D :=
⟨λ J, by { introI, exact has_products_of_shape L W J (hW J), }⟩

end localization

end category_theory
