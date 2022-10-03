import category_theory.limits.shapes.finite_products

noncomputable theory

namespace category_theory

open category

namespace limits

section

variables {J₁ J₂ C : Type*} [category C] (X : J₂ → C) [has_product X] (e : J₁ ≃ J₂)

def fan_of_equiv : fan (X ∘ e) := fan.mk (∏ X)
(λ j, pi.π _ (e j))

@[simp]
lemma fan_of_equiv_proj (j : J₁) : (fan_of_equiv X e).proj j = pi.π _ (e j) := rfl

lemma fan.congr_proj {J : Type*} {F : J → C} (s : fan F)
  {j₁ j₂ : J} (h : j₁ = j₂) : s.proj j₁ ≫ eq_to_hom (by rw h) = s.proj j₂ :=
by { subst h, rw [eq_to_hom_refl, comp_id], }

lemma cone.congr_π {J : Type*} [category J] {F : J ⥤ C} (s : cone F)
  {j₁ j₂ : J} (h : j₁ = j₂) : s.π.app j₁ ≫ eq_to_hom (by rw h) = (s.π.app j₂ : s.X ⟶ _) :=
by { subst h, rw [eq_to_hom_refl, comp_id], }

lemma is_limit_fan_of_equiv : is_limit (fan_of_equiv X e) :=
mk_fan_limit _ (λ s, pi.lift (λ j₂,s.proj (e.symm j₂) ≫ eq_to_hom (by simp)))
(λ s j, begin
  simp only [fan_of_equiv_proj, limit.lift_π, fan.mk_π_app],
  exact fan.congr_proj _ (by simp),
end)
(λ s m hm, begin
  ext j₂,
  discrete_cases,
  simp only [limit.lift_π, fan.mk_π_app, ← hm, assoc],
  congr' 1,
  dsimp,
  symmetry,
  have h : discrete.mk (e (e.symm j₂)) = discrete.mk j₂ := by simp,
  apply cone.congr_π _ h,
end)

lemma has_product_of_equiv : has_product (X ∘ e) :=
⟨nonempty.intro ⟨_, is_limit_fan_of_equiv X e⟩⟩

lemma product_iso_of_equiv [has_product (X ∘ e)] : ∏ (X ∘ e) ≅ ∏ X :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (is_limit_fan_of_equiv X e)

end

lemma product_iso_option {C J : Type*} [category C]
  (X : option J → C) [has_product X] [has_product (λ j, X (some j))]
  [has_binary_product (∏ (λ j, X (some j))) (X none)] :
  (∏ X) ≅ (∏ (λ j, X (some j))) ⨯ (X none) :=
{ hom := limits.prod.lift (pi.lift (λ j, pi.π _ (some j))) (pi.π _ none),
  inv := pi.lift (by { rintro (_|j), exacts [prod.snd, prod.fst ≫ pi.π _ j], } ),
  hom_inv_id' := begin
    ext,
    discrete_cases,
    rcases j with (_|j),
    { simp only [assoc, limit.lift_π, fan.mk_π_app, prod.lift_snd, id_comp], },
    { simp only [assoc, limit.lift_π, fan.mk_π_app, prod.lift_fst_assoc, id_comp], },
  end,
  inv_hom_id' := begin
    ext j,
    { discrete_cases,
      simp only [limit.lift_π, fan.mk_π_app, prod.lift_fst, assoc, id_comp], },
    { simp only [prod.comp_lift, limit.lift_π, fan.mk_π_app, prod.lift_snd, id_comp], },
  end, }

end limits

end category_theory
