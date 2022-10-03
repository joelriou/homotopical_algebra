import category_theory.limits.shapes.finite_products

noncomputable theory

namespace category_theory

open category

namespace limits

section

variables {J₁ J₂ C : Type*} [category C] (X : J₂ → C) [has_product X] (e : J₁ ≃ J₂)

@[simps]
def fan_of_equiv : fan (X ∘ e) := fan.mk (∏ X)
(λ j, pi.π _ (e j))

lemma cone.congr_π {J : Type*} [category J] {F : J ⥤ C} (s : cone F)
  {j₁ j₂ : J} (h : j₁ = j₂) : s.π.app j₁ ≫ eq_to_hom (by rw h) = (s.π.app j₂ : s.X ⟶ _) :=
by { subst h, rw [eq_to_hom_refl, comp_id], }


lemma is_limit_fan_of_equiv : is_limit (fan_of_equiv X e) :=
{ lift := λ s, pi.lift (λ j, s.π.app (discrete.mk (e.symm j)) ≫ eq_to_hom begin
    dsimp,
    simp only [equiv.apply_symm_apply],
  end),
  fac' := λ s j, begin
    discrete_cases,
    simp only [fan_of_equiv_π_app, limit.lift_π, fan.mk_π_app],
    apply cone.congr_π,
    simp only [equiv.symm_apply_apply],
  end,
  uniq' := λ s m hm, begin
    ext j₂,
    discrete_cases,
    have h : ∃ j₁, j₂ = e j₁ := ⟨e.symm j₂, (e.apply_symm_apply j₂).symm⟩,
    rcases h with ⟨j₁, hj₁⟩,
    subst hj₁,
    have eq := hm (discrete.mk j₁),
    erw eq,
    simp only [limit.lift_π, fan.mk_π_app],
    symmetry,
    have h : discrete.mk (e.symm (e j₁)) = discrete.mk j₁ := by rw equiv.symm_apply_apply,
    exact cone.congr_π s h,
  end, }

lemma has_product_of_equiv : has_product (X ∘ e) :=
⟨nonempty.intro ⟨_, is_limit_fan_of_equiv X e⟩⟩

lemma product_iso_of_equiv [has_product (X ∘ e)] : ∏ (X ∘ e) ≅ ∏ X :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (is_limit_fan_of_equiv X e)

end

lemma product_iso_option {C J : Type*} [category C]
  (X : option J → C) [has_product X] [has_product (λ j, X (some j))]
  [has_binary_product (∏ (λ j, X (some j))) (X none)] :
  (∏ X) ≅ (∏ (λ j, X (some j))) ⨯ (X none) :=
sorry

end limits

end category_theory
