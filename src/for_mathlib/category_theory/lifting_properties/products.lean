import category_theory.lifting_properties.basic
import for_mathlib.category_theory.morphism_property_misc

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

namespace has_lifting_property

instance stable_by_coproducts {J : Type*} {A : J → C} {B : J → C} [has_coproduct A]
  [has_coproduct B] (i : Π (j : J), A j ⟶ B j)
  {X Y : C} (p : X ⟶ Y) [hip : ∀ (j : J), has_lifting_property (i j) p] :
    has_lifting_property (limits.sigma.map i) p :=
⟨λ f g sq, begin
  have fac : ∀ (j : J), (sigma.ι A j ≫ f) ≫ p = i j ≫ (sigma.ι B j ≫ g),
  { intro j,
    simp only [sq.w, assoc, ι_colim_map_assoc, discrete.nat_trans_app], },
  exact comm_sq.has_lift.mk'
  { l := sigma.desc (λ j, (comm_sq.mk (fac j)).lift),
    fac_left' := begin
      ext,
      discrete_cases,
      simp only [ι_colim_map_assoc, colimit.ι_desc, cofan.mk_ι_app, comm_sq.fac_left],
    end,
    fac_right' := begin
      ext,
      discrete_cases,
      simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, comm_sq.fac_right],
    end, },
end⟩

instance stable_by_products {J : Type*} {X : J → C} {Y : J → C} [has_product X]
  [has_product Y] (p : Π (j : J), X j ⟶ Y j)
  {A B : C} (i : A ⟶ B) [hip : ∀ (j : J), has_lifting_property i (p j)] :
  has_lifting_property i (limits.pi.map p) :=
⟨λ f g sq, begin
  have fac : ∀ (j : J), (f ≫ pi.π _ j) ≫ p j = i ≫ (g ≫ pi.π _ j),
  { intro j,
    simp only [← sq.w_assoc, assoc, lim_map_π, discrete.nat_trans_app], },
  exact comm_sq.has_lift.mk'
  { l := pi.lift (λ j, (comm_sq.mk (fac j)).lift),
    fac_left' := begin
      ext,
      discrete_cases,
      simp only [assoc, limit.lift_π, fan.mk_π_app, comm_sq.fac_left],
    end,
    fac_right' := begin
      ext,
      discrete_cases,
      simp only [limit.lift_map, limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app,
        fan.mk_π_app, discrete.nat_trans_app, comm_sq.fac_right],
    end, },
end,⟩

end has_lifting_property

end category_theory
