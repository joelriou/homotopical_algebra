import category_theory.functor.basic
import category_theory.eq_to_hom

namespace category_theory

open category

namespace functor

lemma congr_map_conjugate {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (h : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
  F₁.map f = eq_to_hom (by rw h) ≫ F₂.map f ≫ eq_to_hom (by rw h) :=
begin
  subst h,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

end functor

end category_theory
