import category_theory.limits.concrete_category

noncomputable theory

universes v u w

open category_theory

namespace category_theory

namespace limits

variables {C : Type u} [category.{v} C] [concrete_category.{(max w v)} C]
  {J : Type w} (F : J → C) [has_coproduct F]

@[simp]
def concrete.coproduct_map :
  (Σ (j : J), (forget C).obj (F j)) → (forget C).obj (sigma_obj F) :=
λ a, (forget C).map (sigma.ι F a.1) a.2

lemma concrete.coproduct_map_bijective [preserves_colimit (discrete.functor F) (forget C)] :
  function.bijective (concrete.coproduct_map F) :=
begin
  sorry,
end

end limits

end category_theory
