import category_theory.quotient

namespace category_theory

namespace quotient

variables {C : Type*} [category C] (r : hom_rel C)

lemma functor_map_surjective (X Y : C) :
  function.surjective (λ (f : X ⟶ Y), (functor r).map f) := surjective_quot_mk _

end quotient

end category_theory
