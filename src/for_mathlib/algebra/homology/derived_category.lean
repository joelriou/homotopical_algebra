import for_mathlib.algebra.homology.triangulated
import for_mathlib.category_theory.triangulated.homological_functor

open category_theory category_theory.category

variables {C : Type*} [category C] [abelian C]

namespace homotopy_category

/- should be generalised -/
instance homology_functor_additive :
  (homology_functor C (complex_shape.up ℤ) 0).additive := sorry

instance homology_functor_is_homological :
  (homology_functor C (complex_shape.up ℤ) 0).is_homological := sorry

end homotopy_category
