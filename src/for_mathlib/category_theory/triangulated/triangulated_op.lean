import for_mathlib.category_theory.shift_op
import for_mathlib.category_theory.triangulated.triangulated

open category_theory category_theory.limits category_theory.category

namespace category_theory

variables {C : Type*} [category C] [has_zero_object C] [preadditive C]
  [has_shift C ℤ] [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

namespace pretriangulated

end pretriangulated

end category_theory
