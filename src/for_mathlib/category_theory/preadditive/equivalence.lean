import category_theory.preadditive.additive_functor
import category_theory.adjunction.limits
import for_mathlib.category_theory.group_object

namespace category_theory

namespace preadditive

open limits

instance additive_of_binary_products {C D : Type*} [category C] [category D] [preadditive C] [preadditive D]
  (F : C ⥤ D) [is_equivalence F] [has_finite_products C] [has_finite_products D] : F.additive :=
F.additive_of_preserves_binary_products

end preadditive

end category_theory
