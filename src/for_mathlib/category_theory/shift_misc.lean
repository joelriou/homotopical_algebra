import category_theory.shift
import for_mathlib.category_theory.quotient_misc

noncomputable theory

namespace category_theory

open category

variables (C : Type*) {A : Type*} [category C] [add_monoid A] [has_shift C A]

def shift_functor_add' (a b c : A) (h : c = a + b) :
  shift_functor C c ≅ shift_functor C a ⋙ shift_functor C b :=
eq_to_iso (by rw h) ≪≫ shift_functor_add C a b

end category_theory
