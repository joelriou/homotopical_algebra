import category_theory.shift
import for_mathlib.category_theory.quotient_misc

noncomputable theory

namespace category_theory

open category

variables {C D E : Type*} {A : Type*} [category C] [category D] [category E]
  [add_monoid A] [has_shift C A] [has_shift D A] [has_shift E A]

variable (C)

def shift_functor_add' (a b c : A) (h : c = a + b) :
  shift_functor C c ≅ shift_functor C a ⋙ shift_functor C b :=
eq_to_iso (by rw h) ≪≫ shift_functor_add C a b

namespace functor

variable {C}

def comm_shift_comp {F : C ⥤ D} {G : D ⥤ E} {a : A}
  (hF : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (hG : shift_functor D a ⋙ G ≅ G ⋙ shift_functor E a) :
  shift_functor C a ⋙ (F ⋙ G) ≅ (F ⋙ G) ⋙ shift_functor E a :=
(functor.associator _ _ _).symm ≪≫
  iso_whisker_right hF G ≪≫
  functor.associator _ _ _ ≪≫
  iso_whisker_left F hG ≪≫ (functor.associator _ _ _).symm

end functor

end category_theory
