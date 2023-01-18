import for_mathlib.category_theory.localization.derived_functor_functoriality
import for_mathlib.category_theory.functor.shift
import for_mathlib.category_theory.localization.triangulated

noncomputable theory

namespace category_theory

variables {C H D A : Type*} [category C] [category H] [category D] [add_group A]
  [has_shift C A] [has_shift H A] [has_shift D A]
  (F : C ⥤ D) [F.has_comm_shift A] (L : C ⥤ H) [L.has_comm_shift A]
  (W : morphism_property C) [L.is_localization W]
  [W.compatible_with_shift A]
  [F.has_right_derived_functor W] (a : A)

namespace functor

namespace has_comm_shift

--instance has_right_derived_functor (a : A) : (F ⋙ shift_functor D a).has_right_derived_functor W :=

@[simps]
def right_derived_α_shift (a : A) :
  F ⋙ shift_functor D a ⟶ L ⋙ F.right_derived_functor L W ⋙ shift_functor D a :=
whisker_right (F.right_derived_functor_α L W) _  ≫ (functor.associator _ _ _).hom

instance is_right_derived_functor_α_shift :
  (F.right_derived_functor L W ⋙ shift_functor D a).is_right_derived_functor
  (right_derived_α_shift F L W a) :=
by { dsimp only [right_derived_α_shift], apply_instance, }

--include L
--
--instance test : (shift_functor C a ⋙ F).has_right_derived_functor W :=
--begin
--  have paf := right_derived_α_shift F L W a,
--  have pif := (F.right_derived_functor L W ⋙ shift_functor D a).is_right_derived_functor (right_derived_α_shift F L W a),
--  sorry,
--end

end has_comm_shift

end functor

end category_theory
