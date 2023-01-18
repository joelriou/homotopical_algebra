import for_mathlib.category_theory.localization.derived_functor

namespace category_theory

namespace functor

namespace is_right_derived_functor

variables {C D D' H : Type*} [category C] [category D] [category D'] [category H]
  {F : C ⥤ D} (RF : H ⥤ D) {L : C ⥤ H} (α : F ⟶ L ⋙ RF)
  (e : D ≌ D')

lemma of_equivalence_comp_right [RF.is_right_derived_functor α]
  (β : F ⋙ e.functor ⟶ L ⋙ RF ⋙ e.functor)
  (hβ : β = whisker_right α e.functor ≫ (functor.associator _ _ _).hom) :
  (RF ⋙ e.functor).is_right_derived_functor β :=
begin
  let C₁ := structured_arrow F ((whiskering_left C H D).obj L),
  let C₂ := structured_arrow (F ⋙ e.functor) ((whiskering_left C H D').obj L),
  sorry,
end


end is_right_derived_functor

end functor

end category_theory
