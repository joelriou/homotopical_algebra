import for_mathlib.category_theory.localization.predicate

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace functor

lemma right_op_left_op_eq {C D : Type*} [category C] [category D] (F : Cᵒᵖ ⥤ D) :
  F.right_op.left_op = F := by { cases F, refl, }

end functor

namespace morphism_property

namespace is_inverted_by

lemma op {C D : Type*} [category C] [category D]
  {W : morphism_property C} {L : C ⥤ D} (h : W.is_inverted_by L) :
  W.op.is_inverted_by L.op := λ X Y f hf,
by { haveI := h f.unop hf, dsimp, apply_instance, }

lemma right_op {C D : Type*} [category C] [category D]
  {W : morphism_property C} {L : Cᵒᵖ ⥤ D} (h : W.op.is_inverted_by L):
  W.is_inverted_by L.right_op := λ X Y f hf,
by { haveI := h f.op hf, dsimp, apply_instance, }

end is_inverted_by

end morphism_property

variables {C D : Type*} [category C] [category D] {L : C ⥤ D}
  {W : morphism_property C}

namespace localization

def strict_universal_property_fixed_target.op {E : Type*} [category E]
  (h : strict_universal_property_fixed_target L W Eᵒᵖ):
  strict_universal_property_fixed_target L.op W.op E :=
{ inverts_W := h.inverts_W.op,
  lift := λ F hF, (h.lift F.right_op hF.right_op).left_op,
  fac := λ F hF, begin
    convert congr_arg functor.left_op (h.fac F.right_op hF.right_op),
    exact F.right_op_left_op_eq.symm,
  end,
  uniq := λ F₁ F₂ eq, begin
    suffices : F₁.right_op = F₂.right_op,
    { rw [← F₁.right_op_left_op_eq, ← F₂.right_op_left_op_eq, this], },
    have eq' := congr_arg functor.right_op eq,
    exact h.uniq _ _ eq',
  end, }

instance is_localization_op : W.Q.op.is_localization W.op :=
functor.is_localization.mk' W.Q.op W.op
  (strict_universal_property_fixed_target.for_Q W _).op
  (strict_universal_property_fixed_target.for_Q W _).op

end localization

namespace functor

variables (L W)

instance is_localization.op [h : L.is_localization W] : L.op.is_localization W.op :=
is_localization.of_equivalence W.Q.op W.op L.op (localization.equivalence_from_model L W).op
  (nat_iso.op (localization.Q_comp_equivalence_from_model_functor_iso L W).symm)

end functor

end category_theory
