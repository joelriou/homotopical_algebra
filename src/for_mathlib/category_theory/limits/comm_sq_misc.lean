import category_theory.limits.shapes.comm_sq

open category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

namespace is_pushout

variables {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

lemma of_horiz_is_iso [is_iso f] [is_iso inr] (sq : comm_sq f g inl inr) :
  is_pushout f g inl inr := of_is_colimit' sq
begin
  refine pushout_cocone.is_colimit.mk _ (λ s, inv inr ≫ s.inr) (λ s, _) (by tidy) (by tidy),
  simp only [← cancel_epi f, s.condition, sq.w_assoc, is_iso.hom_inv_id_assoc],
end

lemma of_vert_is_iso [is_iso g] [is_iso inl] (sq : comm_sq f g inl inr) :
  is_pushout f g inl inr := (of_horiz_is_iso sq.flip).flip

end is_pushout

end category_theory
