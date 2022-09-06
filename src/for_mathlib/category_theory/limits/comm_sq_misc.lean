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

lemma of_coprod_inl_with_id {A B : C} (f : A ⟶ B) (X : C) [has_binary_coproduct A X]
  [has_binary_coproduct B X] :
  is_pushout coprod.inl f (coprod.map f (𝟙 X)) coprod.inl :=
is_pushout.of_is_colimit' (comm_sq.mk (coprod.inl_map _ _))
(pushout_cocone.is_colimit_aux _ (λ s, coprod.desc s.inr (coprod.inr ≫ s.inl))
(λ s, begin
  dsimp [comm_sq.cocone],
  ext,
  { simp only [coprod.map_desc, coprod.inl_desc, s.condition], },
  { simp only [coprod.map_desc, category.id_comp, coprod.inr_desc], },
end)
(λ s, by { dsimp [comm_sq.cocone], simp only [coprod.inl_desc], })
(λ s m hm, begin
  dsimp [comm_sq.cocone],
  ext,
  { simpa only [coprod.inl_desc] using hm walking_span.right, },
  { have h := coprod.inr ≫= hm walking_span.left,
    dsimp [comm_sq.cocone] at h,
    simpa only [coprod.inr_desc, coprod.inr_map_assoc, category.id_comp] using h, },
end))

end is_pushout

end category_theory
