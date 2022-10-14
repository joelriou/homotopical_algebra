import for_mathlib.category_theory.localization.equivalence

noncomputable theory

namespace category_theory

variables {C₁ C₂ C₃ E : Type*} [category C₁] [category C₂] [category C₃]

open localization

namespace morphism_property

@[refl]
lemma subset.refl (W : morphism_property C₁) : W ⊆ W := λ X Y f hf, hf

@[simp]
def map (W : morphism_property C₁) (F : C₁ ⥤ C₂) : morphism_property C₂ :=
λ X₂ Y₂ f₂, ∃ (X₁ Y₁ : C₁) (f₁ : X₁ ⟶ Y₁) (hf₁ : W f₁),
  nonempty (arrow.mk (F.map f₁) ≅ arrow.mk f₂)

lemma map_mem_map (W : morphism_property C₁) (F : C₁ ⥤ C₂) {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁)
  (hf₁ : W f₁) : W.map F (F.map f₁) :=
⟨_, _, f₁, hf₁, nonempty.intro (iso.refl _)⟩

lemma map_is_inverted_by_iff (W : morphism_property C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
  (W.map F).is_inverted_by G ↔ W.is_inverted_by (F ⋙ G) :=
begin
  split,
  { intros h X₁ Y₁ f₁ hf₁,
    exact h _ (W.map_mem_map F f₁ hf₁), },
  { rintros h X₂ Y₂ f₂ ⟨X₁, Y₁, f₁, hf₁, ⟨e⟩⟩,
    exact ((respects_iso.isomorphisms C₃).arrow_mk_iso_iff (G.map_arrow.map_iso e)).1 (h _ hf₁), },
end

end morphism_property


namespace localization

section

lemma strict_universal_property_fixed_target.comp {E : Type*} [category E]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {W₁ : morphism_property C₁} {W₂ : morphism_property C₂}
  (h₁ : strict_universal_property_fixed_target L₁ W₁ E)
  (h₂ : strict_universal_property_fixed_target L₂ W₂ E)
  (W₃ : morphism_property C₁) (hW₃ : W₃.is_inverted_by (L₁ ⋙ L₂))
  (hW₁₃ : W₁ ⊆ W₃) (hW₂₃ : W₂ ⊆ W₃.map L₁) :
  strict_universal_property_fixed_target (L₁ ⋙ L₂) W₃ E :=
{ inverts := hW₃,
  lift := λ F hF, begin
    have h : W₁.is_inverted_by F := λ X₁ Y₁ f₁ hf₁, hF f₁ (hW₁₃ _ hf₁),
    exact h₂.lift (h₁.lift F h) (λ X₂ Y₂ f₂ hf₂, begin
      obtain ⟨X₁, Y₁, f₁, hf₁, ⟨e⟩⟩ := hW₂₃ _ hf₂,
      refine ((morphism_property.respects_iso.isomorphisms E).arrow_mk_iso_iff
        ((h₁.lift F h).map_arrow.map_iso e)).1 _,
      refine ((morphism_property.respects_iso.isomorphisms E).arrow_mk_iso_iff
        (arrow.iso_of_nat_iso (eq_to_iso (h₁.fac F h)) (arrow.mk f₁))).2 (hF _ hf₁),
    end),
  end,
  fac := λ F hF, by rw [functor.assoc, h₂.fac, h₁.fac],
  uniq := λ F₁ F₂ h, begin
    simp only [functor.assoc] at h,
    exact h₂.uniq _ _ (h₁.uniq _ _ h),
  end, }

end

@[protected]
lemma comp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (W₁ : morphism_property C₁)
  (W₂ : morphism_property C₂) (W₃ : morphism_property C₁)
  [L₁.is_localization W₁] [L₂.is_localization W₂] (hW₃ : W₃.is_inverted_by (L₁ ⋙ L₂))
  (hW₁₃ : W₁ ⊆ W₃) (hW₃' : W₂ ⊆ W₃.map L₁) :
  (L₁ ⋙ L₂).is_localization W₃ :=
begin
  let L₁' := W₁.Q,
  let eq₂ := equivalence_from_model L₁ W₁,
  let W₂' : morphism_property (W₁.localization) := W₂.map eq₂.inverse,
  let L₂' := W₂'.Q,
  have h₂ : W₂'.is_inverted_by (eq₂.functor ⋙ L₂),
  { dsimp only [W₂'],
    rw morphism_property.map_is_inverted_by_iff,
    refine (morphism_property.is_inverted_by.iff_of_iso W₂ _).1 (localization.inverts L₂ W₂),
    exact L₂.left_unitor.symm ≪≫ iso_whisker_right eq₂.counit_iso.symm _ ≪≫ functor.associator _ _ _, },
  let F₃ : W₂'.localization ⥤ C₃ := localization.lift (eq₂.functor ⋙ L₂) h₂ L₂',
  let H : Comm_sq eq₂.functor L₂' L₂ F₃ := ⟨localization.fac _ _ _⟩,
  have h₁' : W₁.is_inverted_by L₁' := localization.inverts _ _,
  have h₁₂' : W₁.is_inverted_by (L₁' ⋙ L₂') :=
    morphism_property.is_inverted_by.of_comp W₁ _ h₁' L₂',
  let F₁₂' := localization.lift (L₁' ⋙ L₂') h₁₂' L₁,
  have hF₁₂' : W₂.is_inverted_by F₁₂' := sorry,
  let G₃ : C₃ ⥤ W₂'.localization := localization.lift F₁₂' hF₁₂' L₂,
  letI : lifting L₂ W₂ (eq₂.inverse ⋙ W₂'.Q) G₃,
  { constructor,
    refine localization.fac F₁₂' hF₁₂' L₂ ≪≫ _,
    letI : lifting L₁ W₁ (L₁' ⋙ L₂') (eq₂.inverse ⋙ W₂'.Q) := sorry,
    refine lift_nat_iso L₁ W₁ (L₁' ⋙ L₂') (L₁' ⋙ L₂') _ _ (iso.refl _), },
  let eq₃ := lifting_equivalence H W₂' W₂ (eq₂.inverse ⋙ W₂'.Q) G₃,
  all_goals { sorry, },
end

end localization

end category_theory
