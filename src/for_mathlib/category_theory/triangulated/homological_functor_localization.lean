import for_mathlib.category_theory.triangulated.homological_functor

namespace category_theory

open limits category pretriangulated
open_locale zero_object

lemma ess_surj.of_iso {C D : Type*} [category C] [category D] {F G : C ⥤ D}
  (e : F ≅ G) [ess_surj F] : ess_surj G :=
⟨λ Y,  ⟨_, ⟨e.symm.app _ ≪≫ F.obj_obj_preimage_iso Y⟩⟩⟩

namespace functor

instance preserves_zero_morphisms_comp {C D E : Type*} [category C] [category D] [category E]
  [has_zero_morphisms C] [has_zero_morphisms D] [has_zero_morphisms E]
  (F : C ⥤ D) (G : D ⥤ E) [F.preserves_zero_morphisms] [G.preserves_zero_morphisms] :
  (F ⋙ G).preserves_zero_morphisms := { }

lemma preserves_zero_morphisms.of_iso {C D : Type*} [category C] [category D] {F G : C ⥤ D}
  [has_zero_morphisms C] [has_zero_morphisms D]
  (e : F ≅ G) [F.preserves_zero_morphisms] : G.preserves_zero_morphisms :=
⟨λ X Y, by rw [← cancel_epi (e.hom.app X), ← e.hom.naturality, F.map_zero, comp_zero, zero_comp]⟩

namespace is_homological

section

variables {C D A : Type*} [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), (shift_functor C n).additive] [pretriangulated C]
  [category D] [has_zero_object D] [has_shift D ℤ]
  [preadditive D] [∀ (n : ℤ), (shift_functor D n).additive] [pretriangulated D]
  [category A] [abelian A]

variables (L : C ⥤ D) [L.has_comm_shift ℤ]
  (hL : ∀ (T : pretriangulated.triangle D) (hT : T ∈ dist_triang D),
    ∃ (T' : pretriangulated.triangle C) (hT' : T' ∈ dist_triang C),
      nonempty (T ≅ L.map_triangle.obj T'))

lemma localization_preserves_zero_morphisms_aux (F : D ⥤ A) [ess_surj L]
  [functor.preserves_zero_morphisms L]
  (hF : (L ⋙ F).preserves_zero_morphisms) : F.preserves_zero_morphisms :=
⟨λ X Y, begin
  simp only [← cancel_epi (F.map (L.obj_obj_preimage_iso X).hom),
    ← cancel_mono (F.map (L.obj_obj_preimage_iso Y).inv), ← F.map_comp,
    zero_comp, comp_zero, ← L.map_zero, ← functor.comp_map,
    (L ⋙ F).map_zero],
end⟩

include hL

lemma ess_surj_aux : ess_surj L :=
⟨λ Y, begin
  obtain ⟨T, hT, ⟨e⟩⟩ := hL (contractible_triangle Y) (contractible_distinguished Y),
  exact ⟨_, ⟨(triangle.eval₁ D).map_iso e.symm⟩⟩,
end⟩

lemma localization_aux (F : D ⥤ A) [F.preserves_zero_morphisms]
  [L.preserves_zero_morphisms] [L.is_triangulated] (hF : (L ⋙ F).is_homological) :
  F.is_homological :=
is_homological.mk' _ (λ T hT, begin
  obtain ⟨T', hT', ⟨e⟩⟩ := hL T hT,
  exact ⟨L.map_triangle.obj T', L.map_distinguished T' hT',
    e, hF.map_distinguished T' hT'⟩,
end)

end

section

variables {C D A : Type*} [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), (shift_functor C n).additive] [pretriangulated C]
  [category D] [preadditive D] [has_shift D ℤ] [has_zero_object D]
  [∀ (n : ℤ), (shift_functor D n).additive] (L : C ⥤ D)
  (W : morphism_property C) [L.is_localization W] [functor.additive L]
  [W.compatible_with_shift ℤ] [left_calculus_of_fractions W]
  [right_calculus_of_fractions W] [morphism_property.compatible_with_triangulation W]
  [L.has_comm_shift ℤ]
  [category A] [abelian A]

section

variables (G : C ⥤ A) (F : (localization L W) ⥤ A)
  [preserves_zero_morphisms G] [localization.lifting L W G F]

include L W

instance : ess_surj (localization_functor L W) :=
by convert localization.ess_surj L W

instance localization_functor_preserves_zero_morphisms :
  (localization_functor L W).preserves_zero_morphisms :=
(infer_instance : L.preserves_zero_morphisms)

lemma localization_preserves_zero_morphisms' [L.preserves_zero_morphisms] :
  F.preserves_zero_morphisms :=
localization_preserves_zero_morphisms_aux (localization_functor L W) F
  (preserves_zero_morphisms.of_iso (localization.lifting.iso L W G F).symm)

lemma localization' [F.preserves_zero_morphisms] [G.is_homological] :
  F.is_homological :=
begin
  refine localization_aux (localization_functor L W) _ F _,
  { intros T hT,
    obtain ⟨T', e, hT'⟩ := hT,
    exact ⟨T', hT', ⟨e⟩⟩, },
  { let e := (localization.lifting.iso L W G F),
    exact is_homological.of_iso e, },
end

end

section

variables (G : C ⥤ A) [preserves_zero_morphisms G]
  (F : W.localization ⥤ A) [localization.lifting W.Q W G F]
  [morphism_property.stable_under_finite_products W]

include G

lemma localization_preserves_zero_morphisms : F.preserves_zero_morphisms :=
@localization_preserves_zero_morphisms' C W.localization A
    _ _ _ _ _ _ _ _ _ _ _ W.Q W _ _ _ _ _ _ _ _ _ G F _ _ _

lemma localization [F.preserves_zero_morphisms] [G.is_homological] :
  F.is_homological :=
localization' W.Q W G F

instance localization_lift_preserves_zero_morphisms [G.is_homological] (hG : W.is_inverted_by G) :
  (localization.lift G hG W.Q).preserves_zero_morphisms :=
localization_preserves_zero_morphisms W G _

instance localization_lift_is_homological [G.is_homological] (hG : W.is_inverted_by G) :
  (localization.lift G hG W.Q).is_homological :=
localization W G _

end

end

end is_homological

end functor

end category_theory
