import for_mathlib.algebra.homology.derivability_structure_injective

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C D : Type*} [category C] [category D] [abelian C] [abelian D]
  (F : C ⥤ D) [functor.additive F]

namespace functor

instance map_is_strictly_ge (X : cochain_complex C ℤ) (n : ℤ) [X.is_strictly_ge n] :
  cochain_complex.is_strictly_ge ((F.map_homological_complex _ ).obj X) n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero D)
  (F.map_iso (cochain_complex.is_strictly_ge.is_zero X n i hi).iso_zero ≪≫ F.map_zero_object)⟩

lemma _root_.cochain_complex.is_plus.map {X : cochain_complex C ℤ} (h : X.is_plus)
  (F : C ⥤ D) [functor.additive F] :
  cochain_complex.is_plus ((map_homological_complex F (complex_shape.up ℤ)).obj X) :=
begin
  obtain ⟨n, hn⟩ := h,
  haveI := hn,
  exact ⟨n, infer_instance⟩,
end

def map_homotopy_category_plus : homotopy_category.plus C ⥤ homotopy_category.plus D :=
full_subcategory.lift _ (homotopy_category.plus.ι ⋙ functor.map_homotopy_category _ F)
  (λ K, cochain_complex.is_plus.map K.2 F)

instance map_homotopy_category_has_comm_shift :
  (functor.map_homotopy_category_plus F).has_comm_shift ℤ :=
begin
  dsimp only [map_homotopy_category_plus],
  haveI : (functor.map_homotopy_category (complex_shape.up ℤ) F).has_comm_shift ℤ := sorry,
  apply_instance,
end

instance map_homotopy_category_is_triangulated :
  (functor.map_homotopy_category_plus F).is_triangulated := sorry

variable [(functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh).has_right_derived_functor
    (triangulated.subcategory.W (homotopy_category.plus.acyclic C))]

abbreviation right_derived_functor_plus : derived_category.plus C ⥤ derived_category.plus D :=
  (functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh).right_derived_functor derived_category.plus.Qh
      (triangulated.subcategory.W (homotopy_category.plus.acyclic C))

def right_derived_functor_plus_αh :
  functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh ⟶ derived_category.plus.Qh ⋙
      right_derived_functor_plus F :=
functor.right_derived_functor_α _ _ _


--lemma test : F.right_derived_functor_plus.has_comm_shift ℤ := infer_instance
--lemma test : F.right_derived_functor_plus.is_triangulated := infer_instance

instance (X : homotopy_category.plus C) [X.obj.as.is_termwise_injective]
  [enough_injectives C] :
  is_iso ((right_derived_functor_plus_αh F).app X) :=
begin
  dsimp only [right_derived_functor_plus_αh],
  apply_instance,
end

include F

def abelian_right_derived_functor (n : ℕ) : C ⥤ D :=
derived_category.plus.single_functor C 0 ⋙ right_derived_functor_plus F ⋙
  derived_category.plus.homology_functor D (n : ℤ)

-- TODO:
-- * show that total_right_derived_functor is a triangulated functor
-- * deduce the long exact sequence attached to a short exact sequence in C
-- * define the natural transformation F ⟶ R^0 F, and show that when F is
--      left exact, it is an isomorphism using an injective resolution

end functor

end category_theory
