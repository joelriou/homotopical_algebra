import for_mathlib.algebra.homology.k_injective

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace abelian

variables {C D : Type*} [category C] [category D] [abelian C] [abelian D]
  (F : C ⥤ D) [functor.additive F]
  [(functor.map_homotopy_category (complex_shape.up ℤ) F ⋙
    derived_category.Qh.to_functor).has_right_derived_functor (homotopy_category.acyclic C).W]

def total_right_derived_functor : derived_category C ⥤ derived_category D :=
  (functor.map_homotopy_category (complex_shape.up ℤ) F ⋙
    derived_category.Qh.to_functor).right_derived_functor derived_category.Qh.to_functor
      (homotopy_category.acyclic C).W

def total_right_derived_functor_αh :
  functor.map_homotopy_category (complex_shape.up ℤ) F ⋙
    derived_category.Qh.to_functor ⟶ derived_category.Qh.to_functor ⋙
      total_right_derived_functor F :=
functor.right_derived_functor_α _ _ _

-- the following needs a compatibility isomorphism between functor.map_homological_complex
--   and functor.map_homotopy_category
--lemma right_derived_functor_α :
--  F.map_homological_complex (complex_shape.up ℤ) ⋙
--    derived_category.Q ⟶ derived_category.Q ⋙ right_derived_functor F :=
-- sorry

instance (X : homotopy_category C (complex_shape.up ℤ)) [X.is_K_injective]
  [has_enough_K_injectives C] :
  is_iso ((total_right_derived_functor_αh F).app X) :=
begin
  dsimp only [total_right_derived_functor_αh],
  apply_instance,
end

include F

def right_derived_functor (n : ℕ) : C ⥤ D :=
derived_category.single_functor C 0 ⋙ total_right_derived_functor F ⋙
  derived_category.homology_functor D (n : ℤ)

-- TODO:
-- * show that total_right_derived_functor is a triangulated functor
-- * deduce the long exact sequence attached to a short exact sequence in C
-- * define the natural transformation F ⟶ R^0 F, and show that when F is
--      left exact, it is an isomorphism using an injective resolution

end abelian

end category_theory
