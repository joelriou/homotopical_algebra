import for_mathlib.category_theory.localization.triangulated

open_locale zero_object

namespace set

open category_theory

class respects_iso {X : Type*} [category X] (A : set X) : Prop :=
(condition : ∀ ⦃x y : X⦄ (e : x ≅ y) (hx : x ∈ A), y ∈ A)

end set

namespace category_theory

open limits

namespace triangulated

variables (C : Type*) [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), functor.additive (shift_functor C n)]
  [pretriangulated C]


structure subcategory :=
(set : set C)
(zero : (0 : C) ∈ set)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ set), (shift_functor C n).obj X ∈ set)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ set) (h₃ : T.obj₃ ∈ set), T.obj₂ ∈ set)

lemma subcategory.respects_iso (A : subcategory C) :
  A.set.respects_iso :=
⟨λ X Y e hX, A.ext₂ _ (pretriangulated.isomorphic_distinguished _
  (pretriangulated.contractible_distinguished X) (triangle.mk C e.hom (0 : Y ⟶ 0) 0)
  (triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy))) hX A.zero⟩

def subcategory.W (A : subcategory C) : morphism_property C :=
λ X Y f, ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor C (1 : ℤ)).obj X)
  (H : triangle.mk C f g h ∈ dist_triang C), Z ∈ A.set

end triangulated

end category_theory
