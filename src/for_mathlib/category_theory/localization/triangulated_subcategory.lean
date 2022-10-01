import for_mathlib.category_theory.localization.triangulated

noncomputable theory

open_locale zero_object

namespace set

open category_theory

class respects_iso {X : Type*} [category X] (A : set X) : Prop :=
(condition : ∀ ⦃x y : X⦄ (e : x ≅ y) (hx : x ∈ A), y ∈ A)

end set

namespace category_theory

open limits

namespace triangulated

open pretriangulated

variables (C : Type*) [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), functor.additive (shift_functor C n)]
  [pretriangulated C]

structure subcategory :=
(set : set C)
(zero : (0 : C) ∈ set)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ set), (shift_functor C n).obj X ∈ set)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ set) (h₃ : T.obj₃ ∈ set), T.obj₂ ∈ set)

variable {C}

namespace subcategory

variable (A : subcategory C)
lemma respects_iso : A.set.respects_iso :=
⟨λ X Y e hX, A.ext₂ _ (pretriangulated.isomorphic_distinguished _
  (pretriangulated.contractible_distinguished X) (triangle.mk C e.hom (0 : Y ⟶ 0) 0)
  (triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy))) hX A.zero⟩

lemma ext₁
  (T : triangle C) (hT : T ∈ dist_triang C) (h₂ : T.obj₂ ∈ A.set) (h₃ : T.obj₃ ∈ A.set) :
  T.obj₁ ∈ A.set :=
A.ext₂ T.inv_rotate (pretriangulated.inv_rot_of_dist_triangle C T hT) (A.shift _ (-1 : ℤ) h₃) h₂

lemma ext₃
  (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ A.set) (h₂ : T.obj₂ ∈ A.set) :
  T.obj₃ ∈ A.set :=
A.ext₂ T.rotate (pretriangulated.rot_of_dist_triangle C T hT) h₂ (A.shift _ (1 : ℤ) h₁)

def W : morphism_property C :=
λ X Y f, ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor C (1 : ℤ)).obj X)
  (H : triangle.mk C f g h ∈ dist_triang C), Z ∈ A.set

variable {A}
instance : left_calculus_of_fractions (W A) := sorry
instance : right_calculus_of_fractions (W A) := sorry
instance W_compatible_with_shift : (W A).compatible_with_shift ℤ := sorry
instance W_stable_under_finite_products : (W A).stable_under_finite_products := sorry
instance W_compatible_with_triangulation : (W A).compatible_with_triangulation := sorry
instance W_is_saturated : (W A).is_saturated := sorry

lemma test [has_finite_products C] : pretriangulated (W A).localization := infer_instance

end subcategory

end triangulated

end category_theory
