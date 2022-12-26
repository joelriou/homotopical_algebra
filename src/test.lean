import for_mathlib.category_theory.abelian.extension_example

noncomputable theory

open category_theory category_theory.pretriangulated category_theory.abelian

variables {C : Type*} [category C] [abelian C]

/-- The derived category `derived_category C` of an abelian category `C`
is a triangulated category. -/
example : is_triangulated (derived_category C) := infer_instance

/-- There is a triangulated functor from the homotopy category to the
derived category. -/
example : triangulated_functor (homotopy_category C (complex_shape.up ℤ))
  (derived_category C) := derived_category.Qh

/-- The derived category on an abelian category is the localization of the
homotopy category of cochain complexes indexed by `ℤ` with respect to a
certain class of morphisms `(homotopy_category.acyclic C).W`.
By definition, `homotopy_category.acyclic C` is the subtriangulated category
of the homotopy category consisting of acyclic complexes (i.e. with zero homology).
The class `(homotopy_category.acyclic C).W` is then the class of morphisms whose
"cone" is acyclic.  -/
example : functor.is_localization derived_category.Qh.to_functor
  (homotopy_category.acyclic C).W := infer_instance

/-- The canonical functor `derived_category.Q : cochain_complex C ℤ ⥤ derived_category C`
is the composition of two functors :
`homotopy_category.quotient _ _ : cochain_complex C ℤ ⟶ homotopy_category C (complex_shape.up ℤ)`
and `Qh.to_functor`. -/
example : cochain_complex C ℤ ⥤ derived_category C := derived_category.Q

/-- The derived category was defined here in two steps from `cochain_complex C ℤ`
(passing to the quotient by the homotopy relation, and then localizing). In this
way, we could get the triangulated structure. We also obtain that the
derived category is the localization of `cochain_complex C ℤ` with
respect to quasi-isomorphisms, which are morphisms inducing isomorphisms
in homology. -/
example : functor.is_localization derived_category.Q (quasi_isomorphisms C _) := infer_instance

namespace derived_category

/- For any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `cochain_complex C ℤ`, there is
an associated distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in the derived category. -/
example {X₁ X₂ X₃ : cochain_complex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0)
  (ex : (short_complex.mk f g w).short_exact) :
  triangle.mk (Q.map f) (Q.map g) (triangle_of_ses_δ ex) ∈ dist_triang (derived_category C) :=
derived_category.triangle_of_ses_dist ex

/-- The homology functors on `cochain_complex C ℤ` induce functors
`homology_functor C n : derived_category C ⥤ C`, and these functors
are homological. -/
example (n : ℤ) : (homology_functor C n).is_homological := infer_instance

/-- That these functors are homological implies that any distinguished triangle
`obj₁ ⟶ obj₂ ⟶ obj₃ ⟶ obj₁⟦1⟧` induces an exact sequence
H⁰ obj₁ ⟶ H⁰ obj₂ ⟶ H⁰ obj₃`. -/
example (T : triangle (derived_category C)) (hT : T ∈ dist_triang (derived_category C)) :
  ((short_complex.mk T.mor₁ T.mor₂ (comp_dist_triangle_mor_zero₁₂ _ T hT)).map
    (homology_functor C 0)).exact :=
functor.is_homological.map_distinguished _ T hT
/- Using rotation of triangles, there is actually an (infinitely) long exact sequence of
homology, which contains as a particular case the long exact homology sequence associated
to as short exact sequence of complexes. -/

/-- For any `n : ℤ`, there is a functor `single_functor C n : C ⥤ derived_category C`
which sends `A : C` to the complex consisting of `A` in degree `n`, and `0` otherwise.
This functor is fully faithful. -/
instance (n : ℤ) : full (single_functor C n) := infer_instance
instance (n : ℤ) : faithful (single_functor C n) := infer_instance

/-- As a particular case of the construction of a distinguished associated to
a short exact sequence of complexes, a short exact sequence `0 ⟶ B ⟶ E ⟶ A ⟶ 0`
in the abelian category `C` induces a distinguished triangle. -/
example {A B : C} (e : extension A B) :
  (triangle.mk ((single_functor C 0).map e.i) ((single_functor C 0).map e.p) e.δ)
    ∈ dist_triang (derived_category C) := extension.triangle_distinguished e

/-- In the distinguished triangle associated to an extension `e : extension A B`,
we have a connecting morphism `e.δ`. -/
example {A B : C} (e : extension A B) :
  (single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦(1 : ℤ)⟧ := e.δ

/-- All morphisms `(single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦(1 : ℤ)⟧`
are `e.δ` for some `e : extension A B`, and the isomorphisms class of `e` is uniquely
determined. This can be translated as a natural isomorphism from the
bifunctor `extensions_functor C` which sends `A` and `B` to the set of isomorphism
classes in the category `extension A B`. -/
example : extensions_functor C ≅
  ((single_functor C 0).op ⋙
    (single_functor C 0 ⋙ shift_functor _ (1 : ℤ) ⋙ yoneda).flip).flip :=
extensions.δ_nat_iso C

/-- When `n : ℤ` is ≥ 2, the obvious short exact sequence 0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/nℤ ⟶ 0 does not split,
which gives a non trival morphism "ℤ/nℤ ⟶ ℤ⟦1⟧` in the derived category. -/
example (n : ℤ) (hn : 2 ≤ n) :
  (Module.extension_of_non_zero_divisor (n : ℤ) (n.non_zero_divisor_of_two_le hn)).δ ≠ 0 :=
begin
  rw Module.extension_of_non_zero_divisor.δ_neq_zero,
  intro h,
  cases int.is_unit_iff.1 h; linarith,
end

/-- Even though we defined (canonical) truncation functors on `cochain_complex C ℤ` and
`derived_category C` (cf. `algebra/homology/trunc.lean`), we did not formalise
t-structures, but at least we have the following "orthogonality condition" which says
that there are no nonzero morphisms `K ⟶ L` in the derived category
when `K` is cohomologically in degrees ≤ 0 and `L` is cohomologically in degrees ≥ 1. -/
lemma t_structure_condition {K L : derived_category C} [K.is_le 0] [L.is_ge 1]
  (f : K ⟶ L) : f = 0 := orthogonality f 0 1 (one_pos)

/-- In particular, there are no nonzeros morphisms
`(single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦n⟧` when `n>0`. -/
example (A B : C) (n : ℤ) (hn : n < 0)
  (f : (single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦n⟧) :
    f = 0 :=
begin
  /- We show that `(((single_functor C 0).obj B)⟦n⟧` has no homology in degrees < -n -/
  haveI : (((single_functor C 0).obj B)⟦n⟧).is_ge (-n) := shift_is_ge _ 0 n (-n) (by linarith),
  /- In particular, it has no homology in degrees < 1 -/
  haveI : (((single_functor C 0).obj B)⟦n⟧).is_ge 1 := is_ge_of_le _ 1 (-n) (by linarith),
  /- Then, we use a general orthogonality condition -/
  apply t_structure_condition,
end

end derived_category
