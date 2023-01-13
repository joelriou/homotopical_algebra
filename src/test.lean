import for_mathlib.category_theory.abelian.extension_example
import for_mathlib.algebra.homology.homology_sequence
import for_mathlib.algebra.homology.k_projective

noncomputable theory

open category_theory category_theory.pretriangulated category_theory.abelian
  derived_category

variables {C : Type*} [category C] [abelian C]

/-- The derived category `derived_category C` of an abelian category `C`
is a triangulated category. -/
example : is_triangulated (derived_category C) := infer_instance

/-- There is a triangulated functor from the homotopy category of cochain
complexes indexed by `ℤ` to the derived category. -/
example : functor.is_triangulated
  (Qh : homotopy_category C (complex_shape.up ℤ) ⥤ derived_category C) := infer_instance

/-- The derived category of an abelian category is the localization of the
homotopy category of cochain complexes indexed by `ℤ` with respect to a
certain class of morphisms `(homotopy_category.acyclic C).W`.
By definition, `homotopy_category.acyclic C` is the subtriangulated category
of the homotopy category consisting of acyclic complexes (i.e. with zero homology).
The class `(homotopy_category.acyclic C).W` is then the class of morphisms whose
"cone" is acyclic.  -/
example : functor.is_localization Qh (homotopy_category.acyclic C).W := infer_instance

/-- The canonical functor `Q : cochain_complex C ℤ ⥤ derived_category C`
is the composition of two functors :
`homotopy_category.quotient _ _ : cochain_complex C ℤ ⥤ homotopy_category C (complex_shape.up ℤ)`
and `Qh : homotopy_category C (complex_shape.up ℤ) ⥤ derived_category C`. -/
example : cochain_complex C ℤ ⥤ derived_category C := Q

/-- The derived category was defined here in two steps from `cochain_complex C ℤ`
(passing to the quotient by the homotopy relation, and then localizing). In this
way, we could get the triangulated structure. We also obtain that the
derived category is the localization of `cochain_complex C ℤ` with
respect to quasi-isomorphisms, which are morphisms inducing isomorphisms
in homology. (This is obtained by showing that the homotopy category is the localization
of `cochain_complex C ℤ` with respect to homotopy equivalences, and a general composition
of localization statement.) -/
example : functor.is_localization Q (quasi_isomorphisms C _) := infer_instance

/- For any short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `cochain_complex C ℤ`, there is
an associated distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` in the derived category. -/
example {X₁ X₂ X₃ : cochain_complex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0)
  (ex : (short_complex.mk f g w).short_exact) :
  triangle.mk (Q.map f) (Q.map g) (triangle_of_ses_δ ex) ∈ dist_triang (derived_category C) :=
triangle_of_ses_dist ex

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
/- Using the rotation of triangles, there is actually an infinitely long exact homology
sequence associated to any distinguished triangle in `derived_category C`. -/

section homology_sequence

open cochain_complex.homology_sequence

variables {X₁ X₂ X₃ : cochain_complex C ℤ} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {w : f ≫ g = 0}
  (ex : (short_complex.mk f g w).short_exact) (n₀ n₁ : ℤ) (h : n₁ = n₀ + 1)

/- Using the distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` associated to
a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `cochain_complex C ℤ`, we get
a connecting homomorphism in homology, which raises the degree by `1` : `n₁ = n₀ + 1`. -/
example : X₃.homology n₀ ⟶ X₁.homology n₁ := cochain_complex.homology_sequence.δ ex n₀ n₁ h

/- Exactness of the long homology sequences. -/

example : (short_complex.mk (homology_map f n₀) (homology_map g n₀) _).exact := ex₂ ex n₀

example : (short_complex.mk (homology_map g n₀) (δ ex n₀ n₁ h) _).exact := ex₃ ex n₀ n₁ h

example : (short_complex.mk (δ ex n₀ n₁ h) (homology_map f n₁) _).exact := ex₁ ex n₀ n₁ h

/- Relation to the snake lemma. -/

variables {A : C} (x₃ : A ⟶ X₃.X n₀) (x₂ : A ⟶ X₂.X n₀) (x₁ : A ⟶ X₁.X n₁)
  (hx₃ : x₃ ≫ X₃.d n₀ n₁ = 0) -- `x₃` can be thought as a cocycle of `X₃`
  (hx₂ : x₂ ≫ g.f n₀ = x₃)    -- `x₂` is a lift of `x₃`, which may not be a cocycle...
  (hx₁ : x₁ ≫ f.f n₁ = x₂ ≫ X₂.d n₀ n₁) -- `x₁` identifies to the differential of `x₂`

/-- The image of the homology class of the cocycle `x₃` by the connecting homomorphism
is the homology class of `x₁`. -/
example : X₃.lift_cycles x₃ n₁ h.symm hx₃ ≫ X₃.homology_π n₀ ≫ δ ex n₀ n₁ h =
  X₁.lift_cycles x₁ _ rfl _ ≫ X₁.homology_π n₁ :=
cochain_complex.homology_sequence.comp_δ_eq ex x₃ x₂ x₁ h hx₃ hx₂ hx₁

/- Note: the proof of the exactness of the long exact sequence above did not use the
snake lemma. Using the snake lemma, one may get a different construction of a more
general exact sequence in homology associated to a short exact sequences of complexes
for any complex_shape `c`. Then, the formula above could be used in order to show
that the connecting homomorphism obtained from the snake lemma is the same as the
one obtained from the construction above using a distinguished triangle in the
derived category. -/

end homology_sequence

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

/-- By definition, a cochain complex `K` is K-projective if for any acyclic complex `L`,
all the maps `K ⟶ L` are null homotopic (Spaltenstein). Then, if `K` is K-projective,
morphisms from `Q.obj K` in the derived category can be computed as homotopy classes
of maps. -/
example (K L : cochain_complex C ℤ) [K.is_K_projective] :
  function.bijective (Qh.map :
    ((homotopy_category.quotient C (complex_shape.up ℤ)).obj K ⟶
    (homotopy_category.quotient C (complex_shape.up ℤ)).obj L) → (Q.obj K ⟶ Q.obj L)) :=
Qh_map_bijective_of_is_K_projective K L

/-- A key technical result is that a bounded above complex consisting of
projective objects is K-projective. -/
example (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_le n]
  [∀ (n : ℤ), projective (K.X n)] : K.is_K_projective :=
cochain_complex.is_K_projective_of_bounded_above_of_projective K n

/- It follows from the two previous results that there is a full embedding from
the homotopy category of bounded above complexes of projectives objects into the
derived category. -/
