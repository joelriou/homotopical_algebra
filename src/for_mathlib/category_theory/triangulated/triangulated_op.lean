import for_mathlib.category_theory.shift_op
import for_mathlib.category_theory.triangulated.triangulated

open category_theory category_theory.limits category_theory.category


namespace category_theory

local attribute [instance] has_shift_op_neg_ℤ

variables (C : Type*) [category C] [has_zero_object C] [preadditive C]
  [has_shift C ℤ] [∀ (n : ℤ), (shift_functor C n).additive]
  [pretriangulated C]

namespace pretriangulated

def distinguished_triangle_op : set (triangle Cᵒᵖ) :=
λ T, T.unop ∈ dist_triang C

variable {C}

lemma mem_dist_triang_iff_unop (T : triangle Cᵒᵖ) :
  T ∈ distinguished_triangle_op C ↔ T.unop ∈ dist_triang C := by refl

lemma mem_dist_triang_iff_op (T : triangle C) :
  (T ∈ dist_triang C) ↔ T.op ∈ distinguished_triangle_op C :=
begin
  rw mem_dist_triang_iff_unop,
  split,
  { exact λ hT, isomorphic_distinguished _ hT _ T.unop_op, },
  { exact λ hT, isomorphic_distinguished _ hT _ T.unop_op.symm, },
end

variable {C}

lemma isomorphic_distinguished_op (T₁ : triangle Cᵒᵖ) (hT₁ : T₁ ∈ distinguished_triangle_op C)
  (T₂ : triangle Cᵒᵖ) (e : T₂ ≅ T₁) : T₂ ∈ distinguished_triangle_op C :=
begin
  rw mem_dist_triang_iff_unop at hT₁ ⊢,
  exact isomorphic_distinguished _ hT₁ _ ((triangle_op_equivalence C).inverse.map_iso e).unop.symm,
end

lemma contractible_distinguished_op (X : Cᵒᵖ) :
  contractible_triangle X ∈ distinguished_triangle_op C :=
begin
  rw [mem_dist_triang_iff_unop, rotate_distinguished_triangle, rotate_distinguished_triangle],
  dsimp [contractible_triangle, triangle.rotate, triangle.unop],
  refine isomorphic_distinguished _ (contractible_distinguished (opposite.unop X)) _ _,
  refine triangle.mk_iso _ _ (iso.refl _) ((shift_equiv C (1 : ℤ)).counit_iso.app (opposite.unop X))
    ((shift_functor C (1 : ℤ)).map_iso ((is_zero_zero Cᵒᵖ).unop).iso_zero ≪≫
    (shift_functor C (1 : ℤ)).map_zero_object) _ (is_zero.eq_of_tgt (is_zero_zero C) _ _)
    (is_zero.eq_of_src (is_zero.of_iso (is_zero_zero C)
      ((shift_functor C (1 : ℤ)).map_iso ((is_zero_zero Cᵒᵖ).unop).iso_zero ≪≫
      (shift_functor C (1 : ℤ)).map_zero_object)) _ _),
  dsimp only [triangle.mk, iso.refl, contractible_triangle],
  simpa only [id_comp] using (shift_equiv C (1 : ℤ)).counit_iso.inv_hom_id_app X.unop,
end

lemma rotate_distinguished_triangle_op (T : triangle Cᵒᵖ) :
  T ∈ distinguished_triangle_op C ↔ T.rotate ∈ distinguished_triangle_op C :=
begin
  simp only [mem_dist_triang_iff_unop],
  rw [isomorphic_distinguished_iff T.unop_rotate, inv_rotate_distinguished_triangle],
end

instance : pretriangulated Cᵒᵖ :=
{ distinguished_triangles := distinguished_triangle_op C,
  isomorphic_distinguished := isomorphic_distinguished_op,
  contractible_distinguished := contractible_distinguished_op,
  distinguished_cocone_triangle := sorry,
  rotate_distinguished_triangle := rotate_distinguished_triangle_op,
  complete_distinguished_triangle_morphism := sorry, }

end pretriangulated

end category_theory
