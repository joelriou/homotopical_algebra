import for_mathlib.category_theory.shift_op
import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.category_theory.triangulated.homological_functor

open category_theory category_theory.limits category_theory.category

namespace category_theory

instance right_op_preserves_zero_morphisms {C D : Type*}
  [category C] [category D] [has_zero_morphisms C]
  [has_zero_morphisms D] (F : Cᵒᵖ ⥤ D) [F.preserves_zero_morphisms] :
    F.right_op.preserves_zero_morphisms :=
⟨λ X Y, begin
  change (F.map 0).op = 0,
  simpa only [F.map_zero],
end⟩

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

lemma distinguished_cocone_triangle_op {X Y : Cᵒᵖ} (f : X ⟶ Y) :
  ∃ (Z : Cᵒᵖ) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
    triangle.mk f g h ∈ distinguished_triangle_op C :=
begin
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle₁ f.unop,
  rw [mem_dist_triang_iff_op, rotate_distinguished_triangle_op] at mem,
  exact ⟨_, _, _, mem⟩,
end

--#check triangle.unop_rotate
lemma complete_distinguished_triangle_morphism_op (T₁ T₂ : triangle Cᵒᵖ)
  (hT₁ : T₁ ∈ distinguished_triangle_op C) (hT₂ : T₂ ∈ distinguished_triangle_op C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃),
    T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ :=
begin
  have comm : T₂.unop.mor₃ ≫ a.unop⟦(-1 : ℤ)⟧'⟦(1 : ℤ)⟧' = b.unop ≫ T₁.unop.mor₃,
  { dsimp [triangle.unop],
    slice_rhs 1 2 { rw ← unop_comp, },
    simp only [fac, unop_comp, assoc],
    erw ← nat_trans.naturality,
    refl, },
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism₂ T₂.unop T₁.unop
    hT₂ hT₁ _ _ comm,
  let f : T₂.unop ⟶ T₁.unop :=
  { hom₁ := a.unop⟦(-1 : ℤ)⟧',
    hom₂ := c,
    hom₃ := b.unop,
    comm₁' := hc₁,
    comm₂' := hc₂,
    comm₃' := comm, },
  let f' := (triangle_op_equivalence C).inverse.preimage f.op,
  have hf' : f = ((triangle_op_equivalence C).inverse.map f').unop :=
    quiver.hom.op_inj (functor.image_preimage _ _).symm,
  have hf'₁ : f'.hom₁ = a,
  { apply quiver.hom.unop_inj,
    apply (shift_functor C (-1 : ℤ)).map_injective,
    change _ = f.hom₁,
    rw hf',
    refl, },
  have hf'₂ : f'.hom₂ = b,
  { apply quiver.hom.unop_inj,
    change _ = f.hom₃,
    rw hf',
    refl, },
  exact ⟨f'.hom₃, by rw [f'.comm₂, hf'₂], by rw [← f'.comm₃, hf'₁]⟩,
end

instance : pretriangulated Cᵒᵖ :=
{ distinguished_triangles := distinguished_triangle_op C,
  isomorphic_distinguished := isomorphic_distinguished_op,
  contractible_distinguished := contractible_distinguished_op,
  distinguished_cocone_triangle := λ X Y f, distinguished_cocone_triangle_op f,
  rotate_distinguished_triangle := rotate_distinguished_triangle_op,
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism_op, }

/- TODO : octahedron axiom for Cᵒᵖ -/

end pretriangulated

namespace functor

variables {C} {A : Type*} [category A] [abelian A] (F : Cᵒᵖ ⥤ A)
  [preserves_zero_morphisms F]

lemma is_homological.of_unop
  (hF : ∀ (T : pretriangulated.triangle C) (hT : T ∈ dist_triang C),
    ((T.short_complex hT).map F.right_op).unop.exact) : F.is_homological :=
⟨λ T hT, begin
  refine (short_complex.exact_iff_of_iso _).1
    (hF T.unop.rotate (by simpa only [← pretriangulated.rotate_distinguished_triangle] using hT)),
  refine short_complex.mk_iso
    (F.map_iso ((shift_equiv C (1 : ℤ)).counit_iso.symm.app (opposite.unop T.obj₁)).op)
    (iso.refl _) (iso.refl _) _ (by tidy),
  { dsimp [pretriangulated.triangle.unop],
    rw [comp_id, F.map_comp], },
end⟩

end functor

end category_theory
