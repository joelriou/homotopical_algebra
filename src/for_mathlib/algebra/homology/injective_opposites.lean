import for_mathlib.algebra.homology.k_projective

open category_theory category_theory.category category_theory.limits

namespace cochain_complex

variables {C : Type*} [category C] [preadditive C]

namespace op_equivalence

@[simps]
def op_obj (K : cochain_complex C ℤ) :
  cochain_complex Cᵒᵖ ℤ :=
{ X := λ n, opposite.op (K.X (-n)),
  d := λ n m, (K.d _ _).op,
  shape' := λ i j hij, begin
    rw K.shape,
    { refl, },
    { simp only [complex_shape.up_rel] at ⊢ hij,
      intro h,
      apply hij,
      linarith, },
  end,
  d_comp_d' := λ i j k hij hjk,
    by simpa only [← op_comp, homological_complex.d_comp_d], }

@[simps]
def unop_obj (K : cochain_complex Cᵒᵖ ℤ) :
  cochain_complex C ℤ :=
{ X := λ n, opposite.unop (K.X (-n)),
  d := λ n m, (K.d _ _).unop,
  shape' := λ i j hij, begin
    rw K.shape,
    { refl, },
    { simp only [complex_shape.up_rel] at ⊢ hij,
      intro h,
      apply hij,
      linarith, },
  end,
  d_comp_d' := λ i j k hij hjk,
    by simpa only [← unop_comp, homological_complex.d_comp_d], }

@[simps]
def unop_op_obj (K : cochain_complex C ℤ) :
  unop_obj (op_obj K) ≅ K :=
homological_complex.hom.iso_of_components
  (λ n, homological_complex.X_iso_of_eq K (by linarith)) (by tidy)

@[simps]
def op_unop_obj (K : cochain_complex Cᵒᵖ ℤ) :
  op_obj (unop_obj K) ≅ K :=
homological_complex.hom.iso_of_components
  (λ n, homological_complex.X_iso_of_eq K (by linarith)) (by tidy)

variable (C)

@[simps]
def functor : (cochain_complex C ℤ)ᵒᵖ ⥤ cochain_complex Cᵒᵖ ℤ :=
{ obj := λ K, op_obj (opposite.unop K) ,
  map := λ K L φ,
  { f := λ n, (φ.unop.f (-n)).op,
    comm' := λ i j hij, begin
      dsimp,
      simp only [← op_comp, homological_complex.hom.comm],
    end, }, }

@[simps]
def inverse : cochain_complex Cᵒᵖ ℤ ⥤ (cochain_complex C ℤ)ᵒᵖ :=
{ obj := λ K, opposite.op (unop_obj K),
  map := λ K L φ, quiver.hom.op
  { f := λ n, (φ.f (-n)).unop,
    comm' := λ i j hij, begin
      dsimp,
      simp only [← unop_comp, homological_complex.hom.comm],
    end, }, }

@[simps]
def unit_iso :
  𝟭 (cochain_complex C ℤ)ᵒᵖ ≅ op_equivalence.functor C ⋙ op_equivalence.inverse C :=
nat_iso.of_components (λ K, (unop_op_obj (opposite.unop K)).op)
  (λ K L f, quiver.hom.unop_inj begin
    ext n,
    dsimp,
    symmetry,
    apply homological_complex.X_iso_of_eq_hom_naturality f.unop,
  end)

@[simps]
def counit_iso :
  op_equivalence.inverse C ⋙ op_equivalence.functor C ≅ 𝟭 (cochain_complex Cᵒᵖ ℤ) :=
nat_iso.of_components (λ K, (op_unop_obj K))
  (λ K L f, begin
    ext n,
    dsimp,
    apply homological_complex.X_iso_of_eq_hom_naturality f,
  end)

end op_equivalence

@[simps]
def op_equivalence : (cochain_complex C ℤ)ᵒᵖ ≌ cochain_complex Cᵒᵖ ℤ :=
{ functor := op_equivalence.functor C,
  inverse := op_equivalence.inverse C,
  unit_iso := op_equivalence.unit_iso C,
  counit_iso := op_equivalence.counit_iso C,
  functor_unit_iso_comp' := λ K, begin
    ext n,
    dsimp [homological_complex.X_iso_of_eq],
    simp only [eq_to_hom_op, eq_to_hom_trans, eq_to_hom_refl],
  end, }

end cochain_complex
