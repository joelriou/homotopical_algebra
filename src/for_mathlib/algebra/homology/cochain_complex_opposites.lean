import for_mathlib.algebra.homology.k_projective
import category_theory.abelian.injective

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

namespace short_complex

variables {C : Type*} [category C] [has_zero_morphisms C]
  (S : short_complex C) [has_homology S]

def homology_op_iso : S.op.homology ≅ opposite.op S.homology :=
begin
  let h := S.some_homology_data,
  exact h.op.homology_iso ≪≫ h.iso.op ≪≫ h.homology_iso.op,
end

end short_complex

end category_theory

open category_theory

namespace cochain_complex

variables {C : Type*} [category C] [abelian C]

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

variable (C)

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

variable {C}

lemma op_obj_is_strictly_le (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_ge (-n)] :
  (op_equivalence.op_obj K).is_strictly_le n :=
⟨λ i hi, (cochain_complex.is_strictly_ge.is_zero K (-n) (-i) (by linarith)).op⟩

lemma op_obj_is_strictly_ge (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_le (-n)] :
  (op_equivalence.op_obj K).is_strictly_ge n :=
⟨λ i hi, (cochain_complex.is_strictly_le.is_zero K (-n) (-i) (by linarith)).op⟩

lemma unop_obj_is_strictly_le (K : cochain_complex Cᵒᵖ ℤ) (n : ℤ) [K.is_strictly_ge (-n)] :
  (op_equivalence.unop_obj K).is_strictly_le n :=
⟨λ i hi, (cochain_complex.is_strictly_ge.is_zero K (-n) (-i) (by linarith)).unop⟩

lemma unop_obj_is_strictly_ge (K : cochain_complex Cᵒᵖ ℤ) (n : ℤ) [K.is_strictly_le (-n)] :
  (op_equivalence.unop_obj K).is_strictly_ge n :=
⟨λ i hi, (cochain_complex.is_strictly_le.is_zero K (-n) (-i) (by linarith)).unop⟩

def unop_homotopy {K L : cochain_complex C ℤ} {f₁ f₂ : K ⟶ L}
  (h : homotopy ((op_equivalence.functor C).map f₁.op) ((op_equivalence.functor C).map f₂.op)) :
  homotopy f₁ f₂ :=
{ hom := λ i j, (K.X_iso_of_eq (by simp)).hom ≫ (h.hom (-j) (-i)).unop ≫
      (L.X_iso_of_eq (by simp)).hom,
  zero' := λ i j hij, begin
    rw [h.zero, unop_zero, zero_comp, comp_zero],
    simp only [complex_shape.up_rel] at hij ⊢,
    intro h,
    apply hij,
    linarith,
  end,
  comm := λ n, quiver.hom.op_inj begin
    obtain ⟨m, rfl⟩ : ∃ (m : ℤ), n = -m := ⟨-n, by rw neg_neg n⟩,
    have eq := h.comm m,
    have eq₁ : (complex_shape.up ℤ).rel m (m+1) := rfl,
    have eq₂ : (complex_shape.up ℤ).rel (m-1) m := by simp,
    have eq₃ : (complex_shape.up ℤ).rel (-m) (-(m-1)),
    { simp only [neg_sub, complex_shape.up_rel], linarith, },
    have eq₄ : (complex_shape.up ℤ).rel (-(m+1)) (-m) := by simp,
    rw [d_next_eq _ eq₁, prev_d_eq _ eq₂] at eq,
    rw [d_next_eq _ eq₃, prev_d_eq _ eq₄],
    dsimp at eq ⊢,
    rw eq,
    have eq₅ : ∀ (a a' b b' : ℤ) (ha : a = a') (hb : b = b'),
      h.hom a b = eq_to_hom (by rw ha) ≫ h.hom a' b' ≫ eq_to_hom (by rw hb),
    { intros a a' b b' ha hb,
      substs ha hb,
      simp only [eq_to_hom_refl, id_comp, comp_id], },
    conv_lhs { congr, rw add_comm, },
    congr' 3;
    { dsimp [homological_complex.X_iso_of_eq],
      simp only [assoc, eq_to_hom_op],
      exact eq₅ _ _ _ _ (neg_neg _).symm (neg_neg _).symm, },
  end, }

def homology_op_iso (K : cochain_complex C ℤ) (n : ℤ) :
  (op_equivalence.op_obj K).homology n ≅ opposite.op (K.homology (-n)) :=
begin
  have r₁ : (complex_shape.up ℤ).rel (-(n+1)) (-n) := by simp,
  have r₂ : (complex_shape.up ℤ).rel (-n) (-(n-1)) := by { rw complex_shape.up_rel, linarith, },
  have r₃ : (complex_shape.up ℤ).rel (n-1) n := by simp,
  have r₄ : (complex_shape.up ℤ).rel n (n+1) := by simp,
  refine _ ≪≫ short_complex.homology_op_iso _ ≪≫
    (short_complex.homology_map_iso
      ((homological_complex.short_complex_functor_nat_iso C _ r₁ r₂).app K)).op,
  exact short_complex.homology_map_iso
    ((homological_complex.short_complex_functor_nat_iso Cᵒᵖ _ r₃ r₄).app ((op_equivalence.op_obj K))),
end

lemma acyclic_op {K : cochain_complex C ℤ} (hK : homological_complex.acyclic K) :
  homological_complex.acyclic (op_equivalence.op_obj K) :=
λ n, is_zero.of_iso (hK (-n)).op (homology_op_iso K n)

end cochain_complex
