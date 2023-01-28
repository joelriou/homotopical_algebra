import for_mathlib.category_theory.triangulated.shift_compatibility
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import category_theory.preadditive.opposite
import tactic.abel

noncomputable theory

universe u

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C : Type*} {A B : Type u} [category C] [add_monoid A] [add_monoid B]
  {G : Type*} [add_comm_group G]

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

variables (C A)

def has_shift_op [has_shift C A] : has_shift Cᵒᵖ A :=
has_shift_mk _ _
{ F := λ a, (shift_functor C a).op,
  ε := (functor.op_unop_equiv C C).functor.map_iso (shift_functor_zero C A).op,
  μ := λ a b, (functor.op_unop_equiv C C).functor.map_iso (shift_functor_add C a b).op,
  associativity := λ a b c X, quiver.hom.unop_inj begin
    have eq := congr_arg iso.inv (monoidal_functor.associativity_iso_eq (shift_monoidal_functor C A)
      (discrete.mk a) (discrete.mk b) (discrete.mk c)),
    replace eq := congr_app eq (opposite.unop X),
    dsimp at ⊢ eq,
    erw [comp_id, id_comp, functor.map_id, functor.map_id, comp_id] at eq,
    simpa only [← eq, eq_to_hom_unop, eq_to_hom_map, eq_to_hom_app],
  end,
  left_unitality := λ a X, quiver.hom.unop_inj begin
    dsimp,
    simpa only [obj_ε_inv_app, eq_to_iso.hom, μ_inv_hom_app_assoc, eq_to_hom_unop,
      eq_to_hom_map, eq_to_hom_app],
  end,
  right_unitality := λ a X, quiver.hom.unop_inj begin
    dsimp,
    simpa only [ε_inv_app_obj, eq_to_iso.hom, μ_inv_hom_app_assoc, eq_to_hom_unop,
      eq_to_hom_map, eq_to_hom_app],
  end, }

variable {A}

def has_shift_pull [has_shift C B] (φ : A →+ B) : has_shift C A :=
⟨monoidal_functor.comp (discrete.add_monoidal_functor φ) (shift_monoidal_functor C B)⟩

variable {C}

def has_shift.op (s : has_shift C A) : has_shift Cᵒᵖ A :=
by { letI := s, apply has_shift_op, }

def has_shift.pull (s : has_shift C B) (φ : A →+ B) : has_shift C A :=
by { letI := s, exact has_shift_pull C φ, }

def has_shift.op_neg (s : has_shift C G) :
  has_shift Cᵒᵖ G :=
s.op.pull (⟨λ g, -g, by tidy, λ x y, by abel⟩ : G →+ G)

variables (C G)

def has_shift_op_neg [has_shift C G] : has_shift Cᵒᵖ G :=
has_shift.op_neg infer_instance

def has_shift_op_neg_ℤ [has_shift C ℤ] : has_shift Cᵒᵖ ℤ :=
has_shift.op_neg infer_instance

namespace pretriangulated

variables (C) [has_shift C ℤ]

local attribute [instance] has_shift_op_neg_ℤ

lemma _root_.category_theory.shift_functor_op_map
  {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) :
  (shift_functor Cᵒᵖ n).map f = ((shift_functor C (-n)).map f.unop).op := rfl

variable [preadditive C]

namespace triangle_op_equivalence

@[simps]
def functor : (triangle C)ᵒᵖ ⥤ triangle Cᵒᵖ :=
{ obj := λ T,
  { obj₁ := opposite.op (T.unop.obj₁⟦(1 : ℤ)⟧),
    obj₂ := opposite.op T.unop.obj₃,
    obj₃ := opposite.op T.unop.obj₂,
    mor₁ := T.unop.mor₃.op,
    mor₂ := T.unop.mor₂.op,
    mor₃ := -T.unop.mor₁.op ≫ ((shift_equiv C (1 : ℤ)).unit_iso.inv.app T.unop.obj₁).op, },
  map := λ T₁ T₂ f,
  { hom₁ := (f.unop.hom₁⟦(1 : ℤ)⟧').op,
    hom₂ := f.unop.hom₃.op,
    hom₃ := f.unop.hom₂.op,
    comm₁' := quiver.hom.unop_inj f.unop.comm₃.symm,
    comm₂' := quiver.hom.unop_inj f.unop.comm₂.symm,
    comm₃' := quiver.hom.unop_inj begin
      dsimp only,
      simp only [category_theory.shift_functor_op_map, shift_equiv_unit_iso,
        add_neg_equiv_unit_iso_inv, unit_of_tensor_iso_unit_hom_app, op_comp, quiver.hom.unop_op,
        preadditive.neg_comp, assoc, unop_neg, unop_comp, μ_naturality, nat_trans.naturality,
        functor.id_map, triangle_morphism.comm₁],
    end, }, }

@[simps]
def inverse : triangle Cᵒᵖ ⥤ (triangle C)ᵒᵖ :=
{ obj := λ T, opposite.op
  { obj₁ := T.obj₁.unop⟦(-1 : ℤ)⟧,
    obj₂ := T.obj₃.unop,
    obj₃ := T.obj₂.unop,
    mor₁ := -T.mor₃.unop,
    mor₂ := T.mor₂.unop,
    mor₃ := T.mor₁.unop ≫ (shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₁.unop, },
  map := λ T₁ T₂ f, quiver.hom.op
  { hom₁ := f.hom₁.unop⟦(-1 : ℤ)⟧',
    hom₂ := f.hom₃.unop,
    hom₃ := f.hom₂.unop,
    comm₁' := quiver.hom.op_inj begin
      dsimp,
      simpa only [preadditive.comp_neg, preadditive.neg_comp, neg_inj] using f.comm₃.symm,
    end,
    comm₂' := quiver.hom.op_inj f.comm₂.symm,
    comm₃' := begin
      dsimp,
      slice_rhs 1 2 { rw [← unop_comp, f.comm₁, unop_comp], },
      simp only [assoc],
      erw ← nat_trans.naturality,
      refl,
    end, }, }

@[simps]
def counit_iso : inverse C ⋙ functor C ≅ 𝟭 _ :=
nat_iso.of_components (λ T, begin
  refine triangle.mk_iso _ _ (((shift_equiv C (1 : ℤ)).counit_iso.app T.obj₁.unop).symm.op)
    (iso.refl _) (iso.refl _) (by tidy) (by tidy) (quiver.hom.unop_inj _),
  change ((shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₁.unop)⟦(-1 : ℤ)⟧' ≫
    (-((shift_equiv C (1 : ℤ)).unit_iso.inv.app (T.obj₁.unop⟦(-1 : ℤ)⟧) ≫ -T.mor₃.unop)) =
    T.mor₃.unop ≫ 𝟙 _,
  simp only [preadditive.comp_neg, neg_neg, comp_id],
  have eq := (shift_equiv C (1 : ℤ)).inverse_counit_inv_comp (opposite.unop T.obj₁) =≫ T.mor₃.unop,
  erw [id_comp, assoc] at eq,
  exact eq,
end)
(λ T₁ T₂ f, begin
  ext; apply quiver.hom.unop_inj,
  { exact ((shift_equiv C (1 : ℤ)).counit_iso.inv.naturality f.hom₁.unop).symm, },
  { dsimp, rw [id_comp, comp_id], },
  { dsimp, rw [id_comp, comp_id], },
end)

@[simps]
def unit_iso : 𝟭 _ ≅ functor C ⋙ inverse C :=
nat_iso.of_components (λ T, begin
  refine iso.op (_ : opposite.unop _ ≅ opposite.unop T),
  refine triangle.mk_iso _ _ (((shift_equiv C (1 : ℤ)).unit_iso.app T.unop.obj₁).symm)
    (iso.refl _) (iso.refl _) _ _ _,
  { tidy, },
  { tidy, },
  { change (T.unop.mor₃ ≫
      ((shift_equiv C (1 : ℤ)).counit_iso).inv.app ((opposite.unop T).obj₁⟦(1 : ℤ)⟧)) ≫
      ((shift_equiv C (1 : ℤ)).unit_iso.inv.app (opposite.unop T).obj₁)⟦(1 : ℤ)⟧' =
      𝟙 _ ≫ T.unop.mor₃,
    rw [id_comp, assoc],
    have eq := T.unop.mor₃ ≫= (shift_equiv C (1 : ℤ)).counit_inv_functor_comp (opposite.unop T).obj₁,
    erw [comp_id] at eq,
    exact eq, },
end)
(λ T₁ T₂ f, quiver.hom.unop_inj begin
  ext,
  { exact ((shift_equiv C (1 : ℤ)).unit_iso.inv.naturality f.unop.hom₁).symm, },
  { dsimp, rw [id_comp, comp_id], },
  { dsimp, rw [id_comp, comp_id], },
end)

end triangle_op_equivalence

@[simps]
def triangle_op_equivalence : (triangle C)ᵒᵖ ≌ triangle Cᵒᵖ :=
{ functor := triangle_op_equivalence.functor C,
  inverse := triangle_op_equivalence.inverse C,
  unit_iso := triangle_op_equivalence.unit_iso C,
  counit_iso := triangle_op_equivalence.counit_iso C,
  functor_unit_iso_comp' := λ T, begin
    ext,
    { exact quiver.hom.unop_inj ((shift_equiv C (1 : ℤ)).counit_inv_functor_comp T.unop.obj₁), },
    { dsimp, rw id_comp, },
    { dsimp, rw id_comp, },
  end, }

variable {C}

def triangle.op (T : triangle C) : triangle Cᵒᵖ :=
(triangle_op_equivalence C).functor.obj (opposite.op T)

def triangle.unop (T : triangle Cᵒᵖ) : triangle C :=
((triangle_op_equivalence C).inverse.obj T).unop

def triangle.unop_op (T : triangle C) : T.op.unop ≅ T :=
((triangle_op_equivalence C).unit_iso.app (opposite.op T)).unop

def triangle.op_unop (T : triangle Cᵒᵖ) : T.unop.op ≅ T :=
(triangle_op_equivalence C).counit_iso.app T

variables [∀ (n : ℤ), (shift_functor C n).additive]

instance shift_functor_op_additive (n : ℤ) : (shift_functor Cᵒᵖ n).additive :=
(infer_instance : (shift_functor C (-n)).op.additive)

variables [has_zero_object C] [pretriangulated C]

variable (C)

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
  rw mem_dist_triang_iff_unop,
  dsimp [contractible_triangle, triangle.unop],
  sorry,
end

instance : pretriangulated Cᵒᵖ :=
{ distinguished_triangles := distinguished_triangle_op C,
  isomorphic_distinguished := isomorphic_distinguished_op,
  contractible_distinguished := contractible_distinguished_op,
  distinguished_cocone_triangle := sorry,
  rotate_distinguished_triangle := sorry,
  complete_distinguished_triangle_morphism := sorry, }

end pretriangulated

end category_theory
