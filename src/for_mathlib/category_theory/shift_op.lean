import for_mathlib.category_theory.triangulated.shift_compatibility
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import category_theory.preadditive.opposite
import for_mathlib.category_theory.preadditive.misc
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
  { obj₁ := opposite.op T.unop.obj₃,
    obj₂ := opposite.op T.unop.obj₂,
    obj₃ := opposite.op T.unop.obj₁,
    mor₁ := T.unop.mor₂.op,
    mor₂ := T.unop.mor₁.op,
    mor₃ := ((shift_equiv C (1 : ℤ)).unit_iso.inv.app T.unop.obj₁).op ≫
      (T.unop.mor₃⟦(-1 : ℤ)⟧').op, },
  map := λ T₁ T₂ f,
  { hom₁ := f.unop.hom₃.op,
    hom₂ := f.unop.hom₂.op,
    hom₃ := f.unop.hom₁.op,
    comm₁' := quiver.hom.unop_inj f.unop.comm₂.symm,
    comm₂' := quiver.hom.unop_inj f.unop.comm₁.symm,
    comm₃' := quiver.hom.unop_inj begin
      dsimp only,
      have h := (shift_equiv C (1 : ℤ)).unit_iso.inv.naturality f.unop.hom₁,
      simp only [category_theory.shift_functor_op_map, unop_comp, quiver.hom.unop_op, assoc],
      erw ← (shift_equiv C (1 : ℤ)).unit_iso.inv.naturality f.unop.hom₁,
      dsimp only [shift_equiv, functor.comp_map],
      simp only [← assoc, ← functor.map_comp, f.unop.comm₃],
    end, }, }

@[simps]
def inverse : triangle Cᵒᵖ ⥤ (triangle C)ᵒᵖ :=
{ obj := λ T, opposite.op
  { obj₁ := T.obj₃.unop,
    obj₂ := T.obj₂.unop,
    obj₃ := T.obj₁.unop,
    mor₁ := T.mor₂.unop,
    mor₂ := T.mor₁.unop,
    mor₃ := (shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₁.unop ≫ T.mor₃.unop⟦(1 : ℤ)⟧', },
  map := λ T₁ T₂ f, quiver.hom.op
  { hom₁ := f.hom₃.unop,
    hom₂ := f.hom₂.unop,
    hom₃ := f.hom₁.unop,
    comm₁' := quiver.hom.op_inj f.comm₂.symm,
    comm₂' := quiver.hom.op_inj f.comm₁.symm,
    comm₃' := begin
      dsimp only,
      have h := functor.congr_map (shift_functor C (1 : ℤ)) (congr_arg quiver.hom.unop f.comm₃),
      simp only [unop_comp, functor.map_comp] at h,
      simp only [assoc, ← h],
      erw ← nat_trans.naturality_assoc,
      refl,
    end, }, }

@[simps]
def unit_iso : 𝟭 _ ≅ functor C ⋙ inverse C :=
nat_iso.of_components (λ T, begin
  refine iso.op (_ : opposite.unop _ ≅ opposite.unop T),
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
  dsimp only [iso.refl],
  rw [functor.map_id, comp_id, id_comp],
  change (shift_equiv C (1 : ℤ)).counit_iso.inv.app T.unop.obj₃ ≫
    (shift_functor C (1 : ℤ)).map (((shift_functor C (-1 : ℤ)).map T.unop.mor₃) ≫
      ((shift_equiv C (1 : ℤ)).unit_iso.inv.app T.unop.obj₁)) = T.unop.mor₃,
  erw [functor.map_comp, (shift_equiv C (1 : ℤ)).fun_inv_map],
  simp only [assoc],
  erw (shift_equiv C (1 : ℤ)).counit_inv_functor_comp,
  erw comp_id,
  erw iso.inv_hom_id_app_assoc,
end) (λ X Y f, quiver.hom.unop_inj (by tidy))

@[simps]
def counit_iso : inverse C ⋙ functor C ≅ 𝟭 _ :=
nat_iso.of_components (λ T, begin
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _)
    (by tidy) (by tidy) (quiver.hom.unop_inj _),
  dsimp only [iso.refl],
  rw [functor.map_id, id_comp, comp_id],
  change ((shift_equiv C (1 : ℤ)).counit_iso.inv.app (opposite.unop T.obj₁) ≫
    T.mor₃.unop⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫
    ((shift_equiv C (1 : ℤ)).unit_iso.inv.app T.obj₃.unop) = T.mor₃.unop,
  erw [functor.map_comp, (shift_equiv C (1 : ℤ)).inv_fun_map],
  simp only [assoc, iso.hom_inv_id_app],
  erw comp_id,
  slice_lhs 1 2 { erw (shift_equiv C (1 : ℤ)).inverse_counit_inv_comp, },
  erw id_comp,
end) (by tidy)

end triangle_op_equivalence

@[simps]
def triangle_op_equivalence : (triangle C)ᵒᵖ ≌ triangle Cᵒᵖ :=
{ functor := triangle_op_equivalence.functor C,
  inverse := triangle_op_equivalence.inverse C,
  unit_iso := triangle_op_equivalence.unit_iso C,
  counit_iso := triangle_op_equivalence.counit_iso C, }

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

def triangle.unop_rotate (T : triangle Cᵒᵖ) : T.rotate.unop ≅ T.unop.inv_rotate :=
begin
  refine triangle.mk_iso _ _ (preadditive.mul_iso (-1) (iso.refl _)) (iso.refl _) (iso.refl _) _ _ _,
  { change T.mor₃.unop ≫ 𝟙 _ = ((-1 : ℤ) • 𝟙 _) ≫
      -((shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₁.unop ≫ T.mor₃.unop⟦(1 : ℤ)⟧')⟦(-1:ℤ)⟧' ≫
      (shift_equiv C (1 : ℤ)).unit_iso.inv.app T.obj₃.unop,
    simp only [comp_id, neg_smul, one_smul, preadditive.comp_neg, preadditive.neg_comp, neg_neg,
      id_comp, functor.map_comp, assoc],
    erw (shift_equiv C (1 : ℤ)).inv_fun_map,
    slice_rhs 1 2 { erw (shift_equiv C (1 : ℤ)).inverse_counit_inv_comp, },
    simp only [assoc, iso.hom_inv_id_app],
    erw [id_comp, comp_id], },
  { dsimp only [iso.refl],
    rw [id_comp, comp_id],
    refl, },
  { change ((shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₂.unop ≫
      (-(T.mor₁).unop⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧') ≫ ((-1 : ℤ) • 𝟙 _)⟦(1 : ℤ)⟧' =
        𝟙 _ ≫ T.mor₁.unop ≫ (shift_equiv C (1 : ℤ)).counit_iso.inv.app T.obj₁.unop,
    simp only [functor.map_neg, neg_smul, one_smul, functor.map_id, preadditive.comp_neg,
      preadditive.neg_comp, neg_neg, comp_id, id_comp],
    erw ← nat_trans.naturality,
    refl, },
end

end pretriangulated

end category_theory
