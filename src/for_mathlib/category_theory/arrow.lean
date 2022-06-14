/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow
import category_theory.limits.shapes.binary_products

noncomputable theory

open category_theory.limits opposite category_theory.category

namespace category_theory

namespace arrow

variables {C D : Type*} [category C] [category D]

/-- Condition that the image of `f` by `F` is an isomorphism -/
def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

namespace is_inverted_by

lemma of_is_iso {f : arrow C} {F : C ⥤ D} (h : is_iso (F.map f.hom)) : f.is_inverted_by F := h

end is_inverted_by

lemma congr_left {f g : arrow C} (h : f = g) : f.left = g.left := by rw h
lemma congr_right {f g : arrow C} (h : f = g) : f.right = g.right := by rw h

lemma mk_eq (f : arrow C) : arrow.mk f.hom = f :=
by { cases f, dsimp [arrow.mk], refl, }

namespace hom

lemma congr_left {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by rw h
lemma congr_right {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by rw h

end hom

def mk_iso {f g : arrow C} (e₁ : f.left ≅ g.left) (e₂ : f.right ≅ g.right)
  (fac : e₁.hom ≫ g.hom = f.hom ≫ e₂.hom) :
  f ≅ g :=
{ hom :=
  { left := e₁.hom,
    right := e₂.hom,
    w' := fac, },
  inv :=
  { left := e₁.inv,
    right := e₂.inv,
    w' := begin
      rw [← comp_id f.hom],
      dsimp,
      rw [← e₂.hom_inv_id],
      slice_lhs 2 3 { rw ← fac, },
      slice_lhs 1 2 { rw e₁.inv_hom_id, },
      rw id_comp,
    end, },
  hom_inv_id' := begin
    ext,
    exacts [e₁.hom_inv_id, e₂.hom_inv_id],
  end,
  inv_hom_id' := begin
    ext,
    exacts [e₁.inv_hom_id, e₂.inv_hom_id],
  end, }

@[simps]
def op_prod {C : Type*} [category C] {X Y : C} [has_binary_product X Y] 
  [has_binary_coproduct (op X) (op Y)] :
  op (X ⨯ Y) ≅ op X ⨿ op Y :=
begin
  let cofan : binary_cofan (op X) (op Y) :=
    binary_cofan.mk (limits.prod.fst : X ⨯ Y ⟶ X).op ((limits.prod.snd : X ⨯ Y ⟶ Y).op),
  refine (is_colimit.cocone_point_unique_up_to_iso (coprod_is_coprod (op X) (op Y)) (_ : is_colimit cofan)).symm,
  exact
  { desc := λ s, begin
      let blah := discrete,
      let φ : _ ⟶ X ⨯ Y := limits.prod.lift (s.ι.app (discrete.mk walking_pair.left)).unop (s.ι.app (discrete.mk walking_pair.right)).unop,
      exact φ.op,
    end,
    fac' := λ s j, begin
      cases j,
      cases j; dsimp [cofan],
      { rw [← op_comp, prod.lift_fst, quiver.hom.op_unop], },
      { rw [← op_comp, prod.lift_snd, quiver.hom.op_unop], },
    end,
    uniq' := λ s j hs, begin
      dsimp,
      apply quiver.hom.unop_inj,
      rw quiver.hom.unop_op,
      ext,
      { simp only [prod.lift_fst],
        exact congr_arg (quiver.hom.unop) (hs (discrete.mk walking_pair.left)), },
      { simp only [prod.lift_snd],
        exact congr_arg (quiver.hom.unop) (hs (discrete.mk walking_pair.right)), },
    end, },
end

def iso_op_prod_lift {A X Y : C} [has_binary_product X Y]
  [has_binary_coproduct (op X) (op Y)] (f : A ⟶ X) (g : A ⟶ Y) :
  arrow.mk (prod.lift f g).op ≅ arrow.mk (coprod.desc f.op g.op) :=
begin
  symmetry,
  refine mk_iso op_prod.symm (by refl) _,
  dsimp,
  erw [comp_id],
  ext,
  { dsimp [limits.is_colimit.cocone_point_unique_up_to_iso, coprod_is_coprod],
    simp only [coprod.inl_desc, id_comp, comp_id, coprod.desc_comp, ← op_comp, prod.lift_fst], },
  { dsimp [limits.is_colimit.cocone_point_unique_up_to_iso, coprod_is_coprod],
    simp only [coprod.inr_desc, id_comp, comp_id, coprod.desc_comp, ← op_comp, prod.lift_snd], },
end

end arrow

end category_theory
