/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.isomorphism
import category_theory.limits.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.pullbacks
import category_theory.comma_op
import category_theory.epi_mono
import category_theory.retracts
import category_theory.cartesian_square

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite

namespace category_theory

variables (C : Type*) [category C]

abbreviation arrow_class := set (arrow C)

instance : has_coe_to_fun (arrow_class C) (λ F, (Π ⦃X Y : C⦄, (X ⟶ Y) → Prop)) :=
⟨λ F X Y f, (arrow.mk f) ∈ F⟩

variables {C}

namespace arrow


lemma mk_comp_eq_to_hom {X Y Z : C} (f : X ⟶ Y) (h : Y = Z) : arrow.mk (f ≫ eq_to_hom h) = arrow.mk f :=
by { subst h, erw comp_id, }
lemma mk_eq_to_hom_comp {X Y Z : C} (f : Y ⟶ Z) (h : X = Y) : arrow.mk (eq_to_hom h ≫ f) = arrow.mk f :=
by { subst h, erw id_comp, }

def is_retract_iff_op (f : arrow C) (f' : arrow C) :
  is_retract f f' ↔ is_retract f.op f'.op :=
begin
  let e := equivalence_arrow_op C,
  haveI := is_equivalence.of_equivalence e,
  have eq₁ := is_retract_iff_op f.op f'.op,
  have eq₂ := is_retract_iff_of_is_equivalence e.functor f f',
  exact eq₂.trans eq₁.symm,
end

def is_retract_iff_unop (f : arrow Cᵒᵖ) (f' : arrow Cᵒᵖ) :
  is_retract f f' ↔ is_retract f.unop f'.unop :=
begin
  have eq₁ := is_retract_iff_of_isos (eq_to_iso f.op_unop.symm) (eq_to_iso f'.op_unop.symm),
  have eq₂ := is_retract_iff_op f.unop f'.unop,
  exact eq₁.trans eq₂.symm,    
end

lemma op_mk {T : Type*} [category T] {X Y : T} (f : X ⟶ Y) : (arrow.mk f).op = arrow.mk f.op := by refl

lemma unop_mk {T : Type*} [category T] {X Y : Tᵒᵖ} (f : X ⟶ Y) :
  (arrow.mk f).unop = arrow.mk f.unop := by refl

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
      let φ : _ ⟶ X ⨯ Y := limits.prod.lift (s.ι.app walking_pair.left).unop (s.ι.app walking_pair.right).unop,
      exact φ.op,
    end,
    fac' := λ s j, begin
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
        exact congr_arg (quiver.hom.unop) (hs walking_pair.left), },
      { simp only [prod.lift_snd],
        exact congr_arg (quiver.hom.unop) (hs walking_pair.right), },
    end, },
end

@[simps]
def unop_prod_op {C : Type*} [category C] {X Y : C} [has_binary_coproduct X Y] [has_binary_product (op X) (op Y)] :
  unop ((op X) ⨯ (op Y)) ≅ X ⨿ Y :=
begin
  let cofan : binary_cofan X Y :=
    binary_cofan.mk (limits.prod.fst : (op X) ⨯ (op Y) ⟶ op X).unop ((limits.prod.snd : (op X) ⨯ (op Y) ⟶ op Y)).unop,
  refine (is_colimit.cocone_point_unique_up_to_iso (coprod_is_coprod X Y) (_ : is_colimit cofan)).symm,
  exact
  { desc := λ s, begin
      let φ : op (s.X) ⟶ (op X) ⨯ (op Y) := limits.prod.lift (s.ι.app walking_pair.left).op (s.ι.app walking_pair.right).op,
      exact φ.unop,
    end,
    fac' := λ s j, begin
      cases j; dsimp [cofan],
      { rw [← unop_comp, prod.lift_fst, quiver.hom.unop_op], },
      { rw [← unop_comp, prod.lift_snd, quiver.hom.unop_op], },
    end,
    uniq' := λ s j hs, begin
      dsimp,
      apply quiver.hom.op_inj,
      rw quiver.hom.op_unop,
      ext,
      { simp only [prod.lift_fst],
        exact congr_arg (quiver.hom.op) (hs walking_pair.left), },
      { simp only [prod.lift_snd],
        exact congr_arg (quiver.hom.op) (hs walking_pair.right), },
    end,
    },
end

def iso_op_prod_lift {C : Type*} [category C] {A X Y : C} [has_binary_product X Y] 
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


def iso_prod_lift_op {C : Type*} [category C] {A B X : C} [has_binary_coproduct A B]
  [has_binary_product (op A) (op B)] (f : A ⟶ X) (g : B ⟶ X) :
  arrow.mk (prod.lift f.op g.op) ≅ (arrow.mk (coprod.desc f g)).op :=
begin
  refine mk_iso (by refl) unop_prod_op.op.symm _,
  apply quiver.hom.unop_inj,
  dsimp,
  erw comp_id,
  ext,
  { dsimp [limits.is_colimit.cocone_point_unique_up_to_iso, coprod_is_coprod],
    simpa only [coprod.inl_desc, id_comp, comp_id, coprod.desc_comp, ← unop_comp, prod.lift_fst], },
  { dsimp [limits.is_colimit.cocone_point_unique_up_to_iso, coprod_is_coprod],
    simpa only [coprod.inr_desc, id_comp, comp_id, coprod.desc_comp, ← unop_comp, prod.lift_snd], },
end

end arrow

namespace arrow_class

variables (F : arrow_class C) (F' : arrow_class Cᵒᵖ)

def isomorphisms : arrow_class C := λ f, is_iso f.hom
def monomorphisms : arrow_class C := λ f, mono f.hom
def epimorphisms : arrow_class C := λ f, epi f.hom

def mem_isomorphisms_iff {X Y : C} (f : X ⟶ Y) : arrow.mk f ∈ (isomorphisms : arrow_class C) ↔ is_iso f :=
by refl
def mem_monomorphisms_iff {X Y : C} (f : X ⟶ Y) : arrow.mk f ∈ (monomorphisms : arrow_class C) ↔ mono f :=
by refl
def mem_epimorphisms_iff {X Y : C} (f : X ⟶ Y) : arrow.mk f ∈ (epimorphisms : arrow_class C) ↔ epi f :=
by refl

def op : arrow_class Cᵒᵖ := λ f, f.unop ∈ F
def unop : arrow_class C := λ f, f.op ∈ F'

lemma unop_op : F.op.unop = F :=
by { ext f, conv_rhs { rw ← arrow.unop_op f, }, refl, }
lemma op_unop : F'.unop.op = F' :=
by { ext f, conv_rhs { rw ← arrow.op_unop f, }, refl, }

lemma op_inj {f g : arrow_class C} (h : f.op = g.op) : f = g :=
by rw [← unop_op f, ← unop_op g, h]

lemma unop_inj {f g : arrow_class Cᵒᵖ} (h : f.unop = g.unop) : f = g :=
by rw [← op_unop f, ← op_unop g, h]

@[simp]
lemma mem_op_iff (f : arrow Cᵒᵖ) : f ∈ F.op ↔ f.unop ∈ F := by refl

@[simp]
lemma unop_mem_iff (f : arrow C) : f ∈ F'.unop ↔ f.op ∈ F' := by refl

lemma subset_iff_op (G : arrow_class C) : F ⊆ G ↔ F.op ⊆ G.op :=
begin
  split,
  { intros h f hf,
    exact h hf, },
  { intros h f hf,
    rw ← f.unop_op at hf ⊢,
    exact h hf, }
end

lemma op_isomorphisms_eq : (isomorphisms : arrow_class C).op = isomorphisms :=
by { ext f, exact is_iso_unop_iff f.hom, }

lemma op_epimorphisms_eq : (epimorphisms : arrow_class C).op = monomorphisms :=
begin
  ext f,
  split,
  { intro h,
    haveI : epi f.unop.hom := h,
    exact category_theory.op_mono_of_epi f.unop.hom, },
  { intro h,
    haveI : mono f.hom := h,
    exact category_theory.unop_epi_of_mono f.hom, },
end

lemma op_monomorphisms_eq : (monomorphisms : arrow_class C).op = epimorphisms :=
begin
  ext f,
  split,
  { intro h,
    haveI : mono f.unop.hom := h,
    exact category_theory.op_epi_of_mono f.unop.hom, },
  { intro h,
    haveI : epi f.hom := h,
    exact category_theory.unop_mono_of_epi f.hom, },
end

lemma isomorphisms_subset_iff_op : isomorphisms ⊆ F ↔ isomorphisms ⊆ F.op :=
begin
  rw subset_iff_op isomorphisms F,
  convert iff.rfl,
  rw op_isomorphisms_eq,
end

def is_stable_by_composition : Prop :=
  ∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F

lemma is_stable_by_composition_iff_op : F.is_stable_by_composition ↔ F.op.is_stable_by_composition :=
begin
  split,
  { intros hF X Y Z f g hf hg,
    rw mem_op_iff at hf hg ⊢,
    exact hF _ _ _ g.unop f.unop hg hf, },
  { intros hF X Y Z f g hf hg,
    rw ← (arrow.mk _).unop_op at ⊢ hf hg,
    rw ← mem_op_iff at hf hg ⊢,
    exact hF _ _ _  g.op f.op hg hf, }
end

lemma iso_comp_stable: (isomorphisms : arrow_class C).is_stable_by_composition :=
begin
  intros X Y Z f g hf hg,
  rw mem_isomorphisms_iff at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply_instance,
end

lemma imp_of_arrow_iso (F : arrow_class C) (h₁ : F.is_stable_by_composition) (h₂ : isomorphisms ⊆ F)
  {f₁ f₂ : arrow C} (e : f₁ ≅ f₂) (h₃ : f₁ ∈ F) : f₂ ∈ F :=
begin
  let e₁ := (comma.fst _ _).map_iso e,
  let e₂ := (comma.snd _ _).map_iso e,
  have h₄ := h₁ _ _ _ f₁.hom e₂.hom _ (h₂ _), rotate,
  { convert h₃, rw arrow.mk_eq, },
  { exact (is_iso.of_iso e₂), },
  convert h₁ _ _ _ e₁.inv _ (h₂ _) h₄, swap,
  { exact (is_iso.of_iso e₁.symm), },
  { simp only [← arrow.mk_eq f₂],
    congr,
    have h₅ := e.hom.w',
    dsimp at h₅,
    erw [← h₅, ← assoc, e₁.inv_hom_id, id_comp], },
end

def iff_of_arrow_iso (F : arrow_class C) := ∀ (f₁ f₂ : arrow C) (e : f₁ ≅ f₂), f₁ ∈ F ↔ f₂ ∈ F

namespace iff_of_arrow_iso

def of_comp_stable_and_contains_iso (F : arrow_class C)
  (h₁ : F.is_stable_by_composition) (h₂ : isomorphisms ⊆ F) :
  F.iff_of_arrow_iso :=
begin
  intros f₁ f₂ e,
  split,
  { exact F.imp_of_arrow_iso h₁ h₂ e, },
  { exact F.imp_of_arrow_iso h₁ h₂ e.symm, },
end

end iff_of_arrow_iso

def is_stable_by_retract (F : arrow_class C) : Prop := ∀ (f f' : arrow C),
  f' ∈ F → is_retract f f' → f ∈ F

lemma is_stable_by_retract_iff_op (F : arrow_class C) :
  is_stable_by_retract F ↔ is_stable_by_retract F.op :=
begin
  split,
  { intros h f f' hf' hff',
    rw mem_op_iff at ⊢ hf',
    apply h f.unop f'.unop hf',
    rw ← arrow.is_retract_iff_unop,
    exact hff', },
  { intros h f f' hf hff',
    rw [← arrow.unop_op f,← mem_op_iff],
    rw ← arrow.unop_op f' at hf,
    apply h f.op f'.op hf,
    rw ← arrow.is_retract_iff_op,
    exact hff', }
end

namespace is_stable_by_retract

def op {F : arrow_class C} := (is_stable_by_retract_iff_op F).mp
def unop {F : arrow_class C} := (is_stable_by_retract_iff_op F).mpr

def of_intersection (F G : arrow_class C)
  (hF : F.is_stable_by_retract) (hG : G.is_stable_by_retract) :
  (F ∩ G).is_stable_by_retract :=
begin
  rintros f f' ⟨h₁, h₂⟩ hff',
  split,
  { exact hF f f' h₁ hff', },
  { exact hG f f' h₂ hff', },
end

lemma for_isomorphisms :
  is_stable_by_retract (isomorphisms : arrow_class C) := λ f f' hf' hff',
begin
  rcases hf'.out with ⟨g, ⟨hg₁, hg₂⟩⟩,
  rcases hff' with ⟨s, r, hsr⟩,
  use s.right ≫ g ≫ r.left,
  split,
  { slice_lhs 1 2 { erw ← s.w, },
    slice_lhs 2 3 { rw hg₁, },
    rw id_comp,
    exact arrow.hom.congr_left hsr, },
  { slice_lhs 3 4 { erw r.w, },
    slice_lhs 2 3 { rw hg₂, },
    erw id_comp,
    exact arrow.hom.congr_right hsr, },
end

lemma for_monomorphisms :
  is_stable_by_retract (monomorphisms : arrow_class C) := λ f f' hf' hff',
begin
  rcases hff' with ⟨s, r, hsr⟩,
  refine ⟨_⟩,
  intros Z g₁ g₂ h,
  have hsr₁ := arrow.hom.congr_left hsr,
  simp only [comma.comp_right, arrow.id_right, comma.comp_left, arrow.id_left] at hsr₁,
  erw [← comp_id g₁, ← comp_id g₂, ← hsr₁, ← assoc, ← assoc],
  congr' 1,
  apply hf'.1,
  erw [assoc, assoc, s.w, ← assoc, ← assoc, h],
end

lemma for_epimorphisms :
  is_stable_by_retract (epimorphisms : arrow_class C) :=
begin
  rw [is_stable_by_retract_iff_op, op_epimorphisms_eq],
  apply for_monomorphisms,
end

end is_stable_by_retract

/- better this definition... -/
def is_stable_by_coproduct (F : arrow_class C) : Prop :=
∀ (J : Type*) (f : J → arrow C) (hl : has_coproduct (λ j, (f j).left))
  (hr : has_coproduct (λ j, (f j).right)),
  (∀ (j : J), f j ∈ F) → (@arrow.coproduct_cofan _ _ _ f hl hr).X ∈ F

def is_stable_by_binary_coproduct (F : arrow_class C) : Prop :=
∀ (f₁ f₂ : arrow C) [hl : has_binary_coproduct f₁.left f₂.left]
[hr : has_binary_coproduct f₁.right f₂.right],
  f₁ ∈ F → f₂ ∈ F → (@arrow.binary_coproduct_cofan _ _ f₁ f₂ hl hr).X ∈ F

def three_of_two_of_comp_left (F : arrow_class C) : Prop :=
∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk f ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk g ∈ F

def three_of_two_of_comp_right (F : arrow_class C) : Prop :=
∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    arrow.mk g ∈ F → arrow.mk (f ≫ g) ∈ F → arrow.mk f ∈ F

structure three_of_two (F : arrow_class C) : Prop :=
  (of_comp : F.is_stable_by_composition)
  (of_comp_left : F.three_of_two_of_comp_left)
  (of_comp_right : F.three_of_two_of_comp_right)

lemma three_of_two_of_comp_left_iff_op : F.three_of_two_of_comp_left ↔ F.op.three_of_two_of_comp_right :=
begin
  split,
  { intros hF X Y Z f g hfg hf,
    exact hF g.unop f.unop hfg hf, },
  { intros hF X Y Z f g hfg hg,
    exact hF g.op f.op hfg hg, }
end

lemma three_of_two_of_comp_right_iff_op : F.three_of_two_of_comp_right ↔ F.op.three_of_two_of_comp_left :=
begin
  split,
  { intros hF X Y Z f g hfg hg,
    exact hF g.unop f.unop hfg hg, },
  { intros hF X Y Z f g hfg hf,
    exact hF g.op f.op hfg hf, }
end

lemma three_of_two_iff (F : arrow_class C) : F.three_of_two ↔
F.is_stable_by_composition ∧ F.three_of_two_of_comp_left ∧ F.three_of_two_of_comp_right :=
begin
  split,
  { intro h,
    cases h,
    finish, },
  { rintro ⟨h₁, h₂, h₃⟩,
    dsimp [three_of_two_of_comp_left] at h₂,
    exact {
      of_comp := h₁,
      of_comp_left := λ _ _ _ , h₂,
      of_comp_right := λ _ _ _ , h₃, } }
end

lemma three_of_two_iff_op : F.three_of_two ↔ F.op.three_of_two :=
begin
  simp only [three_of_two_iff],
  rw [← is_stable_by_composition_iff_op, ← three_of_two_of_comp_left_iff_op,
    ← three_of_two_of_comp_right_iff_op],
  finish,
end

def is_stable_by_cobase_change :=
  ∀ (Sq : square C) (hSq : Sq.is_cocartesian),
  Sq.left ∈ F → Sq.right ∈ F

namespace is_stable_by_cobase_change

variable {F}
def down (hF : F.is_stable_by_cobase_change)
  (Sq : square C) (hSq : Sq.is_cocartesian) :
  Sq.top ∈ F → Sq.bottom ∈ F := hF _ hSq.flip

lemma for_pushout_inl (hF : F.is_stable_by_cobase_change)
  {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (f₂ : A₀ ⟶ A₂) (hf₂ : arrow.mk f₂ ∈ F) [has_pushout f₁ f₂] :
  arrow.mk (pushout.inl : A₁ ⟶ pushout f₁ f₂) ∈ F :=
hF _ (pushout_square_is_cocartesian f₁ f₂) hf₂

lemma for_pushout_inr (hF : F.is_stable_by_cobase_change)
  {A₀ A₁ A₂ : C} (f₁ : A₀ ⟶ A₁) (hf₁ : arrow.mk f₁ ∈ F) (f₂ : A₀ ⟶ A₂) [has_pushout f₁ f₂] :
  arrow.mk (pushout.inr : A₂ ⟶ pushout f₁ f₂) ∈ F :=
hF.down _ (pushout_square_is_cocartesian f₁ f₂) hf₁

lemma for_coprod_inl (hF : F.is_stable_by_cobase_change) [has_initial C]
  (A₁ A₂ : C) [has_binary_coproduct A₁ A₂]
  (hA₂ : arrow.mk (initial.to A₂) ∈ F) :
  (arrow.mk (coprod.inl : A₁ ⟶ coprod A₁ A₂)) ∈ F :=
hF _ (coprod_square_is_cocartesian _ _) hA₂

lemma for_coprod_inr (hF : F.is_stable_by_cobase_change) [has_initial C]
  (A₁ A₂ : C) [has_binary_coproduct A₁ A₂]
  (hA₁ : arrow.mk (initial.to A₁) ∈ F) :
  (arrow.mk (coprod.inr : A₂ ⟶ coprod A₁ A₂)) ∈ F :=
hF.down _ (coprod_square_is_cocartesian _ _) hA₁


end is_stable_by_cobase_change

def factorisation_axiom (F G : arrow_class C) :=
∀ (f : arrow C), ∃ (Z : C) (i : f.left ⟶ Z) (p : Z ⟶ f.right) (fac : f.hom = i ≫ p),
arrow.mk i ∈ F ∧ arrow.mk p ∈ G

lemma factorisation_axiom_iff_op (F G : arrow_class C) :
  factorisation_axiom F G ↔ factorisation_axiom G.op F.op :=
begin
  split,
  { intros h f,
    rcases h f.unop with ⟨Z, i, p, fac, ⟨r₁, r₂⟩⟩,
    use [opposite.op Z, p.op, i.op],
    split,
    { exact quiver.hom.unop_inj fac, },
    { simp only [mem_op_iff, arrow.unop_mk],
      exact ⟨r₂, r₁⟩, }, },
  { intros h f,
    rcases h f.op with ⟨Z, i, p, fac, ⟨r₁, r₂⟩⟩,
    use [opposite.unop Z, p.unop, i.unop],
    split,
    { exact quiver.hom.op_inj fac, },
    { simp only [mem_op_iff, arrow.unop_mk] at r₁ r₂,
      exact ⟨r₂, r₁⟩, }, },
end

namespace factorisation_axiom

def op {F G : arrow_class C} := (factorisation_axiom_iff_op F G).mp
def unop {F G : arrow_class C} := (factorisation_axiom_iff_op F G).mpr

end factorisation_axiom

end arrow_class

end category_theory
