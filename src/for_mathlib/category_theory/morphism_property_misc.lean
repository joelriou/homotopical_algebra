import category_theory.morphism_property
import for_mathlib.category_theory.limits.comm_sq_misc

open category_theory.limits

universes w v u

namespace category_theory

variables {C : Type u} [category.{v} C] {D : Type*} [category D]

namespace morphism_property

/-instance : has_subset (morphism_property C) :=
⟨λ P₁ P₂, ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P₁ f), P₂ f⟩
instance : has_inter (morphism_property C) :=
⟨λ P₁ P₂ X Y f, P₁ f ∧ P₂ f⟩

@[simp] def op (P : morphism_property C) : morphism_property Cᵒᵖ := λ X Y f, P f.unop
@[simp] def unop (P : morphism_property Cᵒᵖ) : morphism_property C := λ X Y f, P f.op
@[simp] lemma unop_op (P : morphism_property C) : P.op.unop = P := rfl
@[simp] lemma op_unop (P : morphism_property Cᵒᵖ) : P.unop.op = P := rfl

/-- A morphism property is `stable_under_cobase_change` if the cobase change of such a morphism
still falls in the class. -/
def stable_under_cobase_change (P : morphism_property C) : Prop :=
∀ ⦃A A' B B' : C⦄ ⦃f : A ⟶ A'⦄ ⦃g : A ⟶ B⦄ ⦃f' : B ⟶ B'⦄ ⦃g' : A' ⟶ B'⦄
  (sq : is_pushout g f f' g') (hf : P f), P f'

lemma stable_under_cobase_change.mk {P : morphism_property C} [has_pushouts C]
  (hP₁ : respects_iso P)
  (hP₂ : ∀ (A B A' : C) (f : A ⟶ A') (g : A ⟶ B) (hf : P f), P (pushout.inr : B ⟶ pushout f g)) :
  stable_under_cobase_change P := λ A A' B B' f g f' g' sq hf,
begin
  let e := sq.flip.iso_pushout,
  rw [← hP₁.cancel_right_is_iso _ e.hom, sq.flip.inr_iso_pushout_hom],
  exact hP₂ _ _ _ f g hf,
end

lemma stable_under_cobase_change.respects_iso {P : morphism_property C}
  (hP : stable_under_cobase_change P) : respects_iso P :=
begin
  apply respects_iso.of_respects_arrow_iso,
  intros f g e,
  exact hP (is_pushout.of_horiz_is_iso (comm_sq.mk e.hom.w)),
end

lemma stable_under_cobase_change.inl {P : morphism_property C}
  (hP : stable_under_cobase_change P) {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [has_pushout f g]
  (H : P g) : P (pushout.inl : A' ⟶ pushout f g) :=
hP (is_pushout.of_has_pushout f g) H

lemma stable_under_cobase_change.inr {P : morphism_property C}
  (hP : stable_under_cobase_change P) {A B A' : C} (f : A ⟶ A') (g : A ⟶ B) [has_pushout f g]
  (H : P f) : P (pushout.inr : B ⟶ pushout f g) :=
hP (is_pushout.of_has_pushout f g).flip H

lemma stable_under_cobase_change.op {P : morphism_property C}
  (hP : stable_under_cobase_change P) : stable_under_base_change P.op :=
λ X Y Y' S f g f' g' sq hg, hP sq.unop hg

lemma stable_under_cobase_change.unop {P : morphism_property Cᵒᵖ}
  (hP : stable_under_cobase_change P) : stable_under_base_change P.unop :=
λ X Y Y' S f g f' g' sq hg, hP sq.op hg

lemma stable_under_base_change.op {P : morphism_property C}
  (hP : stable_under_base_change P) : stable_under_cobase_change P.op :=
λ A A' B B' f g f' g' sq hf, hP sq.unop hf

lemma stable_under_base_change.unop {P : morphism_property Cᵒᵖ}
  (hP : stable_under_base_change P) : stable_under_cobase_change P.unop :=
λ A A' B B' f g f' g' sq hf, hP sq.op hf

def inverse_image (P : morphism_property D) (F : C ⥤ D) : morphism_property C :=
λ X Y f, P (F.map f)

variable (C)
def isomorphisms : morphism_property C := λ X Y f, is_iso f
def monomorphisms : morphism_property C := λ X Y f, mono f
def epimorphisms : morphism_property C := λ X Y f, epi f

variable {C}

section
variables {X Y : C} (f : X ⟶ Y)
@[simp] lemma isomorphisms.iff : (isomorphisms C) f ↔ is_iso f := by refl
@[simp] lemma monomorphisms.iff : (monomorphisms C) f ↔ mono f := by refl
@[simp] lemma epimorphisms.iff : (epimorphisms C) f ↔ epi f := by refl

lemma isomorphisms.infer_property [hf : is_iso f] : (isomorphisms C) f := hf
lemma monomorphisms.infer_property [hf : mono f] : (monomorphisms C) f := hf
lemma epimorphisms.infer_property [hf : epi f] : (epimorphisms C) f := hf

end-/

variable (C)
@[simp]
lemma op_epimorphisms : (epimorphisms C).op = monomorphisms Cᵒᵖ :=
begin
  ext X Y f,
  simp only [morphism_property.op, epimorphisms.iff, monomorphisms.iff],
  split,
  { introI,
    exact category_theory.op_mono_of_epi f.unop, },
  { introI,
    exact category_theory.unop_epi_of_mono f, },
end

@[simp]
lemma op_monomorphisms : (monomorphisms C).op = epimorphisms Cᵒᵖ :=
begin
  ext X Y f,
  simp only [morphism_property.op, epimorphisms.iff, monomorphisms.iff],
  split,
  { introI,
    exact category_theory.op_epi_of_mono f.unop, },
  { introI,
    exact category_theory.unop_mono_of_epi f, },
end

@[simp]
lemma unop_epimorphisms : (epimorphisms Cᵒᵖ).unop = monomorphisms C :=
by rw [← (monomorphisms C).unop_op, op_monomorphisms]

@[simp]
lemma unop_monomorphisms : (monomorphisms Cᵒᵖ).unop = epimorphisms C :=
by rw [← (epimorphisms C).unop_op, op_epimorphisms]

namespace stable_under_composition

variable {C}
/-
lemma op {P : morphism_property C} (h : P.stable_under_composition) :
  P.op.stable_under_composition :=
λ X Y Z f g hf hg, h g.unop f.unop hg hf

lemma unop {P : morphism_property Cᵒᵖ} (h : P.stable_under_composition) :
  P.unop.stable_under_composition :=
λ X Y Z f g hf hg, h g.op f.op hg hf

lemma inverse_image {P : morphism_property D} (h : P.stable_under_composition)
  (F : C ⥤ D) : (P.inverse_image F).stable_under_composition :=
λ X Y Z f g hf hg, by simpa only [← F.map_comp] using h (F.map f) (F.map g) hf hg-/

variable (C)

/-lemma for_isomorphisms : (isomorphisms C).stable_under_composition :=
λ X Y Z f g hf hg, begin
  dsimp [isomorphisms] at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply_instance,
end

lemma for_monomorphisms : (monomorphisms C).stable_under_composition :=
λ X Y Z f g hf hg, begin
  dsimp [monomorphisms] at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply mono_comp,
end

lemma for_epimorphisms : (epimorphisms C).stable_under_composition :=
λ X Y Z f g hf hg, begin
  dsimp [epimorphisms] at hf hg ⊢,
  haveI := hf,
  haveI := hg,
  apply epi_comp,
end-/

end stable_under_composition

namespace respects_iso

/-lemma op {P : morphism_property C} (h : P.respects_iso) :
  P.op.respects_iso :=
⟨λ X Y Z e f, h.2 e.unop f.unop, λ X Y Z e f, h.1 e.unop f.unop⟩

lemma unop {P : morphism_property Cᵒᵖ} (h : P.respects_iso) :
  P.unop.respects_iso :=
⟨λ X Y Z e f, h.2 e.op f.op, λ X Y Z e f, h.1 e.op f.op⟩

lemma for_monomorphisms : (monomorphisms C).respects_iso :=
by { split; { intros X Y Z e f, simp only [monomorphisms.iff], introI, apply mono_comp, }, }

lemma for_epimorphisms : (epimorphisms C).respects_iso :=
by { split; { intros X Y Z e f, simp only [epimorphisms.iff], introI, apply epi_comp, }, }

lemma for_isomorphisms : (isomorphisms C).respects_iso :=
by { split; { intros X Y Z e f, simp only [isomorphisms.iff], introI, apply_instance, }, }
-/
end respects_iso

variable {C}

lemma respects_iso.of_stable_under_composition_and_contains_iso
  {P : morphism_property C} (h₁ : P.stable_under_composition) (h₂ : isomorphisms C ⊆ P) :
  respects_iso P :=
begin
  split,
  { intros X Y Z e f hf,
    exact h₁ e.hom f (h₂ e.hom (isomorphisms.infer_property _)) hf, },
  { intros X Y Z e f hf,
    exact h₁ f e.hom hf (h₂ e.hom (isomorphisms.infer_property _)), },
end

def stable_under_products (P : morphism_property C) : Prop :=
P.respects_iso ∧
∀ (I : Type w) (X : I → C) (Y : I → C) [hX : has_product X] [hY : has_product Y]
(f : Π (i : I), X i ⟶ Y i) (hf : ∀ (i : I), P (f i)), P (@limits.pi.map _ _ _ X Y hX hY f)

namespace stable_under_products

lemma property {P : morphism_property C} (h : morphism_property.stable_under_products.{w} P)
  {I : Type w} (X : I → C) (Y : I → C) [hX : has_product X] [hY : has_product Y]
(f : Π (i : I), X i ⟶ Y i) (hf : ∀ (i : I), P (f i)) :
  P (@limits.pi.map _ _ _ X Y hX hY f) :=
h.2 I X Y f hf

lemma binary {P : morphism_property C} (h : morphism_property.stable_under_products.{0} P)
  {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (h₁ : P f₁) (f₂ : X₂ ⟶ Y₂) (h₂ : P f₂)
  [hX : has_binary_product X₁ X₂] [hY : has_binary_product Y₁ Y₂] :
  P (limits.prod.map f₁ f₂) :=
begin
  haveI : has_product (pair_function X₁ X₂) := hX,
  haveI : has_product (pair_function Y₁ Y₂) := hY,
  convert h.property (pair_function X₁ X₂) (pair_function Y₁ Y₂)
    (λ i, by { cases i, exacts [f₁, f₂], })
    (λ i, by { cases i, exacts [h₁, h₂], }),
  ext,
  { erw [limits.prod.map_fst, lim_map_π], refl, },
  { erw [limits.prod.map_snd, lim_map_π], refl, },
end

end stable_under_products

def stable_under_coproducts (P : morphism_property C) : Prop :=
P.respects_iso ∧
∀ (I : Type w) (X : I → C) (Y : I → C) [hX : has_coproduct X] [hY : has_coproduct Y]
(f : Π (i : I), X i ⟶ Y i) (hf : ∀ (i : I), P (f i)), P (@limits.sigma.map _ _ _ X Y hX hY f)

namespace stable_under_coproducts

lemma property {P : morphism_property C} (h : morphism_property.stable_under_coproducts.{w} P)
  (I : Type w) (X : I → C) (Y : I → C) [hX : has_coproduct X] [hY : has_coproduct Y]
  (f : Π (i : I), X i ⟶ Y i) (hf : ∀ (i : I), P (f i)) :
  P (@limits.sigma.map _ _ _ X Y hX hY f) :=
h.2 I X Y f hf

lemma binary {P : morphism_property C} (h : morphism_property.stable_under_coproducts.{0} P)
  {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (h₁ : P f₁) (f₂ : X₂ ⟶ Y₂) (h₂ : P f₂)
  [hX : has_binary_coproduct X₁ X₂] [hY : has_binary_coproduct Y₁ Y₂] :
  P (coprod.map f₁ f₂) :=
begin
  haveI : has_coproduct (pair_function X₁ X₂) := hX,
  haveI : has_coproduct (pair_function Y₁ Y₂) := hY,
  convert h.property _ (pair_function X₁ X₂) (pair_function Y₁ Y₂)
    (λ i, by { cases i, exacts [f₁, f₂], })
    (λ i, by { cases i, exacts [h₁, h₂], }),
  tidy,
end

end stable_under_coproducts
/-
lemma is_inverted_by.of_comp {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃]
  (W : morphism_property C₁) (F : C₁ ⥤ C₂) (hF : W.is_inverted_by F) (G : C₂ ⥤ C₃) :
  W.is_inverted_by (F ⋙ G) :=
λ X Y f hf, by { haveI := hF f hf, dsimp, apply_instance, }-/

/- better as .of_iso rather that iff_of_iso -/

/-
lemma is_inverted_by.iff_of_iso (W : morphism_property C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
  W.is_inverted_by F₁ ↔ W.is_inverted_by F₂ :=
begin
  suffices : ∀ (X Y : C) (f : X ⟶ Y), is_iso (F₁.map f) ↔ is_iso (F₂.map f),
  { split,
    exact λ h X Y f hf, by { rw ← this, exact h f hf, },
    exact λ h X Y f hf, by { rw this, exact h f hf, }, },
  intros X Y f,
  apply (respects_iso.isomorphisms D).arrow_mk_iso_iff,
  exact arrow.iso_mk (e.app X) (e.app Y) (by simp),
end-/

end morphism_property

end category_theory
