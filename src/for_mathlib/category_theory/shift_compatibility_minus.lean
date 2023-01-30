import for_mathlib.category_theory.triangulated.shift_compatibility
import for_mathlib.category_theory.shift_misc

noncomputable theory

namespace category_theory

open category

variables (C : Type*) {A : Type*} [category C] [add_monoid A] [has_shift C A]

def shift_functor_add₃' (a₁ a₂ a₃ : A) (b : A) (h : b = a₁+a₂+a₃) :
  shift_functor C b ≅ shift_functor C a₁ ⋙
    shift_functor C a₂ ⋙ shift_functor C a₃ :=
shift_functor_add' C (a₁+a₂) a₃ b h ≪≫ iso_whisker_right (shift_functor_add C a₁ a₂) _ ≪≫ functor.associator _ _ _

variable {C}

lemma shift_functor_add₃'_hom_app (a₁ a₂ a₃ : A) (b : A) (h : b = a₁+a₂+a₃) (a₁₂ : A) (h₁₂ : a₁₂ = a₁ + a₂) (X : C) :
  (shift_functor_add₃' C a₁ a₂ a₃ b h).hom.app X =
    (shift_functor_add' C a₁₂ a₃ b (by rw [h₁₂, h])).hom.app X ≫
    ((shift_functor_add' C a₁ a₂ a₁₂ h₁₂).hom.app X)⟦a₃⟧' :=
begin
  substs h₁₂ h,
  dsimp only [shift_functor_add₃', iso.trans, iso_whisker_right,
    functor.associator, nat_trans.comp_app, whiskering_right,
    functor.map_iso, whisker_right],
  simp only [comp_id, shift_functor_add'_eq_shift_functor_add],
end

lemma shift_functor_add₃'_inv_app (a₁ a₂ a₃ : A) (b : A) (h : b = a₁+a₂+a₃) (a₁₂ : A) (h₁₂ : a₁₂ = a₁ + a₂) (X : C) :
  (shift_functor_add₃' C a₁ a₂ a₃ b h).inv.app X =
    ((shift_functor_add' C a₁ a₂ a₁₂ h₁₂).inv.app X)⟦a₃⟧' ≫
    (shift_functor_add' C a₁₂ a₃ b (by rw [h₁₂, h])).inv.app X :=
begin
  substs h₁₂ h,
  dsimp only [shift_functor_add₃', iso.trans, iso_whisker_right,
    functor.associator, nat_trans.comp_app, whiskering_right,
    functor.map_iso, whisker_right],
  simp only [id_comp, shift_functor_add'_eq_shift_functor_add],
end

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

lemma shift_functor_add₃'_hom_app' (a₁ a₂ a₃ : A) (b : A) (h : b = a₁+a₂+a₃) (a₂₃ : A) (h₂₃ : a₂₃ = a₂ + a₃) (X : C) :
  (shift_functor_add₃' C a₁ a₂ a₃ b h).hom.app X =
  (shift_functor_add' C a₁ a₂₃ b (by rw [h, h₂₃, add_assoc])).hom.app _ ≫
    (shift_functor_add' C a₂ a₃ a₂₃ h₂₃).hom.app (X⟦a₁⟧) :=
begin
  subst h₂₃,
  simp only [shift_functor_add₃'_hom_app a₁ a₂ a₃ b h (a₁+a₂) rfl,
    shift_functor_add'_eq_shift_functor_add],
  have h : b = a₁+(a₂+a₃) := by rw [h, add_assoc],
  subst h,
  rw shift_functor_add'_eq_shift_functor_add,
  have eq := congr_arg iso.inv (monoidal_functor.associativity_iso_eq (shift_monoidal_functor C A)
    (discrete.mk a₁) (discrete.mk a₂) (discrete.mk a₃)),
  replace eq := congr_app eq X,
  dsimp [shift_functor_add'] at eq ⊢,
  simpa only [assoc, id_comp, comp_id,
    functor.map_id, eq_to_hom_map] using eq,
end

lemma shift_functor_add₃'_inv_app' (a₁ a₂ a₃ : A) (b : A) (h : b = a₁+a₂+a₃) (a₂₃ : A) (h₂₃ : a₂₃ = a₂ + a₃) (X : C) :
  (shift_functor_add₃' C a₁ a₂ a₃ b h).inv.app X =
  (shift_functor_add' C a₂ a₃ a₂₃ h₂₃).inv.app (X⟦a₁⟧) ≫
  (shift_functor_add' C a₁ a₂₃ b (by rw [h, h₂₃, add_assoc])).inv.app _ :=
begin
  simp only [← cancel_mono ((shift_functor_add₃' C a₁ a₂ a₃ b h).hom.app X),
    iso.inv_hom_id_app, assoc],
  subst h₂₃,
  simpa only [shift_functor_add₃'_hom_app' _ _ _ _ h _ rfl,
    iso.inv_hom_id_app_assoc, iso.inv_hom_id_app],
end

end category_theory
