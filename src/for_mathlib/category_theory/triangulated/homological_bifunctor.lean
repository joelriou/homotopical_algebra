import for_mathlib.category_theory.triangulated.homological_functor
import for_mathlib.category_theory.shift_op

noncomputable theory

namespace category_theory

open category limits

namespace functor

variables {C₁ C₂ D : Type*} [category C₁] [category C₂] [category D]

section

variables (F : C₁ ⥤ C₂ ⥤ D) {A : Type*} [add_comm_monoid A]
  [has_shift C₁ A] [has_shift C₂ A]

def shift_swap (a : A) :=
  (shift_functor C₁ a) ⋙ F ≅ F ⋙ (whiskering_left _ _ D).obj (shift_functor C₂ a)

namespace shift_swap

variable (A)

def zero : shift_swap F (0 : A) :=
iso_whisker_right (shift_functor_zero C₁ A) F ≪≫ F.left_unitor ≪≫
  F.right_unitor.symm ≪≫
  iso_whisker_left F ((whiskering_left_id _ _).symm ≪≫
    (whiskering_left _ _ D).map_iso (shift_functor_zero C₂ A).symm)

lemma zero_hom_app_app (X₁ : C₁) (X₂ : C₂) :
  ((zero F A).hom.app X₁).app X₂ =
  (F.map ((shift_functor_zero C₁ A).hom.app X₁)).app X₂ ≫
    (F.obj X₁).map ((shift_functor_zero C₂ A).inv.app X₂) :=
begin
  dsimp only [zero, left_unitor, right_unitor, iso.trans, iso_whisker_right, iso_whisker_left,
    whiskering_right, whiskering_left, iso.symm, nat_trans.comp_app, whiskering_left_id,
    nat_iso.of_components, map_iso, whisker_left, whisker_right],
  erw [id_comp, id_comp, id_comp],
end

lemma zero_inv_app_app (X₁ : C₁) (X₂ : C₂) :
  ((zero F A).inv.app X₁).app X₂ =
  (F.obj X₁).map ((shift_functor_zero C₂ A).hom.app X₂) ≫
  (F.map ((shift_functor_zero C₁ A).inv.app X₁)).app X₂ :=
begin
  dsimp only [zero, left_unitor, right_unitor, iso.trans, iso_whisker_right, iso_whisker_left,
    whiskering_right, whiskering_left, iso.symm, nat_trans.comp_app, whiskering_left_id,
    nat_iso.of_components, map_iso, whisker_left, whisker_right],
  erw [comp_id, comp_id, comp_id],
end

variables {F A}

def add' {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b) (c : A) (h : c = a+b) :
  shift_swap F c :=
iso_whisker_right (shift_functor_add' C₁ a b c h) F ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left _ e₂ ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right e₁ _ ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left F ((whiskering_left _ _ D).map_iso
    (shift_functor_add' C₂ b a c (by rw [h, add_comm])).symm)

def add {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b) :
  shift_swap F (a+b) := add' e₁ e₂ (a+b) rfl

lemma add'_hom_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (c : A) (h : c = a+b) (X₁ : C₁) (X₂ : C₂) :
  ((add' e₁ e₂ c h).hom.app X₁).app X₂ =
    (F.map ((shift_functor_add' C₁ a b c h).hom.app X₁)).app X₂ ≫
    (e₂.hom.app (X₁⟦a⟧)).app X₂ ≫ (e₁.hom.app X₁).app (X₂⟦b⟧) ≫
    (F.obj X₁).map ((shift_functor_add' C₂ b a c (by rw [h, add_comm])).inv.app X₂) :=
begin
  dsimp [add'],
  erw [id_comp, id_comp, id_comp],
end

lemma add_hom_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
   (X₁ : C₁) (X₂ : C₂) :
  ((add e₁ e₂).hom.app X₁).app X₂ =
    (F.map ((shift_functor_add C₁ a b).hom.app X₁)).app X₂ ≫
    (e₂.hom.app (X₁⟦a⟧)).app X₂ ≫ (e₁.hom.app X₁).app (X₂⟦b⟧) ≫
    (F.obj X₁).map
      ((shift_functor_add' C₂ b a (a+b) (add_comm a b)).inv.app X₂) :=
begin
  dsimp only [add],
  rw [add'_hom_app_app, shift_functor_add'_eq_shift_functor_add],
end

lemma add'_inv_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (c : A) (h : c = a+b) (X₁ : C₁) (X₂ : C₂) :
  ((add' e₁ e₂ c h).inv.app X₁).app X₂ =
    (F.obj X₁).map ((shift_functor_add' C₂ b a c (by rw [h, add_comm])).hom.app X₂) ≫
    (e₁.inv.app X₁).app (X₂⟦b⟧) ≫
    (e₂.inv.app (X₁⟦a⟧)).app X₂ ≫
    (F.map ((shift_functor_add' C₁ a b c h).inv.app X₁)).app X₂ :=
begin
  dsimp [add'],
  erw [comp_id, comp_id, comp_id, assoc, assoc],
end

lemma add_inv_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (X₁ : C₁) (X₂ : C₂) :
  ((add e₁ e₂).inv.app X₁).app X₂ =
    (F.obj X₁).map ((shift_functor_add' C₂ b a _ (add_comm a b)).hom.app X₂) ≫
    (e₁.inv.app X₁).app (X₂⟦b⟧) ≫
    (e₂.inv.app (X₁⟦a⟧)).app X₂ ≫
    (F.map ((shift_functor_add C₁ a b).inv.app X₁)).app X₂ :=
begin
  dsimp only [add],
  rw [add'_inv_app_app, shift_functor_add'_eq_shift_functor_add],
end

end shift_swap

variable (A)

class has_shift_swap :=
(iso : Π (a : A), F.shift_swap a)
(iso_zero : iso 0 = shift_swap.zero F A)
(iso_add : ∀ (a b : A), iso (a+b) = shift_swap.add (iso a) (iso b))

variable {A}

def shift_cancel (a : A) :=
  (shift_functor C₁ a) ⋙ F ⋙ (whiskering_left _ _ D).obj (shift_functor C₂ a) ≅ F

namespace shift_cancel

variable (A)

def zero : shift_cancel F (0 : A) :=
iso_whisker_right (shift_functor_zero C₁ A) _ ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right (F.left_unitor) _ ≪≫
  iso_whisker_left F ((whiskering_left _ _ D).map_iso (shift_functor_zero C₂ A)) ≪≫
  iso_whisker_left F (whiskering_left_id _ _) ≪≫ F.right_unitor

variables {F A} {a b : A} (e₁ : shift_cancel F a) (e₂ : shift_cancel F b)

def add' (c : A) (h : c = a+b) :
  shift_cancel F c :=
iso_whisker_right (shift_functor_add' C₁ a b c h) _ ≪≫
  iso_whisker_left _ (iso_whisker_left _ ((whiskering_left _ _ D).map_iso (shift_functor_add' C₂ a b c h))) ≪≫ (by refl) ≪≫ iso_whisker_left _ (iso_whisker_right e₂ _) ≪≫ e₁

def add : shift_cancel F (a+b) := add' e₁ e₂ (a+b) rfl

end shift_cancel

variables (F A)

class has_shift_cancel :=
(iso : Π (a : A), F.shift_cancel a)
(iso_zero : iso 0 = shift_cancel.zero F A)
(iso_add : ∀ (a b : A), iso (a+b) = shift_cancel.add (iso a) (iso b))

end

section

variables {C : Type*} [category C] [has_shift C ℤ] [preadditive C]

local attribute [instance] has_shift_op_neg_ℤ

variable (C)

/-def yoneda_shift_swap (n : ℤ) : shift_swap (yoneda : C ⥤ _) n :=
nat_iso.of_components (λ X₁, nat_iso.of_components (λ X₂, begin
    dsimp,
    sorry,
  end)
  sorry) sorry
#exit

lemma hom_functor_has_shift_swap : (yoneda : C ⥤ _).has_shift_swap ℤ :=
{ iso := yoneda_shift_swap C,
  iso_zero := sorry,
  iso_add := sorry, }-/

end

end functor

end category_theory
