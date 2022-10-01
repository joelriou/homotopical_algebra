import category_theory.shift

noncomputable theory

namespace category_theory

open category

variables (C : Type*) {A : Type*} [category C] [add_monoid A] [has_shift C A]

def shift_functor_zero' {a : A} (ha : a = 0) : shift_functor C a ≅ 𝟭 _ :=
by { subst ha, exact shift_functor_zero C A, }

def shift_functor_add' {a₁ a₂ s : A} (h : a₁ + a₂ = s) :
  shift_functor C s ≅ shift_functor C a₁ ⋙ shift_functor C a₂ :=
by { subst h, exact shift_functor_add C a₁ a₂, }

lemma shift_functor_add'_eq {a₁ a₂ s : A} (h : a₁ + a₂ = s) :
  shift_functor_add' C h = eq_to_iso (by rw h) ≪≫
    shift_functor_add C a₁ a₂ :=
begin
  subst h,
  ext1,
  simpa only [iso.trans_hom, eq_to_iso_refl, iso.refl_hom, id_comp],
end

include C A

local attribute [reducible] discrete.add_monoidal endofunctor_monoidal_category

lemma shift_functor_assoc' {a₁ a₂ a₃ a₁₂ a₂₃ s : A} (h₁₂₃ : a₁ + a₂ + a₃ = s)
  (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) :
  (shift_functor_add' C (show a₁₂ + a₃ = s, by rw [← h₁₂, h₁₂₃])) ≪≫
    iso_whisker_right (shift_functor_add' C h₁₂) _ ≪≫ functor.associator _ _ _ =
  (shift_functor_add' C (show a₁ + a₂₃ = s, by rw [← h₂₃, ← add_assoc, h₁₂₃]))
    ≪≫ iso_whisker_left _ (shift_functor_add' C h₂₃) :=
begin
  ext1,
  rw ← cancel_mono (iso_whisker_left (shift_functor C a₁) (shift_functor_add' C h₂₃)).inv,
  substs h₁₂ h₂₃ h₁₂₃,
  ext X,
  simp only [shift_functor_add'_eq],
  sorry,
end

end category_theory
