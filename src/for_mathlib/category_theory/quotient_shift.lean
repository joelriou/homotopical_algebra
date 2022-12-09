import category_theory.shift
import for_mathlib.category_theory.quotient_misc

noncomputable theory

namespace category_theory

open category
#check has_shift

variables {C A : Type*} [category C] [add_monoid A] [has_shift C A] {r : hom_rel C}
  (h : ∀ (a : A) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y), r f₁ f₂ → r (f₁⟦a⟧') (f₂⟦a⟧'))

namespace quotient

@[protected]
def shift_functor (a : A) : quotient r ⥤ quotient r :=
lift r (shift_functor C a ⋙ functor r) (λ X Y f₁ f₂ rel, quotient.sound r (h a f₁ f₂ rel))

def comm_shift (a : A) :
  shift_functor C a ⋙ functor r ≅ functor r ⋙ quotient.shift_functor h a :=
(quotient.lift.is_lift _ _ _).symm

def shift_ε : 𝟭 _ ≅ quotient.shift_functor h 0 :=
quotient.lift_nat_iso _ _ (functor.right_unitor _ ≪≫ (functor.left_unitor _).symm ≪≫
      iso_whisker_right (shift_functor_zero C A).symm _ ≪≫ comm_shift h 0)

def shift_μ (a b : A) :
  quotient.shift_functor h a ⋙ quotient.shift_functor h b ≅
  quotient.shift_functor h (a + b) :=
quotient.lift_nat_iso _ _ ((functor.associator _ _ _).symm ≪≫
  iso_whisker_right (comm_shift h a).symm _ ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left _ (comm_shift h b).symm ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right (shift_functor_add C a b).symm _ ≪≫ comm_shift h (a + b))

lemma shift_associativity (a b c : A) :
  (shift_μ h a b).hom ◫ 𝟙 (quotient.shift_functor h c) ≫
    (shift_μ h (a + b) c).hom ≫ eq_to_hom (by rw add_assoc) =
  (functor.associator _ _ _).hom ≫ 𝟙 (quotient.shift_functor h a) ◫ (shift_μ h b c).hom ≫
    (shift_μ h a (b + c)).hom :=
begin
  sorry,
end

--local attribute [instance, reducible] endofunctor_monoidal_category
--local attribute [reducible] discrete.add_monoidal

lemma shift_left_unitality (a : A) :
  (shift_ε h).hom ◫ 𝟙 (quotient.shift_functor h a) ≫ (shift_μ h 0 a).hom =
    eq_to_hom (congr_arg (quotient.shift_functor h) (zero_add a).symm) :=
quotient.nat_trans_ext _ _ (λ X, begin
  sorry,
end)

lemma shift_right_unitality (a : A) :
  𝟙 (quotient.shift_functor h a) ◫ (shift_ε h).hom ≫ (shift_μ h a 0).hom =
    eq_to_hom (congr_arg (quotient.shift_functor h) (add_zero a).symm) :=
begin
  sorry,
end

@[protected]
def shift : has_shift (quotient r) A :=
has_shift_mk _ _
{ F := quotient.shift_functor h,
  ε := shift_ε h,
  μ := shift_μ h,
  associativity := λ a b c X, by simpa using congr_app (shift_associativity h a b c) X,
  left_unitality := λ a X, by simpa using congr_app (shift_left_unitality h a) X,
  right_unitality := λ a X, by simpa using congr_app (shift_right_unitality h a) X, }

end quotient

end category_theory
