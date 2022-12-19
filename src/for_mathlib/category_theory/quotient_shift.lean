import category_theory.shift
import for_mathlib.category_theory.quotient_misc

noncomputable theory

namespace category_theory

open category

variables {C A : Type*} [category C] (r : hom_rel C)

lemma quotient.functor_map_eq {X Y : C} (f : X ⟶ Y) :
  (quotient.functor r).map f = quot.mk _ f := rfl

variables [add_monoid A] [has_shift C A]
  (h : ∀ (a : A) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y), r f₁ f₂ → r (f₁⟦a⟧') (f₂⟦a⟧'))

variable {r}

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

--local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal
local attribute [-simp] lift_map

lemma shift_associativity (a b c : A) :
  (shift_μ h a b).hom ◫ 𝟙 (quotient.shift_functor h c) ≫
    (shift_μ h (a + b) c).hom ≫ eq_to_hom (by rw add_assoc) =
  (functor.associator _ _ _).hom ≫ 𝟙 (quotient.shift_functor h a) ◫ (shift_μ h b c).hom ≫
    (shift_μ h a (b + c)).hom :=
quotient.nat_trans_ext _ _ (λ X, begin
  dsimp only [shift_ε, shift_μ, quotient.shift_functor, comm_shift],
  simp only [iso.symm_symm_eq, lift_nat_iso_hom, iso.trans_hom, iso.symm_hom,
    iso_whisker_right_hom, iso_whisker_left_hom, monoidal_functor.μ_iso_hom, nat_trans.comp_app,
    lift_nat_trans_app, functor.associator_inv_app, whisker_right_app, lift.is_lift_hom,
    functor.associator_hom_app, whisker_left_app, functor_map, lift.is_lift_inv, comp_id, id_comp,
    functor.map_comp, eq_to_hom_app, assoc, nat_trans.hcomp_app, nat_trans.id_app, functor.map_id],
  erw [functor.map_id, functor.map_id, functor.map_id, functor.map_id, comp_id, id_comp,
    id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp],
  sorry,
end)

lemma shift_left_unitality (a : A) :
  (shift_ε h).hom ◫ 𝟙 (quotient.shift_functor h a) ≫ (shift_μ h 0 a).hom =
    eq_to_hom (congr_arg (quotient.shift_functor h) (zero_add a).symm) :=
quotient.nat_trans_ext _ _ (λ X, begin
  dsimp [shift_ε, shift_μ, comm_shift],
  simp only [comp_id, id_comp, eq_to_hom_app],
  erw [functor.map_id, id_comp, id_comp],
  dsimp [quotient.shift_functor, lift_map],
  erw [← functor_map_eq, ← functor_map_eq, ← functor.map_comp],
  transitivity (functor r).map (eq_to_hom _), swap,
  { rw zero_add, },
  { congr' 1,
    simp only [obj_ε_app, eq_to_iso.inv, assoc, μ_inv_hom_app],
    erw [comp_id, eq_to_hom_map, eq_to_hom_app], },
  { apply eq_to_hom_map, },
end)

lemma shift_right_unitality (a : A) :
  𝟙 (quotient.shift_functor h a) ◫ (shift_ε h).hom ≫ (shift_μ h a 0).hom =
    eq_to_hom (congr_arg (quotient.shift_functor h) (add_zero a).symm) :=
quotient.nat_trans_ext _ _ (λ X, begin
  dsimp only [shift_ε, shift_μ, iso.trans, nat_trans.hcomp, nat_trans.comp_app,
    quotient.shift_functor, comm_shift, lift.is_lift],
  simp only [iso.symm_inv, assoc, iso.symm_hom, iso_whisker_right_hom, lift_nat_iso_hom,
    nat_trans.id_app, lift_nat_trans_app, nat_trans.comp_app, whisker_right_app, functor.map_id,
    nat_iso.of_components_hom_app, iso.refl_hom, nat_iso.of_components_inv_app, iso.refl_inv],
  dsimp,
  simp only [id_comp, comp_id, eq_to_hom_app],
  erw [← functor_map_eq, ← functor_map_eq, ← functor.map_comp],
  transitivity (functor r).map (eq_to_hom _), swap,
  { rw add_zero, },
  { congr' 1,
    simp only [ε_app_obj, eq_to_iso.inv, assoc, μ_inv_hom_app, comp_id,
      eq_to_hom_map, eq_to_hom_app], },
  { apply eq_to_hom_map, },
end)

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
