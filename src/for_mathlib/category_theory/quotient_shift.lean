import category_theory.shift
import for_mathlib.category_theory.quotient_misc
import for_mathlib.category_theory.functor.shift

import for_mathlib.category_theory.functor.shift_compatibility

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

@[simp]
lemma comm_shift_hom_app (a : A) (X : C) :
  (comm_shift h a).hom.app X = 𝟙 _ := rfl

@[simp]
lemma comm_shift_inv_app (a : A) (X : C) :
  (comm_shift h a).inv.app X = 𝟙 _ := rfl

def shift_ε : 𝟭 _ ≅ quotient.shift_functor h 0 :=
quotient.lift_nat_iso _ _ (functor.right_unitor _ ≪≫ (functor.left_unitor _).symm ≪≫
      iso_whisker_right (shift_functor_zero C A).symm _ ≪≫ comm_shift h 0)

@[simp]
lemma shift_ε_hom_app (X : C) :
  (shift_ε h).hom.app ((functor r).obj X) =
    (functor r).map ((shift_functor_zero C A).inv.app X) :=
begin
  dsimp [shift_ε],
  simp only [id_comp, comp_id],
end

def shift_μ (a b : A) :
  quotient.shift_functor h a ⋙ quotient.shift_functor h b ≅
  quotient.shift_functor h (a + b) :=
quotient.lift_nat_iso _ _ ((functor.associator _ _ _).symm ≪≫
  iso_whisker_right (comm_shift h a).symm _ ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left _ (comm_shift h b).symm ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right (shift_functor_add C a b).symm _ ≪≫ comm_shift h (a + b))

@[simp]
lemma shift_μ_hom_app (a b : A) (X : C) :
  (shift_μ h a b).hom.app ((functor r).obj X) =
    (functor r).map ((shift_functor_add C a b).inv.app X) :=
begin
  dsimp [shift_μ],
  simpa only [functor.map_id, comp_id, id_comp],
end

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

lemma associativity_compatibility (a b c : A) (X : C) :
  (shift_functor C c).map ((shift_functor_add C a b).inv.app X) ≫
    (shift_functor_add C (a + b) c).inv.app X =
  (shift_functor_add C b c).inv.app ((shift_functor C a).obj X) ≫
  (shift_functor_add C a (b + c)).inv.app X ≫ eq_to_hom (by rw add_assoc):=
begin
  dsimp,
  have eq := (congr_arg iso.hom (monoidal_functor.associativity_iso_eq
    (shift_monoidal_functor C A) (discrete.mk a) (discrete.mk b) (discrete.mk c))),
  replace eq := congr_app eq X,
  dsimp at eq,
  simp only [id_comp, functor.map_id, comp_id] at eq,
  erw ← reassoc_of eq, clear eq,
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_hom_trans, eq_to_hom_refl, comp_id],
end

lemma shift_associativity (a b c : A) :
  (shift_μ h a b).hom ◫ 𝟙 (quotient.shift_functor h c) ≫
    (shift_μ h (a + b) c).hom ≫ eq_to_hom (by rw add_assoc) =
  (functor.associator _ _ _).hom ≫ 𝟙 (quotient.shift_functor h a) ◫ (shift_μ h b c).hom ≫
    (shift_μ h a (b + c)).hom :=
quotient.nat_trans_ext _ _ (λ X, begin
  dsimp only [functor.associator, nat_trans.comp_app, nat_trans.hcomp_app,
    nat_trans.id_app, quotient.shift_functor],
  erw [id_comp, id_comp, shift_μ_hom_app, shift_μ_hom_app, shift_μ_hom_app,
    shift_μ_hom_app, assoc, functor.map_id, id_comp, lift_map_functor_map],
  dsimp only ,
  simp only [functor.comp_map, ← functor.map_comp, ← functor.map_comp_assoc,
    associativity_compatibility],
  simpa only [assoc, functor.map_comp, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans,
    eq_to_hom_refl, comp_id],
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

def functor_comm_shift :
  @functor.has_comm_shift _ _ _ _ (functor r) A _ _
    (quotient.shift h) :=
{ iso := quotient.comm_shift h,
  iso_add := λ a b, begin
    ext K,
    dsimp,
    simp only [functor.comm_shift.add_hom_app, comm_shift_hom_app, id_comp],
    erw [functor.map_id, id_comp, id_comp],
    change _ ≫ (shift_μ h a b).hom.app ((functor r).obj K) = _,
    erw [shift_μ_hom_app, ← functor.map_comp, iso.inv_hom_id_app, functor.map_id],
  end,
  iso_zero := begin
    ext K,
    simp only [nat_trans.comp_app, lift.is_lift_hom, nat_trans.id_app],
    dsimp only [functor.comm_shift.unit, shift.compatibility.comm_shift.unit,
      iso.trans, iso.symm, nat_trans.comp_app, iso_whisker_right, whiskering_right,
      functor.map_iso, whisker_right, iso_whisker_left, functor.left_unitor,
      functor.right_unitor, whiskering_left, whisker_left],
    erw [id_comp, id_comp, id_comp, shift_ε_hom_app, ← functor.map_comp,
      iso.inv_hom_id_app, functor.map_id],
    refl,
  end, }

section

variables
  {D : Type*} [category D]
  {F : C ⥤ D} {F' : quotient r ⥤ D} (e : functor r ⋙ F' ≅ F)
  {B : Type*} [add_monoid B] [has_shift C B] [has_shift D B]
  [has_shift (quotient r) B] [(functor r).has_comm_shift B]
  [F.has_comm_shift B]

def comm_shift_iso_of_fac (a : B) :
  shift_functor (quotient r) a ⋙ F' ≅ F' ⋙ shift_functor D a :=
lift_nat_iso _ _ ((functor.associator _ _ _).symm ≪≫
    iso_whisker_right ((functor r).comm_shift_iso a).symm F' ≪≫
    functor.associator _ _ _ ≪≫ iso_whisker_left _ e ≪≫
    F.comm_shift_iso a ≪≫ iso_whisker_right e.symm _ ≪≫ functor.associator _ _ _)

@[simp]
lemma comm_shift_iso_of_fac_hom_app (a : B) (X : C) :
  (comm_shift_iso_of_fac e a).hom.app ((functor r).obj X) =
    F'.map (((functor r).comm_shift_iso a).inv.app X) ≫
    e.hom.app ((shift_functor C a).obj X) ≫
    (F.comm_shift_iso a).hom.app X ≫
    (shift_functor D a).map (e.inv.app X) :=
begin
  dsimp only [comm_shift_iso_of_fac],
  simp only [lift_nat_iso_hom, iso.trans_hom, iso.symm_hom, iso_whisker_right_hom,
    iso_whisker_left_hom, lift_nat_trans_app, nat_trans.comp_app,
    functor.associator_inv_app, whisker_right_app, functor.associator_hom_app,
    whisker_left_app, comp_id, id_comp],
end

@[simp]
lemma comm_shift_iso_of_fac_inv_app (a : B) (X : C) :
  (comm_shift_iso_of_fac e a).inv.app ((functor r).obj X) =
    (shift_functor D a).map (e.hom.app X) ≫
    (F.comm_shift_iso a).inv.app X ≫
    e.inv.app ((shift_functor C a).obj X) ≫
    F'.map (((functor r).comm_shift_iso a).hom.app X) :=
begin
  dsimp only [comm_shift_iso_of_fac],
  simp only [lift_nat_iso_inv, iso.trans_inv, iso_whisker_right_inv, iso.symm_inv, assoc,
    iso_whisker_left_inv, lift_nat_trans_app, nat_trans.comp_app,
    functor.associator_inv_app, whisker_right_app, whisker_left_app,
    functor.associator_hom_app, comp_id, id_comp],
end

variable (B)

def has_comm_shift : F'.has_comm_shift B :=
{ iso := λ a, comm_shift_iso_of_fac e a,
  iso_zero := begin
    ext1,
    refine nat_trans_ext _ _ (λ X, _),
    simp only [comm_shift_iso_of_fac_hom_app, functor.comm_shift.unit_hom_app,
      functor.comm_shift_iso_zero, functor.comm_shift.unit_inv_app,
      F'.map_comp, assoc, ← e.hom.naturality_assoc, functor.comp_map],
    nth_rewrite 1 ← functor.map_comp_assoc,
    erw [← functor.map_comp, iso.inv_hom_id_app, (functor r).map_id, F'.map_id, id_comp,
      ← nat_trans.naturality],
    dsimp only [functor.id],
    rw e.hom_inv_id_app_assoc,
  end,
  iso_add := λ a b, begin
    ext1,
    refine nat_trans_ext _ _ (λ X, _),
    simp only [functor.comm_shift.add_hom_app, assoc, functor.comm_shift_iso_add,
      comm_shift_iso_of_fac_hom_app, functor.map_comp, functor.comm_shift.add_inv_app],
    erw [← nat_trans.naturality_assoc, ← nat_trans.naturality_assoc,
      comm_shift_iso_of_fac_hom_app, assoc, assoc, assoc],
    dsimp only [functor.comp_map],
    nth_rewrite 3 ← functor.map_comp_assoc,
    erw [← functor.map_comp, iso.inv_hom_id_app, (functor r).map_id, F'.map_id, id_comp],
    nth_rewrite 4 ← functor.map_comp_assoc,
    erw [e.inv_hom_id_app, functor.map_id, id_comp, (shift_functor_add D a b).inv.naturality],
    refl,
  end, }

instance lift_has_comm_shift
 (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) :
  (lift r F hF).has_comm_shift B :=
has_comm_shift (lift.is_lift r F hF) B

end

end quotient

end category_theory
