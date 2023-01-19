import for_mathlib.category_theory.localization.derived_functor_functoriality
import for_mathlib.category_theory.functor.shift
import for_mathlib.category_theory.localization.triangulated

open category_theory category_theory.category

noncomputable theory

namespace category_theory

variables {C H D A : Type*} [category C] [category H] [category D] [add_group A]
  [hD : has_shift D A] (F : C ⥤ D) (L : C ⥤ H)
  (W : morphism_property C) [L.is_localization W]
  [F.has_right_derived_functor W] (a : A)

namespace functor

namespace has_comm_shift

include hD

@[simps]
def right_derived_α_shift (a : A) :
  F ⋙ shift_functor D a ⟶ L ⋙ F.right_derived_functor L W ⋙ shift_functor D a :=
whisker_right (F.right_derived_functor_α L W) _  ≫ (functor.associator _ _ _).hom

instance is_right_derived_functor_α_shift :
  (F.right_derived_functor L W ⋙ shift_functor D a).is_right_derived_functor
  (right_derived_α_shift F L W a) :=
by { dsimp only [right_derived_α_shift], apply_instance, }

instance has_right_derived_functor_α_shift :
  (F ⋙ shift_functor D a).has_right_derived_functor W :=
is_right_derived_functor.has_right_derived_functor (F ⋙ shift_functor D a)
  (F.right_derived_functor W.Q W ⋙ shift_functor D a) W.Q (right_derived_α_shift F W.Q W a) W

omit hD

variables [has_shift C A] [has_shift H A] [L.has_comm_shift A]

@[simps]
def right_derived_shift_α (a : A) :
  shift_functor C a ⋙ F ⟶ L ⋙ shift_functor H a ⋙ F.right_derived_functor L W :=
whisker_left _ (F.right_derived_functor_α L W) ≫ (functor.associator _ _ _).inv ≫
  whisker_right (L.comm_shift_iso a).hom _ ≫ (functor.associator _ _ _).hom

instance is_right_derived_functor_shift_α :
  (shift_functor H a ⋙ F.right_derived_functor L W).is_right_derived_functor
  (right_derived_shift_α F L W a) :=
by { dsimp only [right_derived_shift_α], apply_instance, }

variable [hW : W.compatible_with_shift A]
include hW

instance has_right_derived_functor_shift_α :
  (shift_functor C a ⋙ F).has_right_derived_functor W :=
is_right_derived_functor.has_right_derived_functor (shift_functor C a ⋙ F)
  (shift_functor W.localization a ⋙ F.right_derived_functor W.Q W) W.Q (right_derived_shift_α F W.Q W a) W

omit hW
include hD
variable [F.has_comm_shift A]

def right_derived_comm_shift :
  shift_functor H a ⋙ F.right_derived_functor L W ≅
    F.right_derived_functor L W ⋙ shift_functor D a :=
nat_iso.right_derived (F.comm_shift_iso a) (right_derived_shift_α F L W a)
  (right_derived_α_shift F L W a)

@[reassoc]
lemma right_derived_comm_shift_comm (X : C) :
  (right_derived_shift_α F L W a).app X ≫ (right_derived_comm_shift F L W a).hom.app (L.obj X) =
    (F.comm_shift_iso a).hom.app X ≫ (right_derived_α_shift F L W a).app X :=
nat_trans.right_derived_app (F.comm_shift_iso a).hom
  (right_derived_shift_α F L W a) (right_derived_α_shift F L W a) X

@[reassoc]
lemma right_derived_comm_shift_comm' (X : C) :
  (F.right_derived_functor_α L W).app ((shift_functor C a).obj X) ≫
    (F.right_derived_functor L W).map ((L.comm_shift_iso a).hom.app X) ≫
    (right_derived_comm_shift F L W a).hom.app (L.obj X) =
  (F.comm_shift_iso a).hom.app X ≫
    (shift_functor D a).map ((F.right_derived_functor_α L W).app X) :=
by simpa only [right_derived_shift_α_app, assoc, right_derived_α_shift_app]
  using right_derived_comm_shift_comm F L W a X

instance : has_comm_shift (F.right_derived_functor L W) A :=
{ iso := λ a, right_derived_comm_shift F L W a,
  iso_zero := begin
    ext1,
    apply is_right_derived_functor_to_ext _ (right_derived_shift_α F L W (0 : A)),
    ext X,
    simp only [nat_trans.comp_app, whisker_left_app, right_derived_comm_shift_comm],
    simp only [right_derived_α_shift_app, right_derived_shift_α_app, comm_shift.unit_hom_app,
      assoc, L.comm_shift_iso_zero, F.comm_shift_iso_zero, functor.map_comp],
    nth_rewrite 1 ← functor.map_comp_assoc,
    erw [iso.inv_hom_id_app, functor.map_id, id_comp,
      ← (F.right_derived_functor_α L W).naturality_assoc,
      (shift_functor_zero D A).inv.naturality ((F.right_derived_functor_α L W).app X)],
  end,
  iso_add := λ a b, begin
    ext1,
    apply is_right_derived_functor_to_ext _ (right_derived_shift_α F L W (a+b)),
    ext X,
    simp only [nat_trans.comp_app, whisker_left_app, right_derived_comm_shift_comm],
    simp only [right_derived_α_shift_app, right_derived_shift_α_app, comm_shift.add_hom_app,
      assoc, L.comm_shift_iso_add, F.comm_shift_iso_add, functor.map_comp],
    nth_rewrite 3 ← functor.map_comp_assoc,
    erw [iso.inv_hom_id_app, functor.map_id, id_comp],
    erw ← (F.right_derived_functor_α L W).naturality_assoc,
    rw ← (shift_functor_add D a b).inv.naturality,
    erw (right_derived_comm_shift F L W b).hom.naturality_assoc,
    erw right_derived_comm_shift_comm'_assoc F L W b (X⟦a⟧),
    erw ← functor.map_comp_assoc,
    rw ← right_derived_comm_shift_comm' F L W a X,
    simpa only [functor.map_comp, assoc],
  end, }

instance right_derived_functor_α_respects_comm_shift :
  (F.right_derived_functor_α L W).respects_comm_shift A :=
⟨λ a, begin
  ext X,
  simpa only [nat_trans.comp_app, comp_hom_app, right_derived_α_shift_app,
    right_derived_shift_α_app, assoc] using (right_derived_comm_shift_comm F L W a X).symm,
end⟩

end has_comm_shift

end functor

end category_theory
