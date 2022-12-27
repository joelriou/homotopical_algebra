import category_theory.shift
import for_mathlib.category_theory.quotient_misc

noncomputable theory

namespace category_theory

open category

variables {C D E : Type*} {A : Type*} [category C] [category D] [category E]
  [add_monoid A] [has_shift C A] [has_shift D A] [has_shift E A]

variable (C)

def shift_functor_add' (a b c : A) (h : c = a + b) :
  shift_functor C c ≅ shift_functor C a ⋙ shift_functor C b :=
eq_to_iso (by rw h) ≪≫ shift_functor_add C a b

namespace functor

variables {C}  {F : C ⥤ D} {G : D ⥤ E} {a : A}
  (hF : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (hG : shift_functor D a ⋙ G ≅ G ⋙ shift_functor E a)

def comm_shift_comp :
  shift_functor C a ⋙ (F ⋙ G) ≅ (F ⋙ G) ⋙ shift_functor E a :=
(functor.associator _ _ _).symm ≪≫
  iso_whisker_right hF G ≪≫
  functor.associator _ _ _ ≪≫
  iso_whisker_left F hG ≪≫ (functor.associator _ _ _).symm

@[simp]
lemma comm_shift_comp_hom_app (X : C) :
  (comm_shift_comp hF hG).hom.app X = G.map (hF.hom.app X) ≫ hG.hom.app (F.obj X) :=
begin
  dsimp [comm_shift_comp],
  simp only [comp_id, id_comp],
end

@[simp]
lemma comm_shift_comp_inv_app (X : C) :
  (comm_shift_comp hF hG).inv.app X = hG.inv.app (F.obj X) ≫ G.map (hF.inv.app X) :=
begin
  dsimp [comm_shift_comp],
  simp only [comp_id, id_comp],
end

end functor

lemma shift_functor_comp_shift_functor_neg_eq_add'_comp_zero
  {G : Type*} [add_group G] [has_shift C G] (n : G) (X : C) :
  (shift_functor_comp_shift_functor_neg C n).hom.app X =
    (shift_functor_add' C n (-n) 0 (add_neg_self n).symm).inv.app X ≫
      (shift_functor_zero C G).hom.app X :=
by simpa only [shift_functor_add', eq_to_hom_map, unit_of_tensor_iso_unit_hom_app,
  eq_to_iso.hom, iso.trans_inv, nat_trans.comp_app, assoc]

end category_theory
