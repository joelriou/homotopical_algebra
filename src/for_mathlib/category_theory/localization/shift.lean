import for_mathlib.category_theory.functor.shift
import category_theory.localization.predicate

noncomputable theory

open category_theory category_theory.category

namespace category_theory

@[simps]
instance localization.lifting.L_comp {C H D : Type*} [category C] [category H] [category D]
  (L : C ⥤ H) (W : morphism_property C) [L.is_localization W] (F : H ⥤ D) :
  localization.lifting L W (L ⋙ F) F :=
⟨iso.refl _⟩

namespace functor

namespace has_comm_shift

section

variables {C H D : Type*} [category C] [category H] [category D]
  {L : C ⥤ H} {F : C ⥤ D} {G : H ⥤ D} (e : L ⋙ G ≅ F)
  (W : morphism_property C) [L.is_localization W] {A : Type*} [add_monoid A]
  [has_shift C A] [has_shift D A] [has_shift H A]
  [F.has_comm_shift A] [L.has_comm_shift A]

include e W

def of_localization.iso (a : A) : shift_functor H a ⋙ G ≅ G ⋙ shift_functor D a :=
localization.lift_nat_iso L W (L ⋙ (shift_functor H a ⋙ G)) (L ⋙ G ⋙ shift_functor D a) _ _
  ((functor.associator _ _ _).symm ≪≫ iso_whisker_right (L.comm_shift_iso a).symm _ ≪≫
    functor.associator _ _ _ ≪≫ iso_whisker_left _ e ≪≫ F.comm_shift_iso a ≪≫
    iso_whisker_right e.symm  _ ≪≫ functor.associator _ _ _)

@[simp]
lemma of_localization.iso_hom_app_obj (a : A) (X : C) :
  (of_localization.iso e W a).hom.app (L.obj X) =
    G.map ((L.comm_shift_iso a).inv.app X) ≫ e.hom.app ((shift_functor C a).obj X) ≫
      (F.comm_shift_iso a).hom.app X ≫ (shift_functor D a).map (e.inv.app X) :=
begin
  dsimp [of_localization.iso],
  simp only [localization.lift_nat_trans_app, localization.lifting.L_comp_iso, iso.refl_hom,
    nat_trans.id_app, nat_trans.comp_app, associator_inv_app, whisker_right_app,
    associator_hom_app, whisker_left_app, comp_id, id_comp, iso.refl_inv, assoc],
  erw id_comp,
end

@[simp]
lemma of_localization.iso_inv_app_obj (a : A) (X : C) :
  (of_localization.iso e W a).inv.app (L.obj X) =
    (shift_functor D a).map (e.hom.app X) ≫  (F.comm_shift_iso a).inv.app X ≫
    e.inv.app ((shift_functor C a).obj X) ≫ G.map ((L.comm_shift_iso a).hom.app X) :=
begin
  dsimp [of_localization.iso],
  simp only [assoc, localization.lift_nat_trans_app, localization.lifting.L_comp_iso,
    iso.refl_hom, nat_trans.id_app, nat_trans.comp_app, associator_inv_app, whisker_right_app,
    whisker_left_app, associator_hom_app, comp_id, id_comp, iso.refl_inv],
  erw id_comp,
end

variable (A)

@[simps]
def of_localization : G.has_comm_shift A :=
{ iso := of_localization.iso e W,
  iso_zero := begin
    ext1,
    apply localization.nat_trans_ext L W,
    intro X,
    simp only [of_localization.iso_hom_app_obj, comm_shift.unit_hom_app, iso.symm_hom,
      iso.symm_inv, monoidal_functor.ε_iso_hom, F.comm_shift_iso_zero A,
      L.comm_shift_iso_zero A, comm_shift.unit_inv_app, assoc, functor.map_comp,
      ← nat_trans.naturality, ← nat_trans.naturality_assoc, id_map, comp_map],
    congr' 1,
    dsimp,
    simp only [e.hom_inv_id_app_assoc, ← functor.map_comp_assoc, ← functor.map_comp,
      ε_hom_inv_app],
    erw [functor.map_id, functor.map_id, id_comp],
  end,
  iso_add := λ a b, begin
    ext1,
    apply localization.nat_trans_ext L W,
    intro X,
    simp only [of_localization.iso_hom_app_obj, comm_shift.add_hom_app, iso.symm_hom,
      map_comp, iso.symm_inv, monoidal_functor.μ_iso_hom, assoc, μ_naturality,
      functor.comm_shift_iso_add, comm_shift.add_inv_app],
    erw [← nat_trans.naturality_assoc, ← nat_trans.naturality_assoc],
    dsimp,
    simp only [of_localization.iso_hom_app_obj, assoc],
    nth_rewrite 3 ← G.map_comp_assoc,
    erw [← (shift_functor D b).map_comp_assoc, e.inv_hom_id_app, functor.map_id, id_comp,
      ← L.map_comp, μ_hom_inv_app, L.map_id, G.map_id, id_comp],
    refl,
  end, }

include A

lemma of_localization.respects_comm_shift :
  by { letI := of_localization e W A,
    exact e.hom.respects_comm_shift A } :=
begin
  letI := of_localization e W A,
  refine ⟨λ a, _⟩,
  ext X,
  simp only [nat_trans.comp_app, comp_hom_app, whisker_right_app, assoc, whisker_left_app],
  erw of_localization.iso_hom_app_obj e W a X,
  simp only [assoc, ← G.map_comp_assoc, iso.hom_inv_id_app, ← functor.map_comp,
    iso.inv_hom_id_app],
  dsimp,
  simp only [map_id, id_comp, comp_id],
end

end

section

variables {C H D A : Type*}
  [category C] [category H] [category D] [add_monoid A]
  [has_shift C A] [has_shift D A] [has_shift H A] (W : morphism_property C)
  {L : C ⥤ H} {F : C ⥤ D} [L.has_comm_shift A] [F.has_comm_shift A]
  [L.is_localization W] (hF : W.is_inverted_by F)

instance localization_lift_has_comm_shift :
  (localization.lift F hF L).has_comm_shift A :=
of_localization (localization.fac F hF L) W A

instance localization_fac_hom_respects_comm_shift :
  (localization.fac F hF L).hom.respects_comm_shift A :=
of_localization.respects_comm_shift _ _ _

end
end has_comm_shift

end functor

end category_theory
