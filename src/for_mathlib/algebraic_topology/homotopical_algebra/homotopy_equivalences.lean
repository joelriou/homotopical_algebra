/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma
import for_mathlib.algebraic_topology.homotopical_algebra.over
import for_mathlib.category_theory.functor_misc

noncomputable theory

open algebraic_topology
open category_theory category_theory.category

lemma category_theory.functor.is_iso_map_iff {C D : Type*} [category C] [category D]
  (F : C ⥤ D) [reflects_isomorphisms F] {X Y : C} (f : X ⟶ Y) : is_iso (F.map f) ↔ is_iso f :=
begin
  split,
  { introI,
    exact is_iso_of_reflects_iso f F, },
  { introI,
    apply_instance, },
end

namespace category_theory.morphism_property.three_of_two

variables {C : Type*} [category C] {X Y X' Y' : C}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : X ⟶ X'} {g' : Y ⟶ Y'}

lemma left_iff_right_of_sq {P : morphism_property C}
  (h : P.three_of_two) (sq : comm_sq g f f' g') (hg : P g) (hg' : P g'):
  P f ↔ P f' :=
begin
  split,
  { intro hf,
    refine h.of_comp_left g f' hg _,
    rw sq.w,
    exact h.of_comp _ _ hf hg', },
  { intro hf',
    refine h.of_comp_right f g' hg' _,
    rw ← sq.w,
    exact h.of_comp _ _ hg hf', },
end

end category_theory.morphism_property.three_of_two

open category_theory

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [model_category C]
  {Ho : Type*} [category Ho] (L : C ⥤ Ho) [L.is_localization weq]
  {Hocof : Type*} [category Hocof] (Lcof : cofibrant_object C ⥤ Hocof)
    [Lcof.is_localization cofibrant_object.weq]
  {Hobif : Type*} [category Hobif] (Lbif : bifibrant_object C ⥤ Hobif)
    [Lbif.is_localization bifibrant_object.weq]

lemma strong_deformation_retract_of_cofibration_and_homotopy_equivalence
  {X Y : bifibrant_object C} (f : X ⟶ Y) [is_iso (Lbif.map f)] :
  ∃ (g : Y ⟶ X) (hg₁ : f ≫ g = 𝟙 X) (P : path_object Y.obj)
    (H : right_homotopy P.pre ((bifibrant_object.forget C).map (g ≫ f)) (𝟙 Y.obj)),
    (bifibrant_object.forget C).map f ≫ H.h = (bifibrant_object.forget C).map f ≫ P.σ :=
begin
  sorry,
end

lemma bifibrant_object.is_iso_Lbif_map_cofibration_iff
  {X Y : bifibrant_object C} (f : X ⟶ Y) [cofibration ((bifibrant_object.forget C).map f)] :
  is_iso (Lbif.map f) ↔ bifibrant_object.weq f :=
begin
  refine ⟨_, localization.inverts_W Lbif bifibrant_object.weq f⟩,
  introI,
  rcases strong_deformation_retract_of_cofibration_and_homotopy_equivalence Lbif f
    with ⟨g, hg₁, P, H, property⟩,
  let f' := (bifibrant_object.forget C).map f,
  let W := CM5a.obj f',
  let i : X.obj ⟶ W := CM5a.i f',
  let p : W ⟶ Y.obj := CM5a.p f',
  have sq : comm_sq i f' p (𝟙 Y.obj) :=
    comm_sq.mk (by simpa only [CM5a.fac f'] using (comp_id f').symm),
  suffices : sq.has_lift,
  { haveI := this,
    refine CM3a f' i _ weak_eq.property,
    have fac₁ : 𝟙 X.obj ≫ i = f' ≫ sq.lift := by rw [id_comp, sq.fac_left],
    have fac₂ : 𝟙 X.obj ≫ f' = i ≫ p := by rw [id_comp, CM5a.fac f'],
    refine is_retract.mk (arrow.hom_mk fac₁) (arrow.hom_mk fac₂) _,
    ext,
    { apply comp_id, },
    { exact sq.fac_right, }, },
  sorry,
end

lemma bifibrant_object.is_iso_Lbif_map_iff
  {X Y : bifibrant_object C} (f : X ⟶ Y) :
  is_iso (Lbif.map f) ↔ bifibrant_object.weq f :=
begin
  split,
  { intro hf,
    let f' := (bifibrant_object.forget C).map f,
    let Z := CM5b.obj f',
    let i : X ⟶ bifibrant_object.mk Z := CM5b.i f',
    let p : bifibrant_object.mk Z ⟶ Y := CM5b.p f',
    have h : i ≫ p = f := CM5b.fac f',
    rw ← h,
    rw [← h, Lbif.map_comp] at hf,
    haveI := hf,
    haveI : weak_eq ((bifibrant_object.forget C).map p) := (infer_instance : weak_eq (CM5b.p f')),
    haveI : cofibration ((bifibrant_object.forget C).map i) := (infer_instance : cofibration (CM5b.i f')),
    haveI := is_iso_Lbif_map Lbif p,
    haveI : is_iso (Lbif.map i) := is_iso.of_is_iso_comp_right _ (Lbif.map p),
    refine CM2.of_comp _ _ _ weak_eq.property,
    exact (bifibrant_object.is_iso_Lbif_map_cofibration_iff Lbif i).mp infer_instance, },
  { exact localization.inverts_W Lbif bifibrant_object.weq f, },
end

lemma bifibrant_object.is_iso_Lbif_map_iff_is_iso_Lcof_map
  {X Y : bifibrant_object C} (f : X ⟶ Y) :
  is_iso (Lbif.map f) ↔ is_iso (Lcof.map ((bifibrant_object.forget_fib C).map f)) :=
by rw [← (Hobif_to_Hocof Lcof Lbif).is_iso_map_iff, ← functor.comp_map,
  is_iso_map_iff_of_nat_iso (Lbif_comp_Hobif_to_Hocof_iso Lcof Lbif), functor.comp_map]

lemma cofibrant_object.is_iso_Lcof_map_iff
  {X Y : cofibrant_object C} (f : X ⟶ Y) :
  is_iso (Lcof.map f) ↔ cofibrant_object.weq f :=
begin
  split,
  { intro hf,
    change (morphism_property.isomorphisms _).inverse_image Lcof f at hf,
    have sq := comm_sq.mk (bifibrant_replacement.fac f),
    rw ((morphism_property.three_of_two.for_isomorphisms _).for_inverse_image Lcof).left_iff_right_of_sq sq
      (is_iso_Lcof_map' Lcof _ weak_eq.property) (is_iso_Lcof_map' Lcof _ weak_eq.property) at hf,
    change is_iso _ at hf,
    rw ← bifibrant_object.is_iso_Lbif_map_iff_is_iso_Lcof_map Lcof
      bifibrant_object.homotopy_category.Q at hf,
    rw bifibrant_object.is_iso_Lbif_map_iff at hf,
    exact (CM2.left_iff_right_of_sq ((cofibrant_object.forget C).map_comm_sq sq) weak_eq.property weak_eq.property).mpr hf, },
  { exact localization.inverts_W Lcof cofibrant_object.weq f, },
end

lemma is_iso_Lcof_map_iff_is_iso_L_map
  {X Y : cofibrant_object C} (f : X ⟶ Y) :
  is_iso (Lcof.map f) ↔ is_iso (L.map ((cofibrant_object.forget C).map f)) :=
by rw [← (Hocof_to_Ho Lcof L).is_iso_map_iff, ← functor.comp_map,
  is_iso_map_iff_of_nat_iso (Lcof_comp_Hocof_to_Ho_iso Lcof L), functor.comp_map]

lemma is_iso_L_map_iff {X Y : C} (f : X ⟶ Y) :
  is_iso (L.map f) ↔ weq f :=
begin
  split,
  { intro hf,
    change (morphism_property.isomorphisms _).inverse_image L f at hf,
    have sq := comm_sq.mk (cofibrant_replacement.fac f),
    have eq := ((morphism_property.three_of_two.for_isomorphisms _).for_inverse_image L).left_iff_right_of_sq sq.flip (by { change is_iso _, apply_instance, }) (by { change is_iso _, apply_instance, }),
    rw ← eq at hf,
    change is_iso _ at hf,
    rw ← is_iso_Lcof_map_iff_is_iso_L_map L Lcof' at hf,
    rw cofibrant_object.is_iso_Lcof_map_iff at hf,
    exact (CM2.left_iff_right_of_sq sq.flip weak_eq.property weak_eq.property).mp hf, },
  { exact localization.inverts_W L weq f, },
end

end model_category

end algebraic_topology
