/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma


noncomputable theory

open algebraic_topology
open category_theory category_theory.category

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

lemma category_theory.is_iso_iff_of_nat_iso {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
  is_iso (F₁.map f) ↔ is_iso (F₂.map f) :=
begin
  revert F₁ F₂,
  suffices : ∀ {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) (hf : is_iso (F₁.map f)), is_iso (F₂.map f),
  { exact λ F₁ F₂ e, ⟨this e, this e.symm⟩, },
  introsI F₁ F₂ e hf,
  refine is_iso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, _, _⟩,
  { simp only [nat_trans.naturality_assoc, is_iso.hom_inv_id_assoc, iso.inv_hom_id_app], },
  { simp only [assoc, ← e.hom.naturality, is_iso.inv_hom_id_assoc, iso.inv_hom_id_app], },
end

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
  {Ho : Type*} [category Ho] (L : C ⥤ Ho) [L.is_localization weq]
  {Hocof : Type*} [category Hocof] (Lcof : cofibrant_object C ⥤ Hocof)
    [Lcof.is_localization cofibrant_object.weq]
  {Hobif : Type*} [category Hobif] (Lbif : bifibrant_object C ⥤ Hobif)
    [Lbif.is_localization bifibrant_object.weq]

include M

instance bifibrant_object.is_iso_L_map {X Y : bifibrant_object C} (f : X ⟶ Y) [hf : weak_eq ((bifibrant_object.forget C).map f)] :
  is_iso (Lbif.map f) := localization.inverts_W Lbif bifibrant_object.weq f hf.property

lemma bifibrant_object.is_iso_Lbif_map_cofibration_iff
  {X Y : bifibrant_object C} (f : X ⟶ Y) [cofibration ((bifibrant_object.forget C).map f)] :
  is_iso (Lbif.map f) ↔ bifibrant_object.weq f :=
sorry

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
    haveI : is_iso (Lbif.map i) := is_iso.of_is_iso_comp_right _ (Lbif.map p),
    refine CM2.of_comp _ _ _ weak_eq.property,
    exact (bifibrant_object.is_iso_Lbif_map_cofibration_iff Lbif i).mp infer_instance, },
  { exact localization.inverts_W Lbif bifibrant_object.weq f, },
end

lemma bifibrant_object.is_iso_Lbif_map_iff_is_iso_Lcof_map
  {X Y : bifibrant_object C} (f : X ⟶ Y) :
  is_iso (Lbif.map f) ↔ is_iso (Lcof.map ((bifibrant_object.forget_fib C).map f)) := sorry

lemma cofibrant_object.is_iso_Lcof_map_iff
  {X Y : cofibrant_object C} (f : X ⟶ Y) :
  is_iso (Lcof.map f) ↔ cofibrant_object.weq f :=
begin
  split,
  { sorry, },
  { exact localization.inverts_W Lcof cofibrant_object.weq f, },
end

lemma cofibrant_object.is_iso_Lcof_map_iff_is_iso_L_map
  {X Y : cofibrant_object C} (f : X ⟶ Y) :
  is_iso (Lcof.map f) ↔ is_iso (L.map ((cofibrant_object.forget C).map f)) := sorry

lemma is_iso_L_map_iff {X Y : C} (f : X ⟶ Y) :
  is_iso (L.map f) ↔ weq f :=
begin
  split,
  { intro hf,
    have sq := comm_sq.mk (cofibrant_replacement.fac f),
    change (morphism_property.isomorphisms _).inverse_image L f at hf,
    have eq := ((morphism_property.three_of_two.for_isomorphisms _).for_inverse_image L).left_iff_right_of_sq sq.flip (by { change is_iso _, apply_instance, }) (by { change is_iso _, apply_instance, }),
    rw ← eq at hf,
    change is_iso _ at hf,
    rw ← cofibrant_object.is_iso_Lcof_map_iff_is_iso_L_map L (fundamental_lemma.Lcof C) at hf,
    rw cofibrant_object.is_iso_Lcof_map_iff at hf,
    exact (CM2.left_iff_right_of_sq sq.flip weak_eq.property weak_eq.property).mp hf, },
  { exact localization.inverts_W L weq f, },
end

/-namespace fibrant_and_cofibrant_objects

/-- Hirschhorn 7.8.2 -/
lemma cofibration_is_deformation_retract {X Y : fibrant_and_cofibrant_objects C}
  (i : X ⟶ Y) (hi₁ : (arrow.mk i : arrow C) ∈ (cof : arrow_class C)) (hi₂ : (arrow.mk i).is_inverted_by L) (P : path_object Y.1.1) :
  ∃ (g : Y ⟶ X) (hg₁ : i ≫ g = 𝟙 X) (H : P.pre.right_homotopy (g ≫ i) (𝟙 Y.1.1)),
    forget.map i ≫ H.h = forget.map i ≫ P.pre.σ' :=
begin
  sorry
end

lemma cofibration_is_inverted_by_L_iff (w : arrow (fibrant_and_cofibrant_objects C))
  (hw : (arrow.mk w.hom : arrow C) ∈ M.cof) :
  w.is_inverted_by L ↔ w ∈ (W : arrow_class (fibrant_and_cofibrant_objects C)) :=
begin
  split,
  { intro hw,
    rcases @CM5a C _ _(arrow.mk w.hom) with ⟨Z, i, p, fac, hi, hp⟩,
    sorry, },
  { intro hw,
    exact universal_property.inverts_W ⟨w, hw⟩, },
end

lemma is_inverted_by_L_iff (w : arrow (fibrant_and_cofibrant_objects C)) :
  w.is_inverted_by L ↔ w ∈ (W : arrow_class (fibrant_and_cofibrant_objects C)) :=
begin
  split,
  { intro hw,
    rcases @CM5b C _ _ (arrow.mk w.hom) with ⟨Z, i, p, fac, hi, hp⟩,
    have hip := CM2.of_comp _ _ _ i p _ hp.2,
    { rw ← fac at hip,
      exact hip, },
    { let Z' : fibrant_and_cofibrant_objects C := ⟨⟨Z, nonempty.intro ⟨_⟩⟩, nonempty.intro ⟨_⟩⟩, rotate,
      { convert cof_comp_stable _ _ _ _ _ w.left.1.2.some.cof hi, },
      { convert fib_comp_stable _ _ _ _ _ hp.1 w.right.2.some.fib, },
      let i' : w.left ⟶ Z' := i,
      let p' : Z' ⟶ w.right := p,o
      apply (cofibration_is_inverted_by_L_iff (arrow.mk i') hi).mp,
      have fac : L.map i' ≫ L.map p' = L.map w.hom,
      { rw ← L.map_comp,
        congr' 1,
        exact fac.symm, },
      haveI : is_iso (L.map w.hom) := hw,
      haveI : is_iso (L.map p') := universal_property.inverts_W ⟨arrow.mk p', hp.2⟩,
      exact is_iso.of_is_iso_fac_right fac, }, },
  { intro hw,
    exact universal_property.inverts_W ⟨w, hw⟩, },
end

end fibrant_and_cofibrant_objects

namespace cofibrant_objects

namespace fibrant_replacement

lemma is_inverted_by_L_iff (w : arrow (cofibrant_objects C)) :
  w.is_inverted_by L ↔ w ∈ (W : arrow_class (cofibrant_objects C)) :=
begin
  split,
  { intro hw,
    let φ : (_ : C) ⟶ _ := w.hom,
    suffices hw' : arrow.mk (map.Sq_lift φ) ∈ @fibrant_and_cofibrant_objects.W C _ _,
    { apply CM2.of_comp_right φ _ (triv_cof_ι w.right).2,
      erw ← map.Sq_lift_comm φ,
      exact (@CM2 C _ _).of_comp _ _ _ _ _ (triv_cof_ι w.left).2 hw', },
    rw ← fibrant_and_cofibrant_objects.is_inverted_by_L_iff,
    haveI : is_iso (L.map w.hom) := hw,
    exact (infer_instance : is_iso (R.map (L.map w.hom))), },
  { intro hw,
    exact universal_property.inverts_W ⟨w, hw⟩, },
end

end fibrant_replacement

end cofibrant_objects

namespace cofibrant_replacement

lemma is_inverted_by_L_iff (w : arrow C) :
  w.is_inverted_by L ↔ w ∈ (W : arrow_class C) :=
begin
  split,
  { intro hw,
    suffices hw' : arrow.mk (map.Sq_lift w.hom) ∈ @cofibrant_objects.W C _ _,
    { rw ← arrow.mk_eq w,
      apply CM2.of_comp_left _ w.hom (triv_fib_p w.left).2,
      erw ← map.Sq_lift_comm w.hom,
      exact CM2.of_comp _ _ _ _ _ hw' (triv_fib_p w.right).2, },
    rw ← cofibrant_objects.fibrant_replacement.is_inverted_by_L_iff,
    haveI : is_iso (L.map w.hom) := hw,
    exact (infer_instance : is_iso (R.map (L.map w.hom))), },
  { intro hw,
    have h := universal_property.inverts_W ⟨w, hw⟩,
    exact h, },
end

end cofibrant_replacement

lemma is_inverted_by_Q_iff (w : arrow C) :
  w.is_inverted_by Q ↔ w ∈ (W : arrow_class C) :=
begin
  split,
  { intro hw,
    apply (cofibrant_replacement.is_inverted_by_L_iff w).mp,
    haveI : is_iso (Q.map w.hom) := hw,
    have hw' : is_iso (cofibrant_replacement.is_strict_localization.lift_functor.map
      (Q.map w.hom)) := infer_instance,
    have eq := functor.congr_hom
      cofibrant_replacement.is_strict_localization.lift_functor_fac w.hom,
    erw [id_comp, comp_id] at eq,
    erw eq at hw',
    exact hw', },
  { intro hw,
    exact is_iso.of_iso (arrow_class.localization.Wiso ⟨w, hw⟩), },
end
-/
end model_category

end algebraic_topology
