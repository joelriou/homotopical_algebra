/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.fundamental_lemma


noncomputable theory

open algebraic_topology
open category_theory category_theory.category

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

namespace fibrant_and_cofibrant_objects

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
      let p' : Z' ⟶ w.right := p,
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

end model_category

end algebraic_topology