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

variables {M : model_category}

namespace fibrant_and_cofibrant_objects

lemma cofibration_is_inverted_by_L_iff (w : arrow M.fibrant_and_cofibrant_objects)
  (hw : (arrow.mk w.hom : arrow M.C) ∈ M.cof) :
  w.is_inverted_by L ↔ w ∈ W M :=
begin
  split,
  { intro hw,
    have foo := M.CM5a,
    rcases M.CM5a (arrow.mk w.hom) with ⟨Z, i, p, fac, hi, hp⟩,
    sorry, },
  { intro hw,
    exact universal_property.inverts_W ⟨w, hw⟩, },
end

lemma is_inverted_by_L_iff (w : arrow M.fibrant_and_cofibrant_objects) :
  w.is_inverted_by L ↔ w ∈ W M :=
begin
  split,
  { intro hw,
    rcases M.CM5b (arrow.mk w.hom) with ⟨Z, i, p, fac, hi, hp⟩,
    have hip := M.CM2.of_comp _ _ _ i p _ hp.2,
    { rw ← fac at hip,
      exact hip, },
    { let Z' : M.fibrant_and_cofibrant_objects := ⟨⟨Z, nonempty.intro ⟨_⟩⟩, nonempty.intro ⟨_⟩⟩, rotate,
      { convert M.cof_comp_stable _ _ _ _ _ w.left.1.2.some.cof hi, },
      { convert M.fib_comp_stable _ _ _ _ _ hp.1 w.right.2.some.fib, },
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

lemma is_inverted_by_L_iff (w : arrow M.cofibrant_objects) :
  w.is_inverted_by L ↔ w ∈ W M :=
begin
  split,
  { intro hw,
    suffices hw' : arrow.mk (map.Sq_lift w.hom) ∈ fibrant_and_cofibrant_objects.W M,
    { apply M.CM2.of_comp_right w.hom _ (triv_cof_ι w.right).2,
      erw ← map.Sq_lift_comm w.hom,
      exact M.CM2.of_comp _ _ _ _ _ (triv_cof_ι w.left).2 hw', },
    rw ← fibrant_and_cofibrant_objects.is_inverted_by_L_iff,
    haveI : is_iso (L.map w.hom) := hw,
    exact (infer_instance : is_iso (R.map (L.map w.hom))), },
  { intro hw,
    exact universal_property.inverts_W ⟨w, hw⟩, },
end

end fibrant_replacement

end cofibrant_objects

namespace cofibrant_replacement

lemma is_inverted_by_L_iff (w : arrow M.C) :
  w.is_inverted_by L ↔ w ∈ M.W :=
begin
  split,
  { intro hw,
    suffices hw' : arrow.mk (map.Sq_lift w.hom) ∈ cofibrant_objects.W M,
    { rw ← arrow.mk_eq w,
      apply M.CM2.of_comp_left _ w.hom (triv_fib_p w.left).2,
      erw ← map.Sq_lift_comm w.hom,
      exact M.CM2.of_comp _ _ _ _ _ hw' (triv_fib_p w.right).2, },
    rw ← cofibrant_objects.fibrant_replacement.is_inverted_by_L_iff,
    haveI : is_iso (L.map w.hom) := hw,
    exact (infer_instance : is_iso (R.map (L.map w.hom))), },
  { intro hw,
    have h := universal_property.inverts_W ⟨w, hw⟩,
    exact h, },
end

end cofibrant_replacement

lemma is_inverted_by_Q_iff (w : arrow M.C) :
  w.is_inverted_by M.Q ↔ w ∈ M.W :=
begin
  split,
  { intro hw,
    apply (cofibrant_replacement.is_inverted_by_L_iff w).mp,
    haveI : is_iso (M.Q.map w.hom) := hw,
    have hw' : is_iso (cofibrant_replacement.is_strict_localization.lift_functor.map
      (M.Q.map w.hom)) := infer_instance,
    have eq := functor.congr_map_conjugate
      cofibrant_replacement.is_strict_localization.lift_functor_fac w.hom,
    erw [id_comp, comp_id] at eq,
    erw eq at hw',
    exact hw', },
  { intro hw,
    exact is_iso.of_iso (arrow_class.localization.Wiso ⟨w, hw⟩), },
end

end model_category

end algebraic_topology