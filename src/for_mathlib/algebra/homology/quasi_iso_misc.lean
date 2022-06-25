/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.quasi_iso
import algebra.homology.homotopy

open category_theory category_theory.limits

universes v u

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V] [has_cokernels V]
  [has_images V] [has_equalizers V] [has_zero_object V] [has_image_maps V]
variables {c : complex_shape ι} {K L : homological_complex V c}

lemma quasi_iso.of_homotopy_equiv (e : homotopy_equiv K L) : quasi_iso e.hom :=
⟨λ i, begin
  refine ⟨⟨(homology_functor V c i).map e.inv, _⟩⟩,
  simp only [← functor.map_comp, ← (homology_functor V c i).map_id],
  split; apply homology_map_eq_of_homotopy,
  exacts [e.homotopy_hom_inv_id, e.homotopy_inv_hom_id],
end⟩
