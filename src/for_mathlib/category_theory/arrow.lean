/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow

namespace category_theory

namespace arrow

variables {C D : Type*} [category C] [category D]

/-- Condition that the image of `f` by `F` is an isomorphism -/
def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

namespace is_inverted_by

lemma of_is_iso {f : arrow C} {F : C ⥤ D} (h : is_iso (F.map f.hom)) : f.is_inverted_by F := h

end is_inverted_by

lemma congr_left {f g : arrow C} (h : f = g) : f.left = g.left := by rw h
lemma congr_right {f g : arrow C} (h : f = g) : f.right = g.right := by rw h

end arrow

end category_theory
