/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.pullbacks
import category_theory.comma_op

open category_theory
open category_theory.category
open category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

def cone_of_square {f g : arrow C} (sq : f ⟶ g) : pullback_cone g.hom sq.right :=
pullback_cone.mk sq.left f.hom sq.w'

def cocone_of_square {f g : arrow C} (sq : f ⟶ g) : pushout_cocone sq.left f.hom :=
pushout_cocone.mk g.hom sq.right sq.w'

def is_cartesian {f g : arrow C} (sq : f ⟶ g) := is_limit (cone_of_square sq)

def is_cocartesian {f g : arrow C} (sq : f ⟶ g) := is_colimit (cocone_of_square sq)

/- opposites... -/

end category_theory

