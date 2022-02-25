/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.isomorphism

open category_theory

variables (C : Type*) [category C]

abbreviation hom_class := Π (X Y : C), set (X ⟶ Y)

namespace hom_class

variables {C}

def isomorphisms : hom_class C := λ X Y f, is_iso f

end hom_class

