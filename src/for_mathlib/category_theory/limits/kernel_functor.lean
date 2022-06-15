/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.kernels

noncomputable theory
open category_theory

namespace category_theory

namespace limits

def kernel_functor (C : Type*) [category C] [has_zero_morphisms C] [has_kernels C]: arrow C ⥤ C :=
{ obj := λ w, kernel w.hom,
  map := λ f g φ, kernel.lift _ (kernel.ι _ ≫ φ.left)
    (by simp only [category.assoc, arrow.w, kernel.condition_assoc, zero_comp]), }

def cokernel_functor (C : Type*) [category C] [has_zero_morphisms C] [has_cokernels C]: arrow C ⥤ C :=
{ obj := λ w, cokernel w.hom,
  map := λ f g φ, cokernel.desc _ (φ.right ≫ cokernel.π _)
    (by simp only [← arrow.w_assoc φ, cokernel.condition, comp_zero]), }

end limits

end category_theory