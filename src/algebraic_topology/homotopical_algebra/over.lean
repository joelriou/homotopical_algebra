/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category
import category_theory.limits.comma

open category_theory

namespace algebraic_topology

namespace model_category

def under (M : model_category) (X : M.C) : model_category :=
{ C := under X,
  fib_cof_we :=
  { W := M.W.inverse_image (under.forget _),
    cof := M.cof.inverse_image (under.forget _),
    fib := M.fib.inverse_image (under.forget _), },
  CM1 := begin
    split,
    { refine ⟨_⟩,
      intros J hJ hJ',
      haveI := M.CM1.1,
      apply comma.has_limits_of_shape, },
    { sorry, },
  end,
  CM2 := M.CM2.inverse_image (under.forget _),
  CM3 :=
  { W := M.CM3.W.inverse_image (under.forget _),
    cof := M.CM3.cof.inverse_image (under.forget _),
    fib := M.CM3.fib.inverse_image (under.forget _), },
  CM4 := ⟨M.CM4a.under X, M.CM4b.under X⟩,
  CM5 := ⟨M.CM5a.under X, M.CM5b.under X⟩, }

end model_category

end algebraic_topology

