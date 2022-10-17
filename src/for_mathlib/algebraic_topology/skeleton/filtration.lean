import for_mathlib.algebraic_topology.skeleton.split
import for_mathlib.algebraic_topology.skeleton.misc
import category_theory.limits.mono_coprod

open category_theory category_theory.limits opposite
open_locale simplicial

namespace simplicial_object

namespace splitting

variables {C : Type*} [category C] [has_finite_coproducts C]
  {X : simplicial_object C} (s : splitting X) [mono_coprod C]

lemma sk_succ_comm_sq (d : ℕ) :
  comm_sq (sSet.tensor_map₁ (sSet.boundary_inclusion (d+1)) (s.N (d+1)))
    sorry
    ((sSet.tensor_yoneda_adjunction (d+1) (s.N (d+1)) (s.sk (d+1))).symm
    (s.ι_summand_sk (d+1) (index_set.truncated.id (op [d+1]))))
    (s.sk_inclusion (show d ≤ d+1, by exact nat.le_succ _)) :=
begin
  sorry,
end


end splitting

end simplicial_object
