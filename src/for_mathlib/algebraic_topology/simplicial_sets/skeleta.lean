import algebraic_topology.simplicial_set
import category_theory.limits.kan_extension

noncomputable theory

universes u

open category_theory

namespace sSet

namespace truncated

def i (n : ℕ) : truncated n ⥤ sSet.{u} :=
Lan simplex_category.truncated.inclusion.op

def adjunction (n : ℕ) : i n ⊣ sk n :=
category_theory.Lan.adjunction _ simplex_category.truncated.inclusion.op

instance adjunction.unit_is_iso (n : ℕ) : is_iso (adjunction n).unit :=
Lan.coreflective _ _

end truncated

def sk' (n : ℕ) : sSet ⥤ sSet := sk n ⋙ truncated.i n

def ι_sk' (n : ℕ) : sk' n ⟶ 𝟭 sSet := (truncated.adjunction n).counit

instance sk_ι_sk'_is_iso (n : ℕ) : is_iso (whisker_right (ι_sk' n) (sk.{u} n)) :=
begin
  let f := (whisker_left (sk.{u} n) (truncated.adjunction n).unit),
  let g := whisker_right (truncated.adjunction n).counit (sk.{u} n),
  haveI : is_iso (f ≫ g),
  { rw (truncated.adjunction n).right_triangle,
    apply_instance, },
  change is_iso g,
  exact is_iso.of_is_iso_comp_left f g,
end

lemma ι_sk'_bij (X : sSet) (n : ℕ) (Δ : simplex_categoryᵒᵖ) (h : Δ.unop.len ≤ n) :
  is_iso (((ι_sk' n).app X).app Δ) :=
begin
  induction Δ using opposite.rec,
  have h' : ∃ (Δ' : simplex_category.truncated n), Δ = Δ'.1 := ⟨⟨Δ, h⟩, rfl⟩,
  cases h' with Δ' hΔ',
  subst hΔ',
  let e := as_iso (whisker_right (ι_sk' n) (sk n)),
  exact is_iso.of_iso ((e.app X).app (opposite.op Δ')),
end

end sSet
