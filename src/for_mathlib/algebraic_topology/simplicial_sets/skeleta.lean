import algebraic_topology.simplicial_set
import category_theory.limits.kan_extension
import for_mathlib.split_simplicial_object

noncomputable theory

universes u

open category_theory
open opposite
open_locale simplicial

namespace simplex_category

protected def rec {F : Π (X : simplex_category), Sort u} (h : ∀ (n : ℕ), F [n]) :
  Π X, F X := λ n, h n.len

end simplex_category

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

def simplex_is_degenerate {X : sSet} {Δ : simplex_categoryᵒᵖ} (x : X.obj Δ) : Prop :=
∃ (Δ' : simplex_categoryᵒᵖ) (θ : Δ' ⟶ Δ) (hθ₁ : epi θ.unop) (hθ₂ : ¬mono θ.unop)
  (y : X.obj Δ'), x = X.map θ y

def nondegenerate_simplices (X : sSet) (Δ : simplex_categoryᵒᵖ) : set (X.obj Δ) :=
compl simplex_is_degenerate

lemma zero_simplices_are_nondegenerate (X : sSet) : X.nondegenerate_simplices (op [0]) = ⊤ :=
begin
  ext,
  split,
  { intro h,
    simp only [set.top_eq_univ], },
  { intros h₀ h,
    rcases h with ⟨Δ', θ, hθ₁, hθ₂, y, hy⟩,
    apply hθ₂,
    rw simplex_category.mono_iff_injective,
    intros a₁ a₂ h,
    rw [fin.eq_zero a₁, fin.eq_zero a₂], },
end

lemma is_epi_image_of_nondegenerate_simplex (X : sSet) {Δ : simplex_categoryᵒᵖ} (x : X.obj Δ) :
  ∃ (Δ' : simplex_categoryᵒᵖ) (θ : Δ' ⟶ Δ) (hθ : epi θ.unop) (y : X.obj Δ')
    (hy : y ∈ X.nondegenerate_simplices Δ'), x = X.map θ y :=
begin
  induction Δ using opposite.rec,
  induction Δ with n,
  induction n using nat.strong_rec' with n hn,
  cases n,
  { refine ⟨op [0], 𝟙 _, infer_instance, x, _, by simp only [functor_to_types.map_id_apply]⟩,
    rw zero_simplices_are_nondegenerate,
    simp only [set.top_eq_univ], },
 { by_cases x ∈ X.nondegenerate_simplices (op [n.succ]),
    { exact ⟨_, 𝟙 _, infer_instance, x, h, by simp only [functor_to_types.map_id_apply]⟩, },
    { dsimp [nondegenerate_simplices] at h,
      simp only [set.not_not_mem] at h,
      rcases h with ⟨Δ', π, hπ₁, hπ₂, y, hy⟩,
      induction Δ' using opposite.rec,
      induction Δ' with m,
      have hm : m < n.succ,
      { have hπ₁' := (simplex_category.len_le_of_epi hπ₁),
        dsimp at hπ₁',
        cases hπ₁'.lt_or_eq,
        { assumption, },
        { subst h,
          exfalso,
          apply hπ₂,
          rw simplex_category.mono_iff_injective,
          rw simplex_category.epi_iff_surjective at hπ₁,
          rw fintype.injective_iff_bijective at ⊢,
          rw fintype.surjective_iff_bijective at hπ₁,
          assumption, }, },
      rcases hn m hm y with ⟨Δ'', θ, hθ, z, hz, eq⟩,
      haveI := hπ₁,
      haveI := hθ,
      refine ⟨Δ'', θ ≫ π, by { rw unop_comp, apply epi_comp, }, z, hz, _⟩,
      simp only [functor_to_types.map_comp_apply, hy, eq], }, },
end

@[simp]
def splitting_N (X : sSet.{u}) (n : ℕ) : Type u := X.nondegenerate_simplices (op [n])

def splitting (X : sSet.{u}) : simplicial_object.splitting X :=
{ N := X.splitting_N,
  ι := λ n x, x.1,
  mono_ι := λ n, by { rw mono_iff_injective, apply subtype.coe_injective, },
  is_iso' := λ Δ, begin
    rw is_iso_iff_bijective,
    split,
    { sorry, },
    { intro x,
      rcases X.is_epi_image_of_nondegenerate_simplex x with ⟨Δ', θ, hθ, y, hy, eq⟩,
      induction Δ' using opposite.rec,
      induction Δ' with m,
      let y' : X.nondegenerate_simplices (op [m]) := ⟨y, hy⟩,
      let A : simplex_category.splitting_index_set Δ.unop := ⟨_, ⟨_, hθ⟩⟩,
      refine ⟨_, _⟩,
      { apply (simplicial_object.splitting.ι_sum X.splitting_N A),
        exact y', },
      sorry, },
  end, }

end sSet
