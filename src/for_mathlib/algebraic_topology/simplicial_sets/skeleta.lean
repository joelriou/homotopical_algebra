import algebraic_topology.simplicial_set
import category_theory.limits.kan_extension
import for_mathlib.split_simplicial_object
import for_mathlib.category_theory.limits.concrete

noncomputable theory

universes u

open category_theory
open category_theory.limits
open opposite
open_locale simplicial

namespace simplex_category

section
variables {X Y : simplex_category} (θ : X ⟶ Y)
instance : strong_epi (factor_thru_image θ) :=
strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
  (has_strong_epi_mono_factorisations.has_fac θ).some

instance : epi (factor_thru_image θ) := strong_epi.epi
end

protected def rec {F : Π (X : simplex_category), Sort u} (h : ∀ (n : ℕ), F [n]) :
  Π X, F X := λ n, h n.len

end simplex_category

namespace sSet

lemma map_comp' (X : sSet) {Δ₀ Δ₁ Δ₂ : simplex_categoryᵒᵖ} (θ : Δ₀ ⟶ Δ₁) (θ' : Δ₁ ⟶ Δ₂)
  (x : X.obj Δ₀) : X.map (θ ≫ θ') x = X.map θ' (X.map θ x) :=
congr_fun (X.map_comp θ θ') x

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

@[simp]
def nondegenerate_simplices (X : sSet) (Δ : simplex_categoryᵒᵖ) : set (X.obj Δ) :=
compl simplex_is_degenerate

lemma is_iso_of_nondegenerate_simplices {X : sSet} {Δ Δ' : simplex_categoryᵒᵖ}
  (x : X.nondegenerate_simplices Δ) (θ : Δ' ⟶ Δ) (hθ : epi θ.unop) (y : X.obj Δ')
  (hy : x.1 = X.map θ y) : is_iso θ := sorry

@[simp]
def ι_nondegenerate_simplices (X : sSet.{u}) (Δ : simplex_categoryᵒᵖ) :
  (X.nondegenerate_simplices Δ : Type u) ⟶ X.obj Δ := subtype.val

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

lemma splitting.sum.concrete_bijective (N : ℕ → Type u) (Δ : simplex_category) :
  function.bijective (limits.concrete.coproduct_map (simplicial_object.splitting.summand N Δ) :
    sigma (simplicial_object.splitting.summand N Δ) → simplicial_object.splitting.sum N Δ) :=
limits.concrete.coproduct_map_bijective _

lemma image_of_nondegenerate_simplex_uniqueness₀ (X : sSet)
  {Δ Δ₁ Δ₂ : simplex_categoryᵒᵖ} (y₁ : X.obj Δ₁) (y₂ : X.obj Δ₂)
  (hy₁ : y₁ ∈ X.nondegenerate_simplices Δ₁) (hy₂ : y₂ ∈ X.nondegenerate_simplices Δ₂)
  (θ₁ : Δ₁ ⟶ Δ) (θ₂ : Δ₂ ⟶ Δ) (hθ₁ : epi θ₁.unop) (hθ₂ : epi θ₂.unop)
  (eq : X.map θ₁ y₁ = X.map θ₂ y₂) : Δ₁.unop.len ≤ Δ₂.unop.len :=
begin
  haveI := split_epi_of_epi θ₁.unop,
  let f := section_ θ₁.unop ≫ θ₂.unop,
  have eq₁ : y₁ = X.map f.op y₂,
  { dsimp only [f],
    rw [op_comp, X.map_comp', quiver.hom.op_unop, ← eq, ← X.map_comp'],
    change _ = X.map (θ₁.unop.op ≫ _) _,
    rw [← op_comp, split_epi.id θ₁.unop, op_id, X.map_id, types_id_apply], },
  let F := limits.image.mono_factorisation f,
  rw [← F.fac, op_comp, X.map_comp'] at eq₁,
  haveI : epi F.e := by { simp only [limits.as_factor_thru_image], apply_instance, },
  haveI he := is_iso_of_nondegenerate_simplices ⟨y₁, hy₁⟩ F.e.op infer_instance _ eq₁,
  haveI : is_iso F.e,
  { change is_iso F.e.op.unop,
    apply_instance, },
  have hf : mono f,
  { rw ← F.fac,
    apply mono_comp, },
  exact simplex_category.len_le_of_mono hf,
end

lemma image_of_nondegenerate_simplex_uniqueness₁ (X : sSet)
  {Δ Δ₁ Δ₂ : simplex_categoryᵒᵖ} (y₁ : X.obj Δ₁) (y₂ : X.obj Δ₂)
  (hy₁ : y₁ ∈ X.nondegenerate_simplices Δ₁) (hy₂ : y₂ ∈ X.nondegenerate_simplices Δ₂)
  (θ₁ : Δ₁ ⟶ Δ) (θ₂ : Δ₂ ⟶ Δ) (hθ₁ : epi θ₁.unop) (hθ₂ : epi θ₂.unop)
  (eq : X.map θ₁ y₁ = X.map θ₂ y₂) : Δ₁ = Δ₂ :=
begin
  unfreezingI { induction Δ₁ using opposite.rec, induction Δ₂ using opposite.rec, },
  congr,
  ext,
  apply le_antisymm,
  { exact image_of_nondegenerate_simplex_uniqueness₀ X y₁ y₂ hy₁ hy₂ θ₁ θ₂ hθ₁ hθ₂ eq, },
  { exact image_of_nondegenerate_simplex_uniqueness₀ X y₂ y₁ hy₂ hy₁ θ₂ θ₁ hθ₂ hθ₁ eq.symm, },
end

lemma image_of_nondegenerate_simplex_uniqueness₂ (X : sSet) {Δ : simplex_categoryᵒᵖ}
  {Δ Δ' : simplex_categoryᵒᵖ} (y₁ : X.obj Δ') (y₂ : X.obj Δ')
  (hy₁ : y₁ ∈ X.nondegenerate_simplices Δ') (hy₂ : y₂ ∈ X.nondegenerate_simplices Δ')
  (θ₁ : Δ' ⟶ Δ) (θ₂ : Δ' ⟶ Δ) (hθ₁ : epi θ₁.unop) (hθ₂ : epi θ₂.unop)
  (eq : X.map θ₁ y₁ = X.map θ₂ y₂) : θ₁ = θ₂ ∧ y₁ = y₂ := sorry

@[simps]
def splitting (X : sSet.{u}) : simplicial_object.splitting X :=
{ N := λ n, X.nondegenerate_simplices (op [n]),
  ι := λ n, subtype.val,
  mono_ι := λ n, by { rw mono_iff_injective, apply subtype.coe_injective, },
  is_iso' := λ Δ, begin
    rw is_iso_iff_bijective,
    split,
    { intros y₁ y₂ hy,
      rcases (splitting.sum.concrete_bijective _ Δ.unop).2 y₁ with ⟨⟨θ₁, ⟨z₁, hz₁⟩⟩, eq₁⟩,
      rcases (splitting.sum.concrete_bijective _ Δ.unop).2 y₂ with ⟨⟨θ₂, ⟨z₂, hz₂⟩⟩, eq₂⟩,
      substs eq₁ eq₂,
      sorry, },
    { intro x,
      rcases X.is_epi_image_of_nondegenerate_simplex x with ⟨Δ', θ, hθ, y, hy, eq⟩,
      induction Δ' using opposite.rec,
      induction Δ' with m,
      let F := (simplicial_object.splitting.ι_sum
        (λ n, (X.nondegenerate_simplices (op [n]) : Type u)) ⟨[m], ⟨θ.unop, hθ⟩⟩),
      use F ⟨y, hy⟩,
      have h := comp_apply F (simplicial_object.splitting.map (λ n, subtype.val) Δ),
      simp only [concrete_category.has_coe_to_fun_Type] at h,
      erw [← h, limits.colimit.ι_desc, limits.cofan.mk_ι_app, eq],
      refl, },
  end, }

end sSet
