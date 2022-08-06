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

lemma is_iso_of_epi_and_card [hθ : epi θ] (h : X.len = Y.len) : is_iso θ :=
begin
  apply is_iso_of_bijective,
  split,
  { by_contra h',
    rw epi_iff_surjective at hθ,
    simpa only [fintype.card_fin, add_lt_add_iff_right, h, lt_self_iff_false]
      using fintype.card_lt_of_surjective_not_injective _ hθ h', },
  { change function.surjective θ.to_order_hom,
    rw ← epi_iff_surjective,
    apply_instance, },
end

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
  (hy : x.1 = X.map θ y) : is_iso θ :=
begin
  suffices : is_iso θ.unop,
  { haveI := this,
    change is_iso θ.unop.op,
    apply_instance, },
  apply simplex_category.is_iso_of_bijective,
  split,
  { change function.injective θ.unop.to_order_hom,
    rw ← simplex_category.mono_iff_injective,
    by_contra,
    exact x.2 ⟨Δ', θ, hθ, h, y, hy⟩, },
  { change function.surjective θ.unop.to_order_hom,
    rw ← simplex_category.epi_iff_surjective,
    exact hθ, },
end

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
  (hy₁ : y₁ ∈ X.nondegenerate_simplices Δ₁)
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
  { exact image_of_nondegenerate_simplex_uniqueness₀ X y₁ y₂ hy₁ θ₁ θ₂ hθ₁ hθ₂ eq, },
  { exact image_of_nondegenerate_simplex_uniqueness₀ X y₂ y₁ hy₂ θ₂ θ₁ hθ₂ hθ₁ eq.symm, },
end

lemma image_of_nondegenerate_simplex_uniqueness₂ (X : sSet)
  {Δ Δ' : simplex_categoryᵒᵖ} (y₁ : X.obj Δ') (y₂ : X.obj Δ')
  (hy₁ : y₁ ∈ X.nondegenerate_simplices Δ') (hy₂ : y₂ ∈ X.nondegenerate_simplices Δ')
  (θ₁ : Δ' ⟶ Δ) (θ₂ : Δ' ⟶ Δ) (hθ₁ : epi θ₁.unop) (hθ₂ : epi θ₂.unop)
  (eq : X.map θ₁ y₁ = X.map θ₂ y₂) : y₁ = y₂ :=
begin
  haveI := split_epi_of_epi θ₁.unop,
  let f := section_ θ₁.unop ≫ θ₂.unop,
  have eq₁ : y₁ = X.map f.op y₂,
  { dsimp only [f],
    rw [op_comp, X.map_comp', quiver.hom.op_unop, ← eq, ← X.map_comp'],
    change _ = X.map (θ₁.unop.op ≫ _) _,
    rw [← op_comp, split_epi.id θ₁.unop, op_id, X.map_id, types_id_apply], },
  have eq₂ := eq₁,
  let F := limits.image.mono_factorisation f,
  rw [← F.fac, op_comp, X.map_comp'] at eq₂,
  haveI : epi F.e := by { simp only [limits.as_factor_thru_image], apply_instance, },
  haveI he := is_iso_of_nondegenerate_simplices ⟨y₁, hy₁⟩ F.e.op infer_instance _ eq₂,
  haveI : is_iso F.e,
  { change is_iso F.e.op.unop,
    apply_instance, },
  haveI : mono f,
  { rw ← F.fac,
    apply mono_comp, },
  simpa only [simplex_category.eq_id_of_mono f, op_id, X.map_id, types_id_apply] using eq₁,
end

lemma ext_epi_of_sections {Δ₁ Δ₂ : simplex_category} (θ₁ θ₂ : Δ₁ ⟶ Δ₂) [epi θ₁]
  (h : ∀ (s : split_epi θ₁), s.section_ ≫ θ₂ = 𝟙 _) : θ₁ = θ₂ :=
begin
  ext1, ext1, ext1 x,
  have h₂ : ∃ (s : split_epi θ₁), s.section_.to_order_hom (θ₁.to_order_hom x) = x,
  { let s₀ := split_epi_of_epi θ₁,
    let α : fin (Δ₂.len+1) → fin (Δ₁.len+1) := λ y,
      if (y = θ₁.to_order_hom x) then x else s₀.section_.to_order_hom y,
    have hα : ∀ y, θ₁.to_order_hom (α y) = y,
    { intro y,
      dsimp [α],
      split_ifs with h₁,
      { rw ← h₁, },
      { have h₃ := congr_arg order_hom.to_fun (congr_arg simplex_category.hom.to_order_hom s₀.id'),
        exact congr_fun h₃ y, }, },
    let β : Δ₂ ⟶ Δ₁ := simplex_category.hom.mk ⟨α, begin
      intros x₁ x₂,
      contrapose,
      intro h,
      simp only [not_le] at h ⊢,
      suffices : x₂ ≤ x₁,
      { cases this.lt_or_eq with h₁ h₂,
        { assumption, },
        { exfalso,
          simpa only [h₂, lt_self_iff_false] using h, }, },
      simpa only [hα, order_hom.to_fun_eq_coe] using θ₁.to_order_hom.monotone' h.le,
    end⟩,
    refine ⟨⟨β, _⟩, _⟩,
    { ext1, ext1, ext1 y,
      apply hα, },
    { simp only [simplex_category.hom.to_order_hom_mk, order_hom.coe_fun_mk,
        ite_eq_left_iff, eq_self_iff_true, not_true, is_empty.forall_iff], }, },
  rcases h₂ with ⟨s, hs⟩,
  rw ← hs,
  have eq := h s,
  have h₃ := s.id',
  simp only [auto_param_eq] at h₃,
  rw ← h₃ at eq,
  have h₄ : (θ₁ ≫ s.section_ ≫ θ₁).to_order_hom x =
    (θ₁ ≫ s.section_ ≫ θ₂).to_order_hom x := by rw eq,
  exact h₄,
end

lemma image_of_nondegenerate_simplex_uniqueness₃ (X : sSet)
  {Δ Δ' : simplex_categoryᵒᵖ} (y : X.obj Δ')
  (hy : y ∈ X.nondegenerate_simplices Δ')
  (θ₁ : Δ' ⟶ Δ) (θ₂ : Δ' ⟶ Δ) (hθ₁ : epi θ₁.unop) (hθ₂ : epi θ₂.unop)
  (eq : X.map θ₁ y = X.map θ₂ y) : θ₁ = θ₂ :=
begin
  apply quiver.hom.unop_inj,
  apply ext_epi_of_sections,
  introI s,
  let f := section_ θ₁.unop ≫ θ₂.unop,
  change f = 𝟙 _,
  have eq₁ : y = X.map f.op y,
  { dsimp only [f],
    rw [op_comp, X.map_comp', quiver.hom.op_unop, ← eq, ← X.map_comp'],
    change _ = X.map (θ₁.unop.op ≫ _) _,
    rw [← op_comp, split_epi.id θ₁.unop, op_id, X.map_id, types_id_apply], },
  let F := limits.image.mono_factorisation f,
  rw [← F.fac, op_comp, X.map_comp'] at eq₁,
  haveI : epi F.e := by { simp only [limits.as_factor_thru_image], apply_instance, },
  haveI he := is_iso_of_nondegenerate_simplices ⟨y, hy⟩ F.e.op infer_instance _ eq₁,
  haveI : is_iso F.e,
  { change is_iso F.e.op.unop,
    apply_instance, },
  haveI : mono f,
  { rw ← F.fac,
    apply mono_comp, },
  exact simplex_category.eq_id_of_mono f,
end

@[simp]
def splitting_map (X : sSet.{u}) (Δ : simplex_categoryᵒᵖ) :
  sigma (simplicial_object.splitting.summand
    (λ n, (X.nondegenerate_simplices (op [n]) : Type u)) Δ.unop) → X.obj Δ :=
λ s, X.map s.1.e.op s.2.1

lemma splitting_map_bijective (X : sSet.{u}) (Δ : simplex_categoryᵒᵖ) :
  function.bijective (X.splitting_map Δ) :=
begin
  split,
  { rintros ⟨⟨Δ₁, θ₁, hθ₁⟩, y₁, hy₁⟩ ⟨⟨Δ₂, θ₂, hθ₂⟩, y₂, hy₂⟩ eq,
    have h₁ := X.image_of_nondegenerate_simplex_uniqueness₁ y₁ y₂ hy₁ hy₂ θ₁.op θ₂.op
      hθ₁ hθ₂ eq,
    simp only [simplex_category.mk_len, op_inj_iff] at h₁,
    subst h₁,
    have h₂ := X.image_of_nondegenerate_simplex_uniqueness₂ y₁ y₂ hy₁ hy₂ θ₁.op θ₂.op
      hθ₁ hθ₂ eq,
    subst h₂,
    have h₃ := X.image_of_nondegenerate_simplex_uniqueness₃ y₁ hy₁ θ₁.op θ₂.op hθ₁ hθ₂ eq,
    have h₃' : θ₁ = θ₂ := by { apply quiver.hom.op_inj, exact h₃, },
    subst h₃', },
  { intro y,
    rcases X.is_epi_image_of_nondegenerate_simplex y with ⟨Δ', θ, hθ, y, hy, eq⟩,
    exact ⟨⟨⟨Δ'.unop, ⟨θ.unop, hθ⟩⟩, ⟨y, hy⟩⟩, eq.symm⟩, },
end

@[simps]
def splitting (X : sSet.{u}) : simplicial_object.splitting X :=
begin
  let N : ℕ → Type u := λ n, X.nondegenerate_simplices (op [n]),
  let ι : Π (n : ℕ), N n → X.obj (op [n]) := λ n, subtype.val,
  exact
  { N := N,
    ι := ι,
    mono_ι := λ n, by { rw mono_iff_injective, apply subtype.coe_injective, },
    is_iso' := λ Δ, begin
      rw is_iso_iff_bijective,
      let α := X.splitting_map Δ,
      let β := simplicial_object.splitting.map N ι Δ,
      let γ := concrete.coproduct_map (simplicial_object.splitting.summand N Δ.unop),
      have hγ : function.bijective γ := concrete.coproduct_map_bijective _,
      change function.bijective β,
      have eq : β ∘ γ = α,
      { ext s,
        rcases s with ⟨A, x⟩,
        dsimp [α, β, γ],
        have h := comp_apply (simplicial_object.splitting.ι_sum N A)
          (simplicial_object.splitting.map N ι Δ) x,
        simp only [concrete_category.has_coe_to_fun_Type,
          simplicial_object.splitting.ι_sum, simplicial_object.splitting.map] at h,
        erw [colimit.ι_desc, cofan.mk_ι_app] at h,
        exact h.symm, },
      rw [← function.bijective.of_comp_iff β hγ, eq],
      apply splitting_map_bijective,
    end, },
end

end sSet
