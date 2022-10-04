import algebra.category.Group.preadditive

noncomputable theory

universe u

open category_theory category_theory.category

namespace algebra

namespace homology

def concrete_exact {X₁ X₂ X₃ : AddCommGroup.{u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) : Prop :=
∀ (x₂ : X₂) (h : f₂ x₂ = 0), ∃ (x₁ : X₁), f₁ x₁ = x₂

def concrete_exact.lift {X₁ X₂ X₃ : AddCommGroup.{u}} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
  (h : concrete_exact f₁ f₂) {x₂ : X₂} (zero : f₂ x₂ = 0) : X₁ :=
(h x₂ zero).some

@[simp]
lemma concrete_exact.lift_spec {X₁ X₂ X₃ : AddCommGroup.{u}} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
  (h : concrete_exact f₁ f₂) {x₂ : X₂} (zero : f₂ x₂ = 0) :
  f₁ (h.lift zero) = x₂ := (h x₂ zero).some_spec

lemma injective_iff {X₁ X₂ : AddCommGroup.{u}} (f : X₁ ⟶ X₂) :
  function.injective f ↔ ∀ (x₁ : X₁) (h : f x₁ = 0), x₁ = 0 :=
begin
  split,
  { intros h x₁ hx₁,
    apply h,
    rw [hx₁, map_zero], },
  { intros h x₁ x₂ hx,
    rw ← sub_eq_zero,
    apply h,
    rw [map_sub, hx, sub_self], },
end

variables (A : Type*) [category A] [preadditive A]

structure five_complex :=
(X₁ X₂ X₃ X₄ X₅: A)
(f₁ : X₁ ⟶ X₂)
(f₂ : X₂ ⟶ X₃)
(f₃ : X₃ ⟶ X₄)
(f₄ : X₄ ⟶ X₅)
(h₁₂ : f₁ ≫ f₂ = 0)
(h₂₃ : f₂ ≫ f₃ = 0)
(h₃₄ : f₃ ≫ f₄ = 0)

namespace five_complex

variable {A}

@[ext]
structure hom (E E' : five_complex A) :=
(τ₁ : E.X₁ ⟶ E'.X₁)
(τ₂ : E.X₂ ⟶ E'.X₂)
(τ₃ : E.X₃ ⟶ E'.X₃)
(τ₄ : E.X₄ ⟶ E'.X₄)
(τ₅ : E.X₅ ⟶ E'.X₅)
(comm₁ : E.f₁ ≫ τ₂ = τ₁ ≫ E'.f₁)
(comm₂ : E.f₂ ≫ τ₃ = τ₂ ≫ E'.f₂)
(comm₃ : E.f₃ ≫ τ₄ = τ₃ ≫ E'.f₃)
(comm₄ : E.f₄ ≫ τ₅ = τ₄ ≫ E'.f₄)

instance : category (five_complex A) :=
{ hom := hom,
  id := λ E, hom.mk (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (by rw [id_comp,comp_id])
    (by rw [id_comp,comp_id]) (by rw [id_comp,comp_id]) (by rw [id_comp,comp_id]),
  comp := λ E E' E'' φ φ', hom.mk (φ.τ₁ ≫ φ'.τ₁) (φ.τ₂ ≫ φ'.τ₂) (φ.τ₃ ≫ φ'.τ₃)
    (φ.τ₄ ≫ φ'.τ₄) (φ.τ₅ ≫ φ'.τ₅) (by rw [assoc, reassoc_of (φ.comm₁), φ'.comm₁])
    (by rw [assoc, reassoc_of (φ.comm₂), φ'.comm₂])
    (by rw [assoc, reassoc_of (φ.comm₃), φ'.comm₃])
    (by rw [assoc, reassoc_of (φ.comm₄), φ'.comm₄]), }

example : ℕ := 42

structure exact (E : five_complex (AddCommGroup.{u})) : Prop :=
(ex₂ : concrete_exact E.f₁ E.f₂)
(ex₃ : concrete_exact E.f₂ E.f₃)
(ex₄ : concrete_exact E.f₃ E.f₄)


lemma concrete_comm₁ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₁ : E.X₁) : φ.τ₂ (E.f₁ x₁) = E'.f₁ (φ.τ₁ x₁) :=
by simp only [← comp_apply, φ.comm₁]

lemma concrete_comm₂ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₂ : E.X₂) : φ.τ₃ (E.f₂ x₂) = E'.f₂ (φ.τ₂ x₂) :=
by simp only [← comp_apply, φ.comm₂]

lemma concrete_comm₃ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₃ : E.X₃) : φ.τ₄ (E.f₃ x₃) = E'.f₃ (φ.τ₃ x₃) :=
by simp only [← comp_apply, φ.comm₃]

lemma concrete_comm₄ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₄ : E.X₄) : φ.τ₅ (E.f₄ x₄) = E'.f₄ (φ.τ₄ x₄) :=
by simp only [← comp_apply, φ.comm₄]


lemma five_lemma_injective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₁ : function.surjective φ.τ₁)
  (h₂ : function.injective φ.τ₂)
  (h₄ : function.injective φ.τ₄) :
  function.injective φ.τ₃ :=
begin
  rw injective_iff at ⊢ h₄,
  intros x₃ hx₃,
  have eq₁ : E.f₃ x₃ = 0,
  { apply h₄,
    rw [concrete_comm₃, hx₃, map_zero], },
  let x₂ := hE.ex₃.lift eq₁,
  have hx₂ : E.f₂ x₂ = x₃ := hE.ex₃.lift_spec eq₁,
  let x₂' := φ.τ₂ x₂,
  have eq₂ : E'.f₂ x₂' = 0,
  { dsimp only [x₂'],
    rw [← concrete_comm₂, concrete_exact.lift_spec, hx₃], },
  let x₁' := hE'.ex₂.lift eq₂,
  obtain ⟨x₁, hx₁⟩ := h₁ x₁',
  have eq₃ : E.f₁ x₁ = x₂,
  { apply h₂,
    rw [concrete_comm₁, hx₁, concrete_exact.lift_spec], },
  rw [← hx₂, ← eq₃, ← comp_apply, E.h₁₂, AddCommGroup.zero_apply],
end

lemma five_lemma_surjective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₂ : function.surjective φ.τ₂)
  (h₄ : function.surjective φ.τ₄)
  (h₅ : function.injective φ.τ₅) :
  function.surjective φ.τ₃ :=
begin
  intro x₃',
  obtain ⟨x₄, hx₄⟩ := h₄ (E'.f₃ x₃'),
  have eq₁ : E.f₄ x₄ = 0,
  { apply h₅,
    rw [concrete_comm₄, hx₄, ← comp_apply, E'.h₃₄, AddCommGroup.zero_apply, map_zero], },
  let x₃ := hE.ex₄.lift eq₁,
  have hx₃ : E.f₃ x₃ = x₄ := by simp only [concrete_exact.lift_spec],
  let δ := x₃' - φ.τ₃ x₃,
  have eq₂ : E'.f₃ δ = 0,
  { dsimp only [δ],
    simp only [map_sub, ← concrete_comm₃, hx₃, hx₄, sub_self], },
  let ε := hE'.ex₃.lift eq₂,
  have hε : E'.f₂ ε = δ := by simp only [concrete_exact.lift_spec],
  obtain ⟨x₂, hx₂⟩ := h₂ ε,
  refine ⟨x₃ + E.f₂ x₂, _⟩,
  rw [map_add, concrete_comm₂, hx₂, hε, add_sub_cancel'_right],
end

lemma five_lemma_bijective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₁ : function.bijective φ.τ₁)
  (h₂ : function.bijective φ.τ₂)
  (h₄ : function.bijective φ.τ₄)
  (h₅ : function.bijective φ.τ₅) :
  function.bijective φ.τ₃ :=
⟨five_lemma_injective φ hE hE' h₁.2 h₂.1 h₄.1, five_lemma_surjective φ hE hE' h₂.2 h₄.2 h₅.1⟩

end five_complex

end homology

end algebra
