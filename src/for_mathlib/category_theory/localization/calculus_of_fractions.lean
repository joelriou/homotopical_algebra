import for_mathlib.category_theory.localization.predicate

noncomputable theory

namespace category_theory

open category

variables {C : Type*} [category C] {W : morphism_property C}

structure left_calculus_of_fractions.to_sq
  {X' X Y : C} (s : X ⟶ X') (hs : W s) (f : X ⟶ Y) :=
(obj : C)
(g : X' ⟶ obj)
(s' : Y ⟶ obj)
(hs' : W s')
(fac : f ≫ s' = s ≫ g)

variable (W)

class left_calculus_of_fractions :=
(id : ∀ (X : C), W (𝟙 X))
(comp : W.stable_under_composition)
(ex : ∀ ⦃X' X Y : C⦄ (s : X ⟶ X') (hs : W s) (u : X ⟶ Y),
  nonempty (left_calculus_of_fractions.to_sq s hs u))
(ext : ∀ ⦃X' X Y : C⦄ (f₁ f₂ : X ⟶ Y) (s : X' ⟶ X) (hs : W s) (eq : s ≫ f₁ = s ≫ f₂),
  ∃ (Y' : C) (t : Y ⟶ Y') (ht : W t), f₁ ≫ t = f₂ ≫ t)

namespace left_calculus_of_fractions

variables (W) [left_calculus_of_fractions W]

structure zigzag (X Y : C) :=
(Z : C) (f : X ⟶ Z) (s : Y ⟶ Z) (hs : W s)

def zigzag.of_hom {X Y : C} (f : X ⟶ Y) : zigzag W X Y :=
⟨Y, f, 𝟙 Y, left_calculus_of_fractions.id _⟩

def zigzag.id (X : C) := zigzag.of_hom W (𝟙 X)

variable {W}

def zigzag_rel ⦃X Y : C⦄ (z₁ z₂ : zigzag W X Y) : Prop :=
∃ (Z₃ : C) (t₁ : z₁.Z ⟶ Z₃) (t₂ : z₂.Z ⟶ Z₃) (ht₁₂ : z₁.s ≫ t₁ = z₂.s ≫ t₂), W (z₁.s ≫ t₁)

instance is_equiv_zigzag_rel (X Y : C) :
  is_equiv (zigzag W X Y) (λ z₁ z₂, zigzag_rel z₁ z₂) :=
{ refl := λ z, ⟨z.Z, 𝟙 _, 𝟙 _, rfl, by simpa only [comp_id] using z.hs⟩,
  symm := λ z₁ z₂ h, begin
    rcases h with ⟨Z₃, t₁, t₂, ht₁₂, ht₁⟩,
    refine ⟨Z₃, t₂, t₁, ht₁₂.symm, by simpa only [← ht₁₂] using ht₁⟩,
  end,
  trans := λ z₁ z₂ z₃ h₁₂ h₂₃, begin
    rcases h₁₂ with ⟨Z₄, t₁, t₂, ht₁₂, ht₁⟩,
    rcases h₂₃ with ⟨Z₅, u₂, u₃, hu₂₃, hu₂⟩,
    rcases left_calculus_of_fractions.ex (z₁.s ≫ t₁) ht₁ (z₃.s ≫ u₃) with ⟨Z₆, v₄, v₅, hv₅, fac⟩,
    simp only [assoc] at fac,
    refine ⟨Z₆, t₁ ≫ v₄, u₃ ≫ v₅, fac.symm, _⟩,
    rw [← fac, ← assoc, ← hu₂₃],
    exact left_calculus_of_fractions.comp _ _ hu₂ hv₅,
  end, }

variable {W}

def zigzag.comp₀ {X₁ X₂ X₃ : C} (z₁₂ : zigzag W X₁ X₂) (z₂₃ : zigzag W X₂ X₃)
  (sq : to_sq z₁₂.s z₁₂.hs z₂₃.f) :
  zigzag W X₁ X₃ :=
⟨sq.obj, z₁₂.f ≫ sq.g , z₂₃.s ≫ sq.s', left_calculus_of_fractions.comp _ _ z₂₃.hs sq.hs'⟩

lemma zigzag.comp₀_rel {X₁ X₂ X₃ : C} (z₁₂ : zigzag W X₁ X₂) (z₂₃ : zigzag W X₂ X₃)
  (sq sq' : to_sq z₁₂.s z₁₂.hs z₂₃.f) :
  zigzag_rel (zigzag.comp₀ z₁₂ z₂₃ sq) (zigzag.comp₀ z₁₂ z₂₃ sq') :=
begin
  sorry,
end

--structure localization := (obj : C)

end left_calculus_of_fractions

end category_theory
