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

@[simps]
def zigzag.of_hom {X Y : C} (f : X ⟶ Y) : zigzag W X Y :=
⟨Y, f, 𝟙 Y, left_calculus_of_fractions.id _⟩

@[simps]
def zigzag.id (X : C) := zigzag.of_hom W (𝟙 X)

variable {W}

def zigzag_rel ⦃X Y : C⦄ (z₁ z₂ : zigzag W X Y) : Prop :=
∃ (Z₃ : C) (t₁ : z₁.Z ⟶ Z₃) (t₂ : z₂.Z ⟶ Z₃) (hst : z₁.s ≫ t₁ = z₂.s ≫ t₂)
  (hft : z₁.f ≫ t₁ = z₂.f ≫ t₂), W (z₁.s ≫ t₁)

instance is_equiv_zigzag_rel (X Y : C) :
  is_equiv (zigzag W X Y) (λ z₁ z₂, zigzag_rel z₁ z₂) :=
{ refl := λ z, ⟨z.Z, 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [comp_id] using z.hs⟩,
  symm := λ z₁ z₂ h, begin
    rcases h with ⟨Z₃, t₁, t₂, hst, hft, ht⟩,
    refine ⟨Z₃, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩,
  end,
  trans := λ z₁ z₂ z₃ h₁₂ h₂₃, begin
    rcases h₁₂ with ⟨Z₄, t₁, t₂, hst, hft, ht⟩,
    rcases h₂₃ with ⟨Z₅, u₂, u₃, hsu, hfu, hu⟩,
    rcases left_calculus_of_fractions.ex (z₁.s ≫ t₁) ht (z₃.s ≫ u₃) with ⟨Z₆, v₄, v₅, hv₅, fac⟩,
    simp only [assoc] at fac,
    have eq : z₂.s ≫ u₂ ≫ v₅ = z₂.s ≫ t₂ ≫ v₄,
    { simpa only [← reassoc_of hsu, reassoc_of hst] using fac, },
    rcases left_calculus_of_fractions.ext _ _ _ z₂.hs eq with ⟨Z₇, w, hw, fac'⟩,
    simp only [assoc] at fac',
    refine ⟨Z₇, t₁ ≫ v₄ ≫ w, u₃ ≫ v₅ ≫ w, _, _, _⟩,
    { rw reassoc_of fac, },
    { rw [reassoc_of hft, ← fac', reassoc_of hfu], },
    { rw [← reassoc_of fac, ← reassoc_of hsu, ← assoc],
      exact left_calculus_of_fractions.comp _ _ hu
        (left_calculus_of_fractions.comp _ _ hv₅ hw), },
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
  let H := (left_calculus_of_fractions.ex sq.s' sq.hs' sq'.s').some,
  have eq : z₁₂.s ≫ sq.g ≫ H.g = z₁₂.s ≫ sq'.g ≫ H.s',
  { rw [← reassoc_of sq.fac, ← reassoc_of sq'.fac, H.fac], },
  rcases left_calculus_of_fractions.ext _ _ _ (z₁₂.hs) eq with ⟨Y, t, ht, fac⟩,
  refine ⟨Y, H.g ≫ t, H.s' ≫ t, _, _, _⟩,
  { dsimp [zigzag.comp₀],
    simp only [assoc, reassoc_of H.fac], },
  { dsimp [zigzag.comp₀],
    simp only [assoc] at ⊢ fac,
    rw ← fac, },
  { dsimp [zigzag.comp₀],
    simp only [assoc, ← reassoc_of H.fac],
    refine left_calculus_of_fractions.comp _ _ z₂₃.hs
      (left_calculus_of_fractions.comp _ _ sq'.hs'
        (left_calculus_of_fractions.comp _ _ H.hs' ht)), }
end

variable (W)

def hom (X Y : C) := quot ((λ (z₁ z₂ : zigzag W X Y), zigzag_rel z₁ z₂))

variable {W}

def zigzag.comp {X₁ X₂ X₃ : C} (z₁₂ : zigzag W X₁ X₂) (z₂₃ : zigzag W X₂ X₃) :
  hom W X₁ X₃ :=
quot.mk _ (zigzag.comp₀ z₁₂ z₂₃ (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃.f).some)

lemma zigzag.comp_eq {X₁ X₂ X₃ : C} (z₁₂ : zigzag W X₁ X₂) (z₂₃ : zigzag W X₂ X₃)
  (sq : to_sq z₁₂.s z₁₂.hs z₂₃.f) :
  zigzag.comp z₁₂ z₂₃ = quot.mk _ (zigzag.comp₀ z₁₂ z₂₃ sq) :=
quot.sound (zigzag.comp₀_rel z₁₂ z₂₃ _ _)

def hom.comp {X₁ X₂ X₃ : C} : hom W X₁ X₂ → hom W X₂ X₃ → hom W X₁ X₃ :=
begin
  refine quot.lift₂ (λ z₁₂ z₂₃, zigzag.comp z₁₂ z₂₃) (λ z₁₂ z₂₃ z₂₃' h₂₃, _)
    (λ z₁₂ z₁₂' z₂₃ h₁₂, _),
  { sorry, },
  { sorry, },
end

lemma hom.comp_eq {X₁ X₂ X₃ : C} (z₁₂ : zigzag W X₁ X₂) (z₂₃ : zigzag W X₂ X₃)
  (sq : to_sq z₁₂.s z₁₂.hs z₂₃.f) : hom.comp (quot.mk _ z₁₂) (quot.mk _ z₂₃) =
  quot.mk _ (zigzag.comp₀ z₁₂ z₂₃ sq) :=
begin
  let sq' := (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃.f).some,
  have eq : (quot.mk _ (z₁₂.comp₀ z₂₃ sq) : hom W _ _) = quot.mk _ (z₁₂.comp₀ z₂₃ sq'),
  { rw [← zigzag.comp_eq, ← zigzag.comp_eq], },
  simpa only [eq],
end

include W

variable (W)

structure localization :=
(obj : C)

instance : category (localization W) :=
{ hom := λ X Y, hom W X.obj Y.obj,
  id := λ X, quot.mk _ (zigzag.id W X.obj),
  comp := λ X₁ X₂ X₃, hom.comp,
  id_comp' := λ X Y f, begin
    cases surjective_quot_mk _ f with g hg,
    subst hg,
    dsimp [hom.comp],
    let sq : to_sq (𝟙 X.obj) (left_calculus_of_fractions.id X.obj : W (𝟙 X.obj)) g.f :=
      ⟨g.Z, g.f, 𝟙 g.Z, left_calculus_of_fractions.id g.Z, by rw [id_comp, comp_id]⟩,
    rw zigzag.comp_eq (zigzag.id W X.obj) g sq,
    congr' 1,
    dsimp [zigzag.comp₀],
    cases g,
    tidy,
  end,
  comp_id' := λ X Y f, begin
    cases surjective_quot_mk _ f with g hg,
    subst hg,
    dsimp [hom.comp],
    let sq : to_sq g.s g.hs (𝟙 Y.obj) := ⟨g.Z, 𝟙 g.Z, g.s, g.hs, by rw [id_comp, comp_id]⟩,
    rw zigzag.comp_eq g (zigzag.id W Y.obj) sq,
    congr' 1,
    dsimp [zigzag.comp₀],
    cases g,
    tidy,
  end,
  assoc' := λ X₁ X₂ X₃ X₄ f₁₂ f₂₃ f₃₄, begin
    cases surjective_quot_mk _ f₁₂ with z₁₂ h₁₂,
    cases surjective_quot_mk _ f₂₃ with z₂₃ h₂₃,
    cases surjective_quot_mk _ f₃₄ with z₃₄ h₃₄,
    let sq₁₃ := (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃.f).some,
    let sq₂₄ := (left_calculus_of_fractions.ex z₂₃.s z₂₃.hs z₃₄.f).some,
    dsimp,
    let H := (left_calculus_of_fractions.ex sq₁₃.s' sq₁₃.hs' sq₂₄.g).some,
    let sq : to_sq (z₁₂.comp₀ z₂₃ sq₁₃).s (z₁₂.comp₀ z₂₃ sq₁₃).hs z₃₄.f := begin
      refine ⟨H.obj, H.g, sq₂₄.s' ≫ H.s', left_calculus_of_fractions.comp _ _ sq₂₄.hs' H.hs', _⟩,
      dsimp [zigzag.comp₀],
      rw [assoc, ← H.fac, reassoc_of sq₂₄.fac],
    end,
    let sq' : to_sq z₁₂.s z₁₂.hs (z₂₃.comp₀ z₃₄ sq₂₄).f := begin
      refine ⟨H.obj, sq₁₃.g ≫ H.g, H.s', H.hs', _⟩,
      dsimp [zigzag.comp₀],
      rw [assoc, H.fac, reassoc_of sq₁₃.fac],
    end,
    simp only [← h₁₂, ← h₂₃, ← h₃₄],
    rw [hom.comp_eq z₁₂ z₂₃ sq₁₃, hom.comp_eq z₂₃ z₃₄ sq₂₄,
      hom.comp_eq (z₁₂.comp₀ z₂₃ sq₁₃) z₃₄ sq, hom.comp_eq z₁₂ (z₂₃.comp₀ z₃₄ sq₂₄) sq'],
    congr' 1,
    dsimp [zigzag.comp₀],
    tidy,
  end, }

end left_calculus_of_fractions

end category_theory
