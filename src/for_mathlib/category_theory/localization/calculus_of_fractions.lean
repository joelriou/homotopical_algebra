import for_mathlib.category_theory.localization.predicate
import for_mathlib.category_theory.functor_misc

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

namespace zigzag_rel

lemma refl {X Y : C} (z : zigzag W X Y) : zigzag_rel z z :=
⟨z.Z, 𝟙 _, 𝟙 _, rfl, rfl, by simpa only [comp_id] using z.hs⟩

lemma symm {X Y : C} {z₁ z₂ : zigzag W X Y} (h : zigzag_rel z₁ z₂) : zigzag_rel z₂ z₁ :=
begin
  rcases h with ⟨Z₃, t₁, t₂, hst, hft, ht⟩,
  refine ⟨Z₃, t₂, t₁, hst.symm, hft.symm, by simpa only [← hst] using ht⟩,
end

lemma trans {X Y : C} {z₁ z₂ z₃ : zigzag W X Y} (h₁₂ : zigzag_rel z₁ z₂)
  (h₂₃ : zigzag_rel z₂ z₃) : zigzag_rel z₁ z₃ :=
begin
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
end

end zigzag_rel

instance is_equiv_zigzag_rel (X Y : C) :
  is_equiv (zigzag W X Y) (λ z₁ z₂, zigzag_rel z₁ z₂) :=
{ refl := zigzag_rel.refl,
  symm := λ z₁ z₂, zigzag_rel.symm,
  trans := λ z₁ z₂ z₃, zigzag_rel.trans, }

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
  { dsimp,
    let sq := (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃.f).some,
    let sq' := (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃'.f).some,
    rw [zigzag.comp_eq _ _ sq, zigzag.comp_eq _ _ sq'],
    apply quot.sound,
    rcases h₂₃ with ⟨Y, t, t', hst, hft, ht⟩,
    let H₀ := (left_calculus_of_fractions.ex sq.s' sq.hs' t).some,
    let H₀' := (left_calculus_of_fractions.ex sq'.s' sq'.hs' t').some,
    have h : W (z₂₃.s ≫ sq.s' ≫ H₀.g),
    { rw [← H₀.fac, ← assoc],
      exact left_calculus_of_fractions.comp _ _ ht H₀.hs', },
    let H₁ := (left_calculus_of_fractions.ex H₀.s' H₀.hs' H₀'.s').some,
    have eq : z₁₂.s ≫ sq.g ≫ H₀.g ≫ H₁.g = z₁₂.s ≫ sq'.g ≫ H₀'.g ≫ H₁.s',
    { simp only [← reassoc_of sq.fac, ← reassoc_of sq'.fac,← reassoc_of H₀.fac,
        ← reassoc_of H₀'.fac, reassoc_of hft, H₁.fac], },
    rcases left_calculus_of_fractions.ext _ _ _ z₁₂.hs eq with ⟨Z, u, hu, fac⟩,
    simp only [assoc] at fac,
    refine ⟨Z, H₀.g ≫ H₁.g ≫ u, H₀'.g ≫ H₁.s' ≫ u, _, _, _⟩; dsimp [zigzag.comp₀],
    { simp only [assoc, ← reassoc_of H₀.fac, ← reassoc_of H₀'.fac,
        reassoc_of hst, reassoc_of H₁.fac], },
    { simp only [assoc, fac], },
    { simp only [assoc],
      rw [← reassoc_of H₀.fac, ← reassoc_of H₁.fac, ← assoc],
      refine left_calculus_of_fractions.comp _ _ ht
        (left_calculus_of_fractions.comp _ _ H₀'.hs'
          (left_calculus_of_fractions.comp _ _ H₁.hs' hu)), }, },
  { dsimp,
    let sq := (left_calculus_of_fractions.ex z₁₂.s z₁₂.hs z₂₃.f).some,
    let sq' := (left_calculus_of_fractions.ex z₁₂'.s z₁₂'.hs z₂₃.f).some,
    rw [zigzag.comp_eq _ _ sq, zigzag.comp_eq _ _ sq'],
    apply quot.sound,
    rcases h₁₂ with ⟨Y, t, t', hst, hft, ht⟩,
    let H := (left_calculus_of_fractions.ex (z₁₂.s ≫ t) ht (z₂₃.f ≫ sq.s')).some,
    let H' := (left_calculus_of_fractions.ex (z₁₂'.s ≫ t') (by { rw ← hst, exact ht, })
      (z₂₃.f ≫ sq'.s')).some,
    let z : zigzag W X₁ X₃ := ⟨H.obj, z₁₂.f ≫ t ≫ H.g, z₂₃.s ≫ sq.s' ≫ H.s',
      left_calculus_of_fractions.comp _ _ z₂₃.hs
        (left_calculus_of_fractions.comp _ _ sq.hs' H.hs')⟩,
    let z' : zigzag W X₁ X₃ := ⟨H'.obj, z₁₂'.f ≫ t' ≫ H'.g, z₂₃.s ≫ sq'.s' ≫ H'.s',
      left_calculus_of_fractions.comp _ _ z₂₃.hs
        (left_calculus_of_fractions.comp _ _ sq'.hs' H'.hs')⟩,
    refine trans _ (trans (_ : zigzag_rel z z') (symm _)),
    { have eq : z₁₂.s ≫ sq.g ≫ H.s' = z₁₂.s ≫ t ≫ H.g,
      { have h := H.fac,
        simp only [assoc] at h,
        rw [← h, reassoc_of sq.fac], },
      rcases left_calculus_of_fractions.ext _ _ _ z₁₂.hs eq with ⟨Z, u, hu, fac⟩,
      simp only [assoc] at fac,
      refine ⟨Z, H.s' ≫ u, u, _,_, _⟩; dsimp [zigzag.comp₀],
      { simp only [assoc, comp_id], },
      { simp only [assoc, comp_id, fac], },
      { simp only [assoc],
        refine left_calculus_of_fractions.comp _ _ z₂₃.hs
          (left_calculus_of_fractions.comp _ _ sq.hs'
          (left_calculus_of_fractions.comp _ _ H.hs' hu)), }, },
    { let T := (left_calculus_of_fractions.ex (sq.s' ≫ H.s')
        (left_calculus_of_fractions.comp _ _ sq.hs' H.hs') (sq'.s' ≫ H'.s')).some,
      have Tfac := T.fac,
      have fac := H.fac,
      have fac' := H'.fac,
      simp only [assoc] at Tfac fac fac',
      have eq : z₁₂.s ≫ t ≫ H.g ≫ T.g = z₁₂.s ≫ t ≫ H'.g ≫ T.s',
      { simp only [reassoc_of hst, ← reassoc_of fac', Tfac, reassoc_of fac], },
      rcases left_calculus_of_fractions.ext _ _ _ z₁₂.hs eq with ⟨Z, u, hu, fac''⟩,
      simp only [assoc] at fac'',
      refine ⟨Z, T.g ≫ u, T.s' ≫ u, _, _, _⟩; dsimp [z, z'],
      { simp only [assoc, reassoc_of Tfac], },
      { rw [assoc, assoc, assoc, assoc, fac'', reassoc_of hft], },
      { simp only [assoc, ← reassoc_of Tfac],
        exact left_calculus_of_fractions.comp _ _ z₂₃.hs
          (left_calculus_of_fractions.comp _ _ sq'.hs'
          (left_calculus_of_fractions.comp _ _ H'.hs'
          (left_calculus_of_fractions.comp _ _ T.hs' hu))), }, },
    { have eq : z₁₂'.s ≫ sq'.g ≫ H'.s' = z₁₂'.s ≫ t' ≫ H'.g,
      { have h := H'.fac,
        simp only [assoc] at h,
        rw [← h, reassoc_of sq'.fac], },
      rcases left_calculus_of_fractions.ext _ _ _ z₁₂'.hs eq with ⟨Z, u, hu, fac⟩,
      simp only [assoc] at fac,
      refine ⟨Z, H'.s' ≫ u, u, _,_, _⟩; dsimp [zigzag.comp₀],
      { simp only [assoc, comp_id], },
      { simp only [assoc, comp_id, fac], },
      { simp only [assoc],
        refine left_calculus_of_fractions.comp _ _ z₂₃.hs
          (left_calculus_of_fractions.comp _ _ sq'.hs'
          (left_calculus_of_fractions.comp _ _ H'.hs' hu)), }, }, },
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

example : ℕ := 42

variable {W}

def zigzag.hom {X Y : localization W} (z : zigzag W X.obj Y.obj) : X ⟶ Y := quot.mk _ z

def map_zigzag {D : Type*} [category D] (F : C ⥤ D) (hF : W.is_inverted_by F)
  {X Y : C} (z : zigzag W X Y) : F.obj X ⟶ F.obj Y :=
F.map z.f ≫ by { haveI := hF z.s z.hs, exact inv (F.map z.s), }

namespace localization

lemma comp_eq {X₁ X₂ X₃ : localization W} (z₁₂ : zigzag W X₁.obj X₂.obj) (z₂₃ : zigzag W X₂.obj X₃.obj)
  (sq : to_sq z₁₂.s z₁₂.hs z₂₃.f) : z₁₂.hom ≫ z₂₃.hom = (zigzag.comp₀ z₁₂ z₂₃ sq).hom :=
hom.comp_eq z₁₂ z₂₃ sq

variable (W)

def hom_obj {X Y : C} (f : X ⟶ Y) :
  (⟨X⟩ : localization W).obj ⟶ (⟨Y⟩ : localization W).obj := f

@[simps]
def Q : C ⥤ localization W :=
{ obj := λ X, ⟨X⟩,
  map := λ X Y f, (zigzag.of_hom W (hom_obj W f)).hom,
  map_comp' := λ X₁ X₂ X₃ f g, begin
    dsimp,
    rw localization.comp_eq (zigzag.of_hom W (hom_obj W f)) (zigzag.of_hom W (hom_obj W g))
      ⟨X₃, g, 𝟙 X₃, left_calculus_of_fractions.id X₃, by tidy⟩,
    dsimp [zigzag.of_hom, zigzag.comp₀],
    congr' 1,
    tidy,
  end, }

variable {W}

@[simps]
def zigzag.inv {X Y : C} (s : X ⟶ Y) (hs : W s) :
  zigzag W (⟨Y⟩ : localization W).obj (⟨X⟩ : localization W).obj := ⟨Y, 𝟙 Y, s, hs⟩

def inv_Q_map {X Y : C} (s : X ⟶ Y) (hs : W s) : (Q W).obj Y ⟶ (Q W).obj X :=
zigzag.hom (zigzag.inv s hs)

lemma comp_inv_Q_map {X Y : C} (s : X ⟶ Y) (hs : W s) :
  (Q W).map s ≫ inv_Q_map s hs = 𝟙 _ :=
begin
  dsimp only [Q, inv_Q_map],
  rw localization.comp_eq (zigzag.of_hom W (hom_obj W s)) (zigzag.inv s hs)
    ⟨Y, 𝟙 Y, 𝟙 Y, left_calculus_of_fractions.id _, rfl⟩,
  dsimp [zigzag.comp₀],
  exact quot.sound ⟨Y, 𝟙 Y, s, by tidy, by tidy, by tidy⟩,
end

lemma inv_Q_map_comp {X Y : C} (s : X ⟶ Y) (hs : W s) :
   inv_Q_map s hs ≫ (Q W).map s = 𝟙 _ :=
begin
  dsimp [Q, inv_Q_map],
  rw localization.comp_eq (zigzag.inv s hs) (zigzag.of_hom W (hom_obj W s))
    ⟨Y, 𝟙 Y, 𝟙 Y, left_calculus_of_fractions.id _, rfl⟩,
  dsimp [zigzag.comp₀],
  exact quot.sound ⟨Y, 𝟙 Y, 𝟙 Y, by tidy, by tidy,
    by { dsimp, simp only [comp_id], exact left_calculus_of_fractions.id _, }⟩,
end

variable (W)

lemma Q_inverts_W : W.is_inverted_by (Q W) :=
λ X Y s hs, ⟨⟨inv_Q_map s hs, comp_inv_Q_map s hs, inv_Q_map_comp s hs⟩⟩

lemma inv_Q_map_eq {X Y : C} (s : X ⟶ Y) (hs : W s) :
  inv_Q_map s hs = (by { haveI := Q_inverts_W W s hs, exact inv ((Q W).map s), }) :=
begin
  haveI := Q_inverts_W W s hs,
  simp only [← cancel_mono ((Q W).map s), is_iso.inv_hom_id, inv_Q_map_comp],
end

instance {X Y : C} (s : X ⟶ Y) (hs : W s) : is_iso (inv_Q_map s hs) :=
by { rw inv_Q_map_eq, apply_instance, }

variables {W}

@[simp]
lemma id_eq (X : localization W) : 𝟙 X = quot.mk _ (zigzag.id W X.obj) := rfl

instance {X Y : C} (z : zigzag W X Y) : is_iso ((Q W).map z.s) :=
Q_inverts_W W z.s z.hs


lemma map_zigzag_eq {X Y : C} (z : zigzag W X Y) :
  map_zigzag (localization.Q W) (Q_inverts_W W) z = quot.mk _ z :=
begin
  dsimp only [map_zigzag],
  rw ← inv_Q_map_eq W z.s z.hs,
  dsimp only [Q, inv_Q_map],
  rw comp_eq (zigzag.of_hom W (hom_obj W z.f)) (zigzag.inv z.s z.hs)
    ⟨z.Z, 𝟙 _, 𝟙 _, left_calculus_of_fractions.id _, rfl⟩,
  dsimp [zigzag.of_hom, zigzag.comp₀, hom_obj, zigzag.hom],
  simp only [comp_id],
  cases z,
  refl,
end

variable (W)
lemma hom_fac {X Y : C} (f : (Q W).obj X ⟶ (Q W).obj Y) :
  ∃ (z : zigzag W X Y), f = map_zigzag (Q W) (Q_inverts_W W) z :=
begin
  cases surjective_quot_mk _ f with z hz,
  subst hz,
  exact ⟨z, (map_zigzag_eq z).symm⟩,
end

variable {W}

def lift {D : Type*} [category D] (F : C ⥤ D) (hF : W.is_inverted_by F) :
  localization W ⥤ D :=
{ obj := λ X, F.obj X.obj,
  map := λ X Y, quot.lift (λ (f : zigzag W X.obj Y.obj),
    by { haveI := hF f.s f.hs, exact F.map f.f ≫ inv (F.map f.s)})
    (λ z z' (h : zigzag_rel z z'), begin
      dsimp,
      rcases h with ⟨Y, t₁, t₂, hst, hft, ht⟩,
      haveI := hF _ ht,
      rw [← cancel_mono (F.map (z.s ≫ t₁)), assoc, assoc],
      nth_rewrite 0 F.map_comp,
      rw [is_iso.inv_hom_id_assoc, hst, F.map_comp, is_iso.inv_hom_id_assoc,
        ← F.map_comp z'.f, ← hft, F.map_comp],
    end),
  map_comp' := λ X₁ X₂ X₃ f₁ f₂, begin
    dsimp,
    cases surjective_quot_mk _ f₁ with g₁ h₁,
    cases surjective_quot_mk _ f₂ with g₂ h₂,
    substs h₁ h₂,
    let sq := (left_calculus_of_fractions.ex g₁.s g₁.hs g₂.f).some,
    erw comp_eq g₁ g₂ sq,
    dsimp [zigzag.comp₀, zigzag.hom],
    simp only [functor.map_comp, assoc],
    haveI := hF g₁.s g₁.hs,
    haveI := hF g₂.s g₂.hs,
    haveI := hF sq.s' sq.hs',
    rw is_iso.inv_comp,
    congr' 1,
    simp only [← cancel_mono (F.map g₂.s), ← cancel_mono (F.map sq.s'), ← cancel_epi (F.map g₁.s),
      assoc, is_iso.inv_hom_id, comp_id, is_iso.hom_inv_id_assoc, ← F.map_comp, sq.fac],
  end, }

example : ℕ := 42

lemma fac {D : Type*} [category D] (F : C ⥤ D) (hF : W.is_inverted_by F) :
  Q W ⋙ lift F hF = F :=
functor.ext (λ X, rfl) (λ X Y f, begin
  dsimp [lift, zigzag.hom, hom_obj],
  simp only [functor.map_id, is_iso.inv_id, id_comp],
end)

lemma uniq {D : Type*} [category D] (F₁ F₂ : localization W ⥤ D) (h : Q W ⋙ F₁ = Q W ⋙ F₂) :
  F₁ = F₂ :=
begin
  have eq : ∀ (X : localization W), F₁.obj X = F₂.obj X,
  { intro X,
    cases X,
    apply functor.congr_obj h X, },
  apply functor.ext eq,
  intros X Y f,
  cases X,
  cases Y,
  rcases hom_fac W f with ⟨φ, hφ⟩,
  subst f,
  have eq₁ := functor.congr_map_conjugate h φ.f,
  have eq₂ := functor.congr_map_conjugate h φ.s,
  dsimp only [functor.comp_map] at eq₁ eq₂,
  dsimp only [map_zigzag],
  simpa only [functor.map_comp, functor.map_inv, eq₁, eq₂, assoc, is_iso.inv_comp,
    inv_eq_to_hom, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp],
end

def universal_property (D : Type*) [category D]:
  localization.strict_universal_property_fixed_target (Q W) W D :=
{ inverts_W := Q_inverts_W W,
  lift := lift,
  fac := fac,
  uniq := uniq, }

instance Q_is_localization : (Q W).is_localization W :=
functor.is_localization.mk' (Q W) W (universal_property _) (universal_property _)

end localization

lemma map_zigzag_compatibility {D E : Type*} [category D] [category E]
  (L₁ : C ⥤ D) (hL₁ : W.is_inverted_by L₁) (L₂ : C ⥤ E) (hL₂ : W.is_inverted_by L₂)
  (M : D ⥤ E) (e : L₁ ⋙ M ≅ L₂) {X Y : C} (z : zigzag W X Y) :
  map_zigzag L₂ hL₂ z = e.inv.app X ≫ M.map (map_zigzag L₁ hL₁ z) ≫ e.hom.app Y :=
begin
  dsimp [map_zigzag],
  simp only [M.map_comp, assoc],
  erw ← e.inv.naturality_assoc,
  congr' 1,
  haveI := hL₂ z.s z.hs,
  simp only [← cancel_mono (L₂.map z.s), is_iso.inv_hom_id, functor.map_inv, assoc,
    ← cancel_epi (e.hom.app z.Z), comp_id, iso.hom_inv_id_app_assoc, is_iso.eq_inv_comp],
  apply e.hom.naturality,
end

lemma map_zigzag_compatibility_imp {D E : Type*} [category D] [category E]
  (L₁ : C ⥤ D) (hL₁ : W.is_inverted_by L₁) (L₂ : C ⥤ E) (hL₂ : W.is_inverted_by L₂)
  (M : D ⥤ E) (e : L₁ ⋙ M ≅ L₂) {X Y : C} (z z' : zigzag W X Y)
  (eq : map_zigzag L₁ hL₁ z = map_zigzag L₁ hL₁ z') :
  map_zigzag L₂ hL₂ z = map_zigzag L₂ hL₂ z' :=
by simp only [map_zigzag_compatibility L₁ hL₁ L₂ hL₂ M e, eq]

lemma L_map_fac {D : Type*} [category D] (L : C ⥤ D) (W : morphism_property C)
  [left_calculus_of_fractions W]
  [L.is_localization W] {X Y : C} (f : L.obj X ⟶ L.obj Y) :
  ∃ (z : zigzag W X Y), f = map_zigzag L (localization.inverts_W L W) z :=
begin
  let E := (localization.uniq_equivalence W (localization.Q W) L),
  let e : localization.Q W ⋙ E.functor ≅ L :=
    localization.comp_uniq_equivalence_functor_iso W (localization.Q W) L,
  let f' := e.hom.app X ≫ f ≫ e.inv.app Y,
  cases localization.hom_fac W (E.functor.preimage f') with z hz,
  change E.functor.preimage f' =
    map_zigzag (localization.Q W) (localization.inverts_W _ W) z at hz,
  replace hz := congr_arg E.functor.map hz,
  refine ⟨z, _⟩,
  simp only [map_zigzag_compatibility (localization.Q W) (localization.inverts_W _ W)
    L (localization.inverts_W _ W) E.functor e, ← hz, functor.image_preimage, assoc,
    iso.inv_hom_id_app, comp_id, iso.inv_hom_id_app_assoc],
end

lemma L_map_zigzag_eq_iff {D : Type*} [category D] (L : C ⥤ D) {W : morphism_property C}
  [left_calculus_of_fractions W] [L.is_localization W] {X Y : C} (z₁ z₂ : zigzag W X Y) :
  map_zigzag L (localization.inverts_W L W) z₁ =
    map_zigzag L (localization.inverts_W L W) z₂ ↔ zigzag_rel z₁ z₂ :=
begin
  have eq : map_zigzag L (localization.inverts_W _ W) z₁ =
      map_zigzag L (localization.inverts_W _ W) z₂ ↔
    map_zigzag (localization.Q W) (localization.inverts_W _ W) z₁ =
      map_zigzag (localization.Q W) (localization.inverts_W _ W) z₂,
  { split,
    all_goals { exact map_zigzag_compatibility_imp _ _ _ _ _
      (localization.comp_uniq_equivalence_functor_iso W _ _)  _ _, }, },
  simp only [eq, localization.map_zigzag_eq],
  split,
  { rw quot.eq,
    clear eq,
    intro h,
    induction h with s₁ s₂ h s s₁ s₂ h' h s₁ s₂ s₃ h'₁ h'₂ h₁ h₂,
    exacts [h, zigzag_rel.refl _, h.symm, h₁.trans h₂], },
  { exact quot.sound, },
end

end left_calculus_of_fractions

end category_theory
