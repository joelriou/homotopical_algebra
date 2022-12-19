import algebra.homology.short_complex.short_exact
import algebra.add_torsor

noncomputable theory

namespace category_theory

open limits category

variables (C : Type*) [category C]

@[derive category]
def short_exact_sequence [has_zero_morphisms C] :=
full_subcategory (λ (S : short_complex C), S.short_exact)

namespace short_exact_sequence

variable {C}

section

variables [has_zero_morphisms C] (S : short_exact_sequence C)

abbreviation short_complex : short_complex C := S.1

lemma short_exact : S.short_complex.short_exact := S.2

lemma exact : S.short_complex.exact := S.short_exact.exact

instance : mono S.short_complex.f := S.short_exact.mono_f
instance : epi S.short_complex.g := S.short_exact.epi_g

end

instance five_lemma [preadditive C] [balanced C]
  {S₁ S₂ : short_exact_sequence C} (φ : S₁ ⟶ S₂)
  [is_iso φ.τ₁] [is_iso φ.τ₃] : is_iso φ.τ₂ :=
begin
  rw is_iso_iff_mono_and_epi,
  refine ⟨_, _⟩,
  { rw preadditive.mono_iff_cancel_zero,
    intros A f hf,
    let f' := S₁.short_exact.lift f
      (by simp only [assoc, ← cancel_mono φ.τ₃, ← φ.comm₂₃, reassoc_of hf, zero_comp]),
    have hf' : f' ≫ _ = _ := S₁.short_exact.lift_f _ _,
    have hf'' : f' = 0,
    { simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.short_complex.f, assoc, φ.comm₁₂,
        reassoc_of hf', hf, zero_comp], },
    rw [← hf', hf'', zero_comp], },
  { rw preadditive.epi_iff_cancel_zero,
    intros A f hf,
    let f' := S₂.short_exact.desc f
      (by simp only [← cancel_epi φ.τ₁, φ.comm₁₂_assoc, hf, comp_zero]),
    have hf' : _ ≫ f' = _ := S₂.short_exact.g_desc _ _,
    have hf'' : f' = 0,
    { simp only [← cancel_epi φ.τ₃, ← cancel_epi S₁.short_complex.g, ← φ.comm₂₃_assoc,
        hf', hf, comp_zero], },
    rw [← hf', hf'', comp_zero], },
end

end short_exact_sequence

namespace abelian

variables {C} (A B : C)

structure extension [has_zero_morphisms C] :=
(X : C)
(i : B ⟶ X)
(p : X ⟶ A)
(w : i ≫ p = 0)
(ex : (short_complex.mk _ _ w).short_exact)

namespace extension

section

variables {A B} [has_zero_morphisms C]

instance (E : extension A B) : mono E.i := E.ex.mono_f
instance (E : extension A B) : epi E.p := E.ex.epi_g

@[ext]
structure hom (E₁ E₂ : extension A B) :=
(τ : E₁.X ⟶ E₂.X)
(commi : E₁.i ≫ τ = E₂.i)
(commp : τ ≫ E₂.p = E₁.p)

attribute [simp, reassoc] w hom.commi hom.commp

@[simps]
def hom.id (E : extension A B) : hom E E :=
{ τ := 𝟙 _,
  commi := by simp,
  commp := by simp, }

@[simps]
def hom.comp {E₁ E₂ E₃ : extension A B} (φ : hom E₁ E₂) (φ' : hom E₂ E₃) : hom E₁ E₃ :=
{ τ := φ.τ ≫ φ'.τ,
  commi := by simp,
  commp := by simp, }

instance : category (extension A B) :=
{ hom := hom,
  id := hom.id,
  comp := λ E₁ E₂ E₃, hom.comp, }

@[simp]
lemma comp_τ {E₁ E₂ E₃ : extension A B} (φ : E₁ ⟶ E₂) (φ' : E₂ ⟶ E₃) :
  (φ ≫ φ').τ = φ.τ ≫ φ'.τ := rfl

@[simp]
lemma id_τ (E : extension A B) :
  hom.τ (𝟙 E) = 𝟙 E.X := rfl

variables (A B)

@[simps]
def to_short_exact_sequence_functor : extension A B ⥤ short_exact_sequence C :=
{ obj := λ E, ⟨short_complex.mk E.i E.p E.w, E.ex⟩,
  map := λ E₁ E₂ φ,
  { τ₁ := 𝟙 _,
    τ₂ := φ.τ,
    τ₃ := 𝟙 _, },
  map_comp' := λ E₁ E₂ E₃ φ φ', begin
    ext,
    { dsimp, erw short_complex.comp_τ₁, dsimp, simp only [comp_id], },
    { refl, },
    { dsimp, erw short_complex.comp_τ₃, dsimp, simp only [comp_id], },
  end, }

instance : faithful (to_short_exact_sequence_functor A B) :=
⟨λ E₁ E₂ f₁ f₂ eq, begin
  ext,
  simpa only using congr_arg short_complex.hom.τ₂ eq,
end⟩

instance (E₁ E₂ : extension A B) (f : E₁ ⟶ E₂) :
  is_iso ((to_short_exact_sequence_functor A B).map f).τ₁ :=
by { dsimp, apply_instance, }

instance (E₁ E₂ : extension A B) (f : E₁ ⟶ E₂) :
  is_iso ((to_short_exact_sequence_functor A B).map f).τ₃ :=
by { dsimp, apply_instance, }

end

variable [abelian C]

variables {A B} {E₁ E₂ : extension A B}

instance (f : E₁ ⟶ E₂) : is_iso f :=
⟨begin
  haveI : is_iso f.τ := (infer_instance : is_iso ((to_short_exact_sequence_functor A B).map f).τ₂),
  refine ⟨⟨inv f.τ, _, _⟩, _, _⟩,
  tidy,
end⟩

@[simps]
instance has_vadd : has_vadd (A ⟶ B) (E₁ ⟶ E₂) :=
{ vadd := λ g f,
  { τ := E₁.p ≫ g ≫ E₂.i + f.τ,
    commi := by simp,
    commp := by simp, }, }

instance : add_action (A ⟶ B) (E₁ ⟶ E₂) :=
{ zero_vadd := by tidy,
  add_vadd := λ g₁ g₂ f, begin
    ext,
    simp only [has_vadd_vadd_τ, preadditive.add_comp, preadditive.comp_add, add_assoc],
  end, }

def hom.vsub (f₁ f₂ : E₁ ⟶ E₂) : A ⟶ B :=
begin
  let g₀ := E₂.ex.lift (f₁.τ - f₂.τ) (by simp),
  have hg₀ : g₀ ≫ E₂.i = _ := E₂.ex.lift_f _ _,
  exact E₁.ex.desc g₀ begin
    dsimp,
    simp only [← cancel_mono E₂.i, assoc, hg₀, preadditive.comp_sub,
    hom.commi, sub_self, zero_comp],
  end,
end

lemma hom.p_vsub_i (f₁ f₂ : E₁ ⟶ E₂) : E₁.p ≫ hom.vsub f₁ f₂ ≫ E₂.i = f₁.τ - f₂.τ :=
begin
  dsimp [hom.vsub],
  rw [← assoc, E₁.ex.g_desc, E₂.ex.lift_f],
end

instance has_vsub : has_vsub (A ⟶ B) (E₁ ⟶ E₂) :=
{ vsub := hom.vsub, }

@[simp, reassoc]
lemma p_has_vsub_vsub_i (f₁ f₂ : E₁ ⟶ E₂) :
  E₁.p ≫ (f₁ -ᵥ f₂) ≫ E₂.i = f₁.τ - f₂.τ :=
hom.p_vsub_i f₁ f₂

@[simp]
lemma vsub_vadd (f₁ f₂ : E₁ ⟶ E₂) :
  (f₁ -ᵥ f₂ : A ⟶ B) +ᵥ f₂ = f₁ :=
begin
  ext,
  simp only [has_vadd_vadd_τ, p_has_vsub_vsub_i, sub_add_cancel],
end

@[simp]
lemma vadd_vsub (g : A ⟶ B) (f : E₁ ⟶ E₂) :
  g +ᵥ f -ᵥ f = g :=
by rw [← cancel_mono E₂.i, ← cancel_epi E₁.p, p_has_vsub_vsub_i, has_vadd_vadd_τ, add_sub_cancel]

end extension

end abelian

end category_theory
