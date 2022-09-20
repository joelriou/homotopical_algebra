import for_mathlib.category_theory.localization.predicate
import category_theory.products.basic
import for_mathlib.category_theory.functor_misc

noncomputable theory

universes v v' u

namespace category_theory

variables {C₁ D₁ C₂ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
(W₁ : morphism_property C₁) (W₂ : morphism_property C₂)

namespace morphism_property

class contains_identities {C : Type*} [category C] (W : morphism_property C) : Prop :=
(id : ∀ (X : C), W (𝟙 X))

def prod : morphism_property (C₁ × C₂) :=
λ X Y f, W₁ f.fst ∧ W₂ f.snd

variables {W₁ W₂}

lemma is_inverted_by.prod {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} (h₁ : W₁.is_inverted_by F₁)
  (h₂ : W₂.is_inverted_by F₂) : (W₁.prod W₂).is_inverted_by (F₁.prod F₂) :=
λ X Y f hf, by { rw is_iso_prod_iff, exact ⟨h₁ f.1 hf.1,h₂ f.2 hf.2⟩, }

end morphism_property

namespace localization

namespace strict_universal_property_fixed_target

section

variables {E : Type*} [category E] (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  [hW₁ : W₁.contains_identities] [hW₂ : W₂.contains_identities]
  (h₁ : strict_universal_property_fixed_target F₁ W₁ (C₂ ⥤ E))
  (h₂ : strict_universal_property_fixed_target F₂ W₂ (D₁ ⥤ E))
  (F : C₁ × C₂ ⥤ E) (hF : (W₁.prod W₂).is_inverted_by F)

def prod.hom_mk {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
  (⟨X₁, X₂⟩ : C₁ × C₂) ⟶ ⟨Y₁, Y₂⟩ := ⟨f₁, f₂⟩

namespace prod

include hF hW₂
def lift₁ : D₁ ⥤ C₂ ⥤ E := h₁.lift (curry.obj F) (λ X₁ Y₁ f₁ hf₁, begin
  haveI : Π (Z₂ : C₂), is_iso (((curry.obj F).map f₁).app Z₂),
  { intro Z₂,
    apply hF,
    exact ⟨hf₁, morphism_property.contains_identities.id _⟩, },
    apply nat_iso.is_iso_of_is_iso_app,
end)

def fac₁ : F₁ ⋙ (lift₁ W₁ W₂ F₁ h₁ F hF) = curry.obj F := h₁.fac _ _

def lift₁_obj_obj (X₁ : C₁) (X₂ : C₂) :
  ((lift₁ W₁ W₂ F₁ h₁ F hF).obj (F₁.obj X₁)).obj X₂ = F.obj ⟨X₁, X₂⟩ :=
functor.congr_obj (functor.congr_obj (fac₁ W₁ W₂ F₁ h₁ F hF) X₁) X₂

@[simp]
def lift₁_obj_map (X₁ : C₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂) :
  ((lift₁ W₁ W₂ F₁ h₁ F hF).obj (F₁.obj X₁)).map f₂ =
    eq_to_hom (by rw lift₁_obj_obj) ≫ F.map (prod.hom_mk (𝟙 X₁) f₂) ≫ eq_to_hom (by rw lift₁_obj_obj) :=
functor.congr_map_conjugate (functor.congr_obj (fac₁ W₁ W₂ F₁ h₁ F hF) X₁) f₂

def lift₁_map₁ {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) (X₂ : C₂) :
  ((lift₁ W₁ W₂ F₁ h₁ F hF).map (F₁.map f₁)).app X₂ =
    eq_to_hom (by rw lift₁_obj_obj) ≫ F.map (prod.hom_mk f₁ (𝟙 X₂)) ≫ eq_to_hom (by rw lift₁_obj_obj) :=
by simpa only [nat_trans.comp_app, eq_to_hom_app]
  using congr_app (functor.congr_map_conjugate (fac₁ W₁ W₂ F₁ h₁ F hF) f₁) X₂

include hW₁

def lift₂ : D₂ ⥤ D₁ ⥤ E := h₂.lift (lift₁ W₁ W₂ F₁ h₁ F hF).flip (λ X₂ Y₂ f₂ hf₂, begin
  haveI : ∀ (X₁ : D₁), is_iso (((lift₁ W₁ W₂ F₁ h₁ F hF).flip.map f₂).app X₁),
  { intro X₁,
    have hF₁ : ∃ (A₁ : C₁), X₁ = F₁.obj A₁ := sorry,
    cases hF₁ with A₁ hA₁,
    subst hA₁,
    simp only [functor.flip_map_app, lift₁_obj_map],
    haveI := hF (prod.hom_mk (𝟙 A₁) f₂) ⟨morphism_property.contains_identities.id _, hf₂⟩,
    apply_instance, },
  apply nat_iso.is_iso_of_is_iso_app,
end)

def lift₃ : D₁ × D₂ ⥤ E := uncurry.obj (lift₂ W₁ W₂ F₁ F₂ h₁ h₂ F hF).flip

lemma uniq₁ (G G' : D₂ ⥤ D₁ ⥤ E) (eq : F₂ ⋙ G = F₂ ⋙ G') : G = G' := h₂.uniq _ _ eq

omit hF hW₁ hW₂

lemma flip_flip (H : D₁ ⥤ D₂ ⥤ E) : H.flip.flip = H :=
functor.ext (λ X₁, (functor.ext (λ X₂, rfl) (by tidy))) (by tidy)

lemma comp_comp_curry_flip_flip_eq_curry (H : D₁ × D₂ ⥤ E) :
  F₁ ⋙ (F₂ ⋙ (curry.obj H).flip).flip = curry.obj (F₁.prod F₂ ⋙ H) :=
functor.ext (λ X₁, (functor.ext (λ Y₁, rfl) (by tidy))) (by tidy)

lemma uncurry_curry (H : D₁ × D₂ ⥤ E) : uncurry.obj (curry.obj H) = H :=
functor.ext (λ X, by { cases X, refl, }) (by tidy)

end prod

include hW₁ hW₂

def prod : strict_universal_property_fixed_target (F₁.prod F₂) (W₁.prod W₂) E :=
{ inverts_W := h₁.inverts_W.prod h₂.inverts_W,
  lift := λ F hF, prod.lift₃ W₁ W₂ F₁ F₂ h₁ h₂ F hF,
  fac := sorry,
  uniq := λ H H' eq, begin
    let G := (curry.obj H).flip,
    let G' := (curry.obj H').flip,
    suffices : G = G',
    { rw [← prod.uncurry_curry H, ← prod.uncurry_curry H'],
      congr' 1,
      rw [← prod.flip_flip (curry.obj H), ← prod.flip_flip (curry.obj H')],
      congr', },
    apply h₂.uniq,
    suffices : (F₂ ⋙ G).flip = (F₂ ⋙ G').flip,
    { rw [← prod.flip_flip (F₂ ⋙ G), ← prod.flip_flip (F₂ ⋙ G'), this], },
    apply h₁.uniq,
    convert congr_arg curry.obj eq,
    all_goals { apply prod.comp_comp_curry_flip_flip_eq_curry, },
  end, }

end

end strict_universal_property_fixed_target

end localization

lemma prod_is_localization (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.is_localization W₁] [L₂.is_localization W₂] :
  (L₁.prod L₂).is_localization (W₁.prod W₂) := sorry

end category_theory
