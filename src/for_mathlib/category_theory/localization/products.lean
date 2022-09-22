import for_mathlib.category_theory.localization.predicate
import category_theory.products.basic
import for_mathlib.category_theory.functor_misc

noncomputable theory

universes v v' u

namespace category_theory

variables {C₁ D₁ C₂ D₂ : Type*} [category C₁] [category C₂] [category D₁] [category D₂]
  (W₁ : morphism_property C₁) (W₂ : morphism_property C₂) {E : Type*} [category E]

@[simps]
def nat_iso.prod {F F' : C₁ ⥤ D₁} {G G' : C₂ ⥤ D₂} (α : F ≅ F') (β : G ≅ G') :
  F.prod G ≅ F'.prod G' :=
{ hom := α.hom.prod β.hom,
  inv := α.inv.prod β.inv, }

namespace equivalence

def prod (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) : C₁ × C₂ ≌ D₁ × D₂ :=
{ functor := E₁.functor.prod E₂.functor,
  inverse := E₁.inverse.prod E₂.inverse,
  unit_iso := ((functor_prod_functor_equiv (C₁ × C₂) C₁ C₂).counit_iso.app (𝟭 _)).symm
      ≪≫ nat_iso.prod E₁.unit_iso E₂.unit_iso,
  counit_iso := nat_iso.prod E₁.counit_iso E₂.counit_iso ≪≫
      ((functor_prod_functor_equiv (D₁ × D₂) D₁ D₂).counit_iso.app (𝟭 _)), }

end equivalence

namespace functor

@[simps]
def prod_functor : (C₁ ⥤ D₁) × (C₂ ⥤ D₂) ⥤ (C₁ × C₂) ⥤ (D₁ × D₂) :=
{ obj := λ F, F.1.prod F.2,
  map := λ F G φ, φ.1.prod φ.2, }

lemma flip_flip (H : D₁ ⥤ D₂ ⥤ E) : H.flip.flip = H :=
functor.ext (λ X₁, (functor.ext (λ X₂, rfl) (by tidy))) (by tidy)

lemma comp_comp_curry_flip_flip_eq_curry (H : D₁ × D₂ ⥤ E) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
  F₁ ⋙ (F₂ ⋙ (curry.obj H).flip).flip = curry.obj (F₁.prod F₂ ⋙ H) :=
functor.ext (λ X₁, (functor.ext (λ Y₁, rfl) (by tidy))) (by tidy)

lemma uncurry_curry (H : D₁ × D₂ ⥤ E) : uncurry.obj (curry.obj H) = H :=
functor.ext (λ X, by { cases X, refl, }) (by tidy)

end functor

namespace morphism_property

class contains_identities {C : Type*} [category C] (W : morphism_property C) : Prop :=
(id : ∀ (X : C), W (𝟙 X))

def prod : morphism_property (C₁ × C₂) := λ X Y f, W₁ f.fst ∧ W₂ f.snd

variables {W₁ W₂}

lemma is_inverted_by.prod {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} (h₁ : W₁.is_inverted_by F₁)
  (h₂ : W₂.is_inverted_by F₂) : (W₁.prod W₂).is_inverted_by (F₁.prod F₂) :=
λ X Y f hf, by { rw is_iso_prod_iff, exact ⟨h₁ f.1 hf.1,h₂ f.2 hf.2⟩, }

end morphism_property

namespace localization

variables [hW₁ : W₁.contains_identities] [hW₂ : W₂.contains_identities]

namespace strict_universal_property_fixed_target

variables  (F : C₁ × C₂ ⥤ E) (hF : (W₁.prod W₂).is_inverted_by F)

@[simps]
def prod.hom_mk {X₁ Y₁ : C₁} {X₂ Y₂ : C₂} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
  (⟨X₁, X₂⟩ : C₁ × C₂) ⟶ ⟨Y₁, Y₂⟩ := ⟨f₁, f₂⟩

namespace prod

include hF hW₂
def lift₁ : W₁.localization ⥤ C₂ ⥤ E :=
localization.construction.lift (curry.obj F) (λ X₁ Y₁ f₁ hf₁, begin
  haveI : Π (Z₂ : C₂), is_iso (((curry.obj F).map f₁).app Z₂),
  { intro Z₂,
    apply hF,
    exact ⟨hf₁, morphism_property.contains_identities.id _⟩, },
    apply nat_iso.is_iso_of_is_iso_app,
end)

lemma fac₁ : W₁.Q ⋙ (lift₁ W₁ W₂ F hF) = curry.obj F := localization.construction.fac _ _

lemma lift₁_obj_map (X₁ : C₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂) :
  ((lift₁ W₁ W₂ F hF).obj (W₁.Q.obj X₁)).map f₂ =
    F.map (prod.hom_mk (𝟙 X₁) f₂) := rfl

lemma lift₁_map_app {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) (X₂ : C₂) :
  ((lift₁ W₁ W₂ F hF).map (W₁.Q.map f₁)).app X₂ =
    F.map (prod.hom_mk f₁ (𝟙 X₂)) :=
by simpa only [functor.comp_map, eq_to_hom_refl, category.comp_id, category.id_comp,
  curry_obj_map_app] using congr_app (functor.congr_map_conjugate (fac₁ W₁ W₂ F hF) f₁) X₂

include hW₁

def lift₂ : W₂.localization ⥤ W₁.localization ⥤ E :=
localization.construction.lift (lift₁ W₁ W₂ F hF).flip (λ X₂ Y₂ f₂ hf₂, begin
  haveI : ∀ (X₁ : W₁.localization), is_iso (((lift₁ W₁ W₂ F hF).flip.map f₂).app X₁),
  { intro X₁,
    have hF₁ : ∃ (A₁ : C₁), W₁.Q.obj A₁ = X₁ := (construction.obj_equiv W₁).surjective X₁,
    cases hF₁ with A₁ hA₁,
    subst hA₁,
    simp only [functor.flip_map_app, lift₁_obj_map],
    haveI := hF (prod.hom_mk (𝟙 A₁) f₂) ⟨morphism_property.contains_identities.id _, hf₂⟩,
    apply_instance, },
  apply nat_iso.is_iso_of_is_iso_app,
end)

lemma fac₂ : W₂.Q ⋙ (lift₂ W₁ W₂ F hF) = (lift₁ W₁ W₂ F hF).flip :=
localization.construction.fac _ _

lemma lift₂_obj_map {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) (X₂ : C₂) :
  ((lift₂ W₁ W₂ F hF).obj (W₂.Q.obj X₂)).map (W₁.Q.map f₁) = F.map (prod.hom_mk f₁ (𝟙 X₂)) :=
by simpa only [eq_to_hom_refl, functor.flip_obj_map, category.comp_id,
  category.id_comp, lift₁_map_app] using functor.congr_map_conjugate
    (functor.congr_obj (fac₂ W₁ W₂ F hF) X₂) (W₁.Q.map f₁)

lemma lift₂_map_app (X₁ : C₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂) :
  ((lift₂ W₁ W₂ F hF).map (W₂.Q.map f₂)).app (W₁.Q.obj X₁) = F.map (prod.hom_mk (𝟙 X₁) f₂) :=
by simpa only [eq_to_hom_refl, category.comp_id, category.id_comp]
  using congr_app (functor.congr_map_conjugate (fac₂ W₁ W₂ F hF) f₂) (W₁.Q.obj X₁)

def lift₃ : W₁.localization × W₂.localization ⥤ E := uncurry.obj (lift₂ W₁ W₂ F hF).flip

lemma fac : W₁.Q.prod W₂.Q ⋙ prod.lift₃ W₁ W₂ F hF = F :=
begin
  refine functor.ext (λ X, by { cases X, refl, }) (λ X Y f, _),
  { rcases X with ⟨X₁, X₂⟩,
    rcases Y with ⟨Y₁, Y₂⟩,
    have eq : f = prod.hom_mk (𝟙 X₁) f.2 ≫ prod.hom_mk f.1 (𝟙 Y₂) :=
      by simp only [prod_comp, hom_mk_fst, category.id_comp, hom_mk_snd, category.comp_id,
        prod.mk.eta],
    nth_rewrite 0 eq,
    dsimp [functor.comp, lift₃],
    simp only [category.id_comp, category.comp_id, nat_trans.naturality,
      lift₂_obj_map, lift₂_map_app, ← F.map_comp],
    congr' 1,
    ext,
    { apply category.comp_id, },
    { apply category.id_comp, }, },
end

omit hF hW₁ hW₂

lemma uniq (H H' : W₁.localization × W₂.localization ⥤ E)
  (eq : W₁.Q.prod W₂.Q ⋙ H = W₁.Q.prod W₂.Q ⋙ H') : H = H' :=
begin
  let G := (curry.obj H).flip,
  let G' := (curry.obj H').flip,
  suffices : G = G',
  { rw [← functor.uncurry_curry H, ← functor.uncurry_curry H'],
    congr' 1,
    rw [← functor.flip_flip (curry.obj H), ← functor.flip_flip (curry.obj H')],
    congr', },
  apply construction.uniq,
  suffices : (W₂.Q ⋙ G).flip = (W₂.Q ⋙ G').flip,
  { rw [← functor.flip_flip (W₂.Q ⋙ G), ← functor.flip_flip (W₂.Q ⋙ G'), this], },
  apply construction.uniq,
  convert congr_arg curry.obj eq,
  all_goals { apply functor.comp_comp_curry_flip_flip_eq_curry, },
end

end prod

include hW₁ hW₂

variable (E)

def prod : strict_universal_property_fixed_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) E :=
{ inverts_W := (localization.inverts_W _ _).prod (localization.inverts_W _ _),
  lift := λ F hF, prod.lift₃ W₁ W₂ F hF,
  fac := λ F hF, prod.fac W₁ W₂ F hF,
  uniq := λ H H' eq, begin
    let G := (curry.obj H).flip,
    let G' := (curry.obj H').flip,
    suffices : G = G',
    { rw [← functor.uncurry_curry H, ← functor.uncurry_curry H'],
      congr' 1,
      rw [← functor.flip_flip (curry.obj H), ← functor.flip_flip (curry.obj H')],
      congr', },
    apply construction.uniq,
    suffices : (W₂.Q ⋙ G).flip = (W₂.Q ⋙ G').flip,
    { rw [← functor.flip_flip (W₂.Q ⋙ G), ← functor.flip_flip (W₂.Q ⋙ G'), this], },
    apply construction.uniq,
    convert congr_arg curry.obj eq,
    all_goals { apply functor.comp_comp_curry_flip_flip_eq_curry, },
  end, }

end strict_universal_property_fixed_target

include hW₁ hW₂

instance prod_construction_is_localization : (W₁.Q.prod W₂.Q).is_localization (W₁.prod W₂) :=
functor.is_localization.mk' _ _
  (strict_universal_property_fixed_target.prod W₁ W₂ _)
  (strict_universal_property_fixed_target.prod W₁ W₂ _)

lemma prod_is_localization (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.is_localization W₁] [L₂.is_localization W₂] :
  (L₁.prod L₂).is_localization (W₁.prod W₂) :=
begin
  let E₁ := equivalence_from_model L₁ W₁,
  let E₂ := equivalence_from_model L₂ W₂,
  let e₁ : W₁.Q ⋙ E₁.functor ≅ L₁ := Q_comp_equivalence_from_model_functor_iso _ _,
  let e₂ : W₂.Q ⋙ E₂.functor ≅ L₂ := Q_comp_equivalence_from_model_functor_iso _ _,
  exact functor.is_localization.of_equivalence (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    (E₁.prod E₂) (functor.prod_functor.map_iso (e₁.prod e₂)),
end

end localization

end category_theory
