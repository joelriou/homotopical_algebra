import for_mathlib.category_theory.localization.equivalence
import category_theory.products.basic
import for_mathlib.category_theory.functor_misc

noncomputable theory

universes v v' u u'

namespace category_theory

lemma morphism_property.of_arrow_eq {C : Type*} [category C] (W : morphism_property C)
  (f₁ f₂ : arrow C) (hf₂ : W f₂.hom) (eq : f₁ = f₂) : W f₁.hom := by { subst eq, exact hf₂, }

lemma morphism_property.of_arrow_mk_eq {C : Type*} [category C] (W : morphism_property C)
  {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (hf₂ : W f₂) (eq : arrow.mk f₁ = arrow.mk f₂) :
  W f₁ :=
W.of_arrow_eq (arrow.mk f₁) (arrow.mk f₂) hf₂ eq

lemma functor.congr_map_arrow_obj_arrow_mk {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (eq : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
  F₁.map_arrow.obj (arrow.mk f) = F₂.map_arrow.obj (arrow.mk f) := by subst eq

section

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
(id [] : ∀ (X : C), W (𝟙 X))

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
    exact ⟨hf₁, morphism_property.contains_identities.id _ _⟩, },
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
    haveI := hF (prod.hom_mk (𝟙 A₁) f₂) ⟨morphism_property.contains_identities.id _ _, hf₂⟩,
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
{ inverts := (localization.inverts _ _).prod (localization.inverts _ _),
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

section

variables {J : Type*} {C : J → Type*} {D : J → Type*}
  [Π j, category (C j)] [Π j, category (D j)]
  (W : Π j, morphism_property (C j))
  [hW : ∀ j, (W j).contains_identities]
  (L : Π j, C j ⥤ D j) [Π j, (L j).is_localization (W j)]

instance : category (Π j, C j) :=
{ hom := λ X Y, Π j, X j ⟶ Y j,
  id := λ X j, 𝟙 (X j),
  comp := λ X Y Z f g j, f j ≫ g j, }

@[simps]
def functor.pi_ (F : Π j, C j ⥤ D j) : (Π j, C j) ⥤ (Π j, D j) :=
{ obj := λ X j, (F j).obj (X j),
  map := λ X Y f j, (F j).map (f j), }

@[simps]
def functor.pi'_ (F : Π j, E ⥤ D j) : E ⥤ (Π j, D j) :=
{ obj := λ X j, (F j).obj X,
  map := λ X Y f j, (F j).map f, }

@[simps]
def nat_trans.pi_ {F G : Π j, C j ⥤ D j} (e : Π j, F j ⟶ G j) :
  functor.pi_ F ⟶ functor.pi_ G :=
{ app := λ X j, (e j).app (X j), }

@[simps]
def nat_iso.pi {F G : Π j, C j ⥤ D j} (e : Π j, F j ≅ G j) :
  functor.pi_ F ≅ functor.pi_ G :=
{ hom := nat_trans.pi_ (λ j, (e j).hom),
  inv := nat_trans.pi_ (λ j, (e j).inv), }

@[simps]
def nat_trans.pi'_ {F G : Π j, E ⥤ D j} (e : Π j, F j ⟶ G j) :
  functor.pi'_ F ⟶ functor.pi'_ G :=
{ app := λ X j, (e j).app X, }

@[simps]
def nat_iso.pi'_ {F G : Π j, E ⥤ D j} (e : Π j, F j ≅ G j) :
  functor.pi'_ F ≅ functor.pi'_ G :=
{ hom := nat_trans.pi'_ (λ j, (e j).hom),
  inv := nat_trans.pi'_ (λ j, (e j).inv), }

@[simps]
def equivalence.pi (e : Π j, C j ≌ D j) : (Π j, C j) ≌ (Π j, D j) :=
{ functor := functor.pi_ (λ j, (e j).functor),
  inverse := functor.pi_ (λ j, (e j).inverse),
  unit_iso := nat_iso.pi (λ j, (e j).unit_iso),
  counit_iso := nat_iso.pi (λ j, (e j).counit_iso), }

variable (C)

@[simps]
def functor.pi_.eval (j : J) : (Π j, C j) ⥤ C j :=
{ obj := λ X, X j,
  map := λ X Y f, f j, }

variable {C}

@[simp]
lemma functor.pi_eval (F : Π j, C j ⥤ D j) (j : J) :
  functor.pi_ F ⋙ functor.pi_.eval _ j = functor.pi_.eval _ j ⋙ F j := rfl

@[simp]
def functor.pi'__eval (F : Π j, E ⥤ D j) (j : J) :
  functor.pi'_ F ⋙ functor.pi_.eval _ j = F j :=
functor.ext (λ X, rfl) (by tidy)

lemma functor.pi_.ext {F₁ F₂ : E ⥤ (Π j, C j)}
  (h : ∀ (j : J), F₁ ⋙ functor.pi_.eval _ j = F₂ ⋙ functor.pi_.eval _ j) : F₁ = F₂ :=
begin
  refine functor.ext (λ X, _) (λ X Y f, _),
  { ext j,
    exact functor.congr_obj (h j) X, },
  { ext j,
    simpa only [pi.comp_apply, functor.eq_to_hom_proj]
      using functor.congr_map_conjugate (h j) f, },
end

def pi.equivalence_of_eq {j j' : J} (eq : j = j') : C j ≌ C j' := by subst eq

@[simps]
def equivalence.pi' {J' : Type*} (α : J ≃ J') {D : J' → Type*}
  [Π j', category (D j')] (e : Π j, C j ≌ D (α j)) :
  (Π j, C j) ≌ (Π j', D j') :=
begin
  let e' : Π j', C (α.symm j') ≌ D j' := λ j', (e (α.symm j')).trans (pi.equivalence_of_eq (by simp)),
  exact
  { functor := functor.pi'_ (λ j', functor.pi_.eval _ _ ⋙ (e' j').functor),
    inverse := functor.pi'_ (λ j, functor.pi_.eval _ _ ⋙ (e j).inverse),
    unit_iso := eq_to_iso (functor.pi_.ext (λ c, begin
      rw [functor.assoc, functor.pi'__eval, ← functor.assoc, functor.pi'__eval],
      sorry,
    end)),
    counit_iso := eq_to_iso sorry, },
end

lemma equivalence.pi'_inverse_comp_eval {J' : Type*} (α : J ≃ J') {D : J' → Type*}
  [Π j', category (D j')] (e : Π j, C j ≌ D (α j)) (j : J) :
  (equivalence.pi' α e).inverse ⋙ functor.pi_.eval _ j =
    functor.pi_.eval _ (α j) ⋙ (e j).inverse := rfl

lemma equivalence.pi'_functor_comp_eval {J' : Type*} (α : J ≃ J') {D : J' → Type*}
  [Π j', category (D j')] (e : Π j, C j ≌ D (α j)) (j : J) :
  (equivalence.pi' α e).functor ⋙ functor.pi_.eval _ (α j) =
    functor.pi_.eval _ j ⋙ (e j).functor :=
begin
  dsimp only [equivalence.pi', equivalence.trans],
  rw functor.pi'__eval,
  suffices : ∀ (j₂ : J) (eq : j₂ = j),
    functor.pi_.eval C j₂ ⋙ (e j₂).functor ⋙ (pi.equivalence_of_eq (by rw eq)).functor =
    functor.pi_.eval C j ⋙ (e j).functor,
  { exact this _ (by simp), },
  intros j₂ eq,
  subst eq,
  refl,
end

lemma is_iso_pi_iff {X Y : Π j, C j} (f : X ⟶ Y) :
  is_iso f ↔ ∀ j, is_iso (f j) :=
begin
  split,
  { introI,
    intro j,
    change is_iso ((functor.pi_.eval C j).map f),
    apply_instance, },
  { introI,
    exact ⟨⟨λ j, inv (f j), by tidy⟩⟩, },
end

def morphism_property.pi : morphism_property (Π j, C j) := λ X Y f, ∀ j, (W j) (f j)

end

end

section

variables {J₁ J₂ : Type*} (C₁ : J₁ → Type u) (C₂ : J₂ → Type u)

@[simp]
def sum.desc : sum J₁ J₂ →  Type u
|(sum.inl j₁) := C₁ j₁
|(sum.inr j₂) := C₂ j₂

variables [Π j₁, category.{v} (C₁ j₁)] [Π j₂, category.{v} (C₂ j₂)]

instance : Π j, category.{v} (sum.desc C₁ C₂ j) :=
λ j, by { cases j; dsimp only [sum.desc]; apply_instance, }

def equivalence_pi_prod :
  (Π j₁, C₁ j₁) × (Π j₂, C₂ j₂) ≌ (Π j, sum.desc C₁ C₂ j) :=
{ functor := functor.pi'_ (λ j, match j with
    | sum.inl j₁ := category_theory.prod.fst _ _ ⋙ functor.pi_.eval _ j₁
    | sum.inr j₂ := category_theory.prod.snd _ _ ⋙ functor.pi_.eval _ j₂
  end),
  inverse := functor.prod'
    (functor.pi'_ (λ j₁, functor.pi_.eval _ (sum.inl j₁)))
    (functor.pi'_ (λ j₂, functor.pi_.eval _ (sum.inr j₂))),
  unit_iso := eq_to_iso (functor.ext (by tidy) (by tidy)),
  counit_iso := eq_to_iso (functor.ext (by tidy) (by tidy)), }

end

section

variables {J : Type*} (j : J) [subsingleton J] (C : J → Type*) [Π t, category (C t)]

def equivalence_pi_single :
  (Π t, C t) ≌ C j :=
{ functor := functor.pi_.eval _ j,
  inverse := functor.pi'_ (λ t, begin
    have eq := subsingleton.elim j t,
    subst eq,
    exact 𝟭 _,
  end),
  unit_iso := eq_to_iso begin
    refine functor.ext _ _,
    { intro X,
      ext t,
      have eq := subsingleton.elim j t,
      subst eq,
      refl, },
    { intros X Y f,
      ext t,
      have eq := subsingleton.elim j t,
      subst eq,
      simp, },
  end,
  counit_iso := eq_to_iso rfl, }

end

section

variables {J : Type*} {C : J → Type*} {D : J → Type*}
  [Π j, category (C j)] [Π j, category (D j)]
  (W : Π j, morphism_property (C j))
  (L : Π j, C j ⥤ D j)

lemma morphism_property.is_inverted_by.pi (h : ∀ j, (W j).is_inverted_by (L j)):
  (morphism_property.pi W).is_inverted_by (functor.pi_ (λ j, L j)) :=
λ X Y f hf, by { rw is_iso_pi_iff, exact λ j, h _ _ (hf j), }

instance [Π j, (W j).contains_identities] :
  morphism_property.contains_identities (morphism_property.pi W) :=
⟨λ X j, morphism_property.contains_identities.id (W j) (X j)⟩

end

namespace localization

variables (J : Type*) [finite J] {C : J → Type*} {D : J → Type*}
  [Π j, category (C j)] [Π j, category (D j)]
  (W : Π j, morphism_property (C j))
  [hW : ∀ j, (W j).contains_identities]
  (L : Π j, C j ⥤ D j) [Π j, (L j).is_localization (W j)]

def pi_is_localization : ((functor.pi_ L).is_localization (morphism_property.pi W)) :=
begin
  apply nonempty.some,
  unfreezingI { revert C D, },
  refine finite.induction_empty_option _ _ _ J,
  { intros J₁ J₂ e h₁ C₂ D₂, introI, introI, intros W₂ L₂, introI,
    let C₁ := λ j₁, C₂ (e j₁),
    let D₁ := λ j₁, D₂ (e j₁),
    let L₁ : Π j₁, C₁ j₁ ⥤ D₁ j₁ := λ j₁, L₂ (e j₁),
    let W₁ : Π j₁, morphism_property (C₁ j₁) := λ j₁, W₂ (e j₁),
    haveI := (h₁ W₁ L₁).some,
    let E : (Π j₁, C₁ j₁) ≌ (Π j₂, C₂ j₂) := equivalence.pi' e (λ j₁, by refl),
    let E' : (Π j₁, D₁ j₁) ≌ (Π j₂, D₂ j₂) := equivalence.pi' e (λ j₁, by refl),
    let Sq : Comm_sq E.symm.functor (functor.pi_ L₂) (functor.pi_ L₁) E'.symm.functor :=
      ⟨eq_to_iso (functor.pi_.ext (λ j₁, begin
        simp only [functor.assoc, functor.pi_eval],
        erw equivalence.pi'_inverse_comp_eval,
        simp only [← functor.assoc],
        erw equivalence.pi'_inverse_comp_eval,
        refl,
    end))⟩,
    have hW₁ : morphism_property.pi W₁ ⊆ (morphism_property.pi W₂).inverse_image' E.symm.inverse,
    { intros X₁ Y₁ f hf,
      refine ⟨X₁, Y₁, iso.refl _, iso.refl _, f, λ j₂, _, by tidy⟩,
      rcases e.surjective j₂ with ⟨j₁, hj₁⟩,
      subst hj₁,
      refine (W₂ (e j₁)).of_arrow_mk_eq _ _ (hf j₁) _,
      exact functor.congr_map_arrow_obj_arrow_mk (equivalence.pi'_functor_comp_eval e _ _) f, },
    exact nonempty.intro (functor.is_localization.of_equivalence'' E.symm E'.symm Sq
      (morphism_property.pi W₂) (morphism_property.pi W₁)
      (morphism_property.is_inverted_by.pi W₂ L₂ (λ j₂, localization.inverts _ _)) hW₁), },
  { intros C D, introI, introI, intros W L, introI,
    sorry, },
  { sorry, },
end

end localization

end category_theory
