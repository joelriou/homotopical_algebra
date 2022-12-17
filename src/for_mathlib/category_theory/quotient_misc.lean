import category_theory.quotient
import category_theory.limits.shapes.zero_morphisms
import category_theory.preadditive.additive_functor
import group_theory.subgroup.basic

namespace category_theory

open limits

namespace quotient

variables {C D : Type*} [category C] [category D] {r : hom_rel C}

lemma functor_map_surjective (X Y : C) :
  function.surjective (λ (f : X ⟶ Y), (functor r).map f) := surjective_quot_mk _

lemma nat_trans_ext {F G : quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G)
  (h : ∀ (X : C), τ₁.app ((functor r).obj X) = τ₂.app ((functor r).obj X)) : τ₁ = τ₂ :=
by { ext X, cases X, exact h X, }

def lift_nat_trans (F G : quotient r ⥤ D) (τ : functor _ ⋙ F ⟶ functor _ ⋙ G) :
  F ⟶ G :=
{ app := by { rintro ⟨X⟩, exact τ.app X, },
  naturality' := by { rintros ⟨X⟩ ⟨Y⟩ ⟨f⟩, exact τ.naturality f, }, }

@[simp]
lemma lift_nat_trans_app (F G : quotient r ⥤ D) (τ : functor _ ⋙ F ⟶ functor _ ⋙ G) (X : C) :
  (lift_nat_trans F G τ).app ((functor r).obj X) = τ.app X := rfl

@[simp]
lemma lift_nat_trans_id (F : quotient r ⥤ D) :
  lift_nat_trans F F (𝟙 _) = 𝟙 _ :=
nat_trans_ext _ _ (λ X, rfl)

@[simp, reassoc]
lemma lift_nat_trans_comp (F G H : quotient r ⥤ D) (τ : functor _ ⋙ F ⟶ functor _ ⋙ G)
  (τ' : functor _ ⋙ G ⟶ functor _ ⋙ H) :
  lift_nat_trans F G τ ≫ lift_nat_trans G H τ' = lift_nat_trans F H (τ ≫ τ') :=
nat_trans_ext _ _ (λ X, by simp)

@[simps]
def lift_nat_iso (F G : quotient r ⥤ D) (e : functor _ ⋙ F ≅ functor _ ⋙ G) :
  F ≅ G :=
{ hom := lift_nat_trans _ _ e.hom,
  inv := lift_nat_trans _ _ e.inv, }

variable (r)

def lift_nat_trans' {F G : C ⥤ D} (τ : F ⟶ G)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂)
  (hG : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), G.map f₁ = G.map f₂) :
  lift r F hF ⟶ lift r G hG :=
lift_nat_trans _ _
    ((quotient.lift.is_lift r F hF).hom ≫ τ ≫ (quotient.lift.is_lift r G hG).inv)

@[simp]
lemma lift_nat_trans'_app {F G : C ⥤ D} (τ : F ⟶ G)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂)
  (hG : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), G.map f₁ = G.map f₂) (X : C) :
  (lift_nat_trans' r τ hF hG).app ((functor r).obj X) = τ.app X :=
begin
  dsimp [lift_nat_trans'],
  simp,
end

@[simp]
lemma lift_nat_trans'_id (F : C ⥤ D)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂) :
  lift_nat_trans' r (𝟙 F) hF hF = 𝟙 _ :=
nat_trans_ext _ _ (λ X, by { dsimp, simp, })

@[simp]
lemma lift_nat_trans'_comp {F G H : C ⥤ D} (τ : F ⟶ G) (τ' : G ⟶ H)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂)
  (hG : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), G.map f₁ = G.map f₂)
  (hH : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), H.map f₁ = H.map f₂) :
  lift_nat_trans' r τ hF hG ≫ lift_nat_trans' r τ' hG hH =
    lift_nat_trans' r (τ ≫ τ') hF hH :=
nat_trans_ext _ _ (λ X, by simp)

@[simps]
def lift_nat_iso' {F G : C ⥤ D} (e : F ≅ G)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂)
  (hG : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), G.map f₁ = G.map f₂) :
  lift r F hF ≅ lift r G hG :=
{ hom := lift_nat_trans' r e.hom hF hG,
  inv := lift_nat_trans' r e.inv hG hF, }

lemma lift_map_eq (F : C ⥤ D)
  (hF : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y) (h : r f₁ f₂), F.map f₁ = F.map f₂)
  {X Y : C} (f : X ⟶ Y) :
  (lift r F hF).map ((functor r).map f) = F.map f :=
by rw [functor_map, lift_map]

open_locale zero_object

lemma is_zero_of_is_zero {X : C} (hX : is_zero X) :
  is_zero ((functor r).obj X) :=
begin
  haveI : has_zero_object C := ⟨⟨_, hX⟩⟩,
  refine limits.is_zero.of_iso _ ((functor r).map_iso (is_zero.iso_zero hX)),
  split,
  { rintro ⟨Y⟩,
    haveI := (has_zero_object.unique_from Y),
    refine ⟨⟨⟨(functor r).map default⟩, _⟩⟩,
    intro f,
    obtain ⟨g, rfl⟩ := functor_map_surjective _ _ f,
    rw subsingleton.elim g default, },
  { rintro ⟨Y⟩,
    haveI := (has_zero_object.unique_to Y),
    refine ⟨⟨⟨(functor r).map default⟩, _⟩⟩,
    intro f,
    obtain ⟨g, rfl⟩ := functor_map_surjective _ _ f,
    rw subsingleton.elim g default, },
end

instance [has_zero_object C] : has_zero_object (quotient r) :=
⟨⟨_, is_zero_of_is_zero _ (is_zero_zero C)⟩⟩

section preadditive

variables [preadditive C] [congruence r]
  (add : ∀ ⦃X Y : C⦄ ⦃f₁ g₁ f₂ g₂ : X ⟶ Y⦄ (h₁ : r f₁ g₁) (h₂ : r f₂ g₂), (r (f₁ + f₂) (g₁ + g₂)))
  (neg : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄ (h : r f g), r (-f) (-g))

lemma comp_closure_eq_self : comp_closure r = r :=
begin
  ext X Y f₁ f₂,
  split,
  { intro h,
    simpa only [← functor_map_eq_iff r] using quot.sound h, },
  { exact comp_closure.of _ _ _, },
end

variable {r}

include add

def preadditive.add {X Y : quotient r} (φ φ' : X ⟶ Y) : X ⟶ Y :=
begin
  refine quot.lift₂ (λ x y, quot.mk _ (x+y)) _ _ φ φ',
  { intros x y₁ y₂ h,
    rw comp_closure_eq_self at h,
    change (functor r).map (x+y₁) = (functor r).map (x+y₂),
    rw functor_map_eq_iff,
    exact add (refl _) h, },
  { intros x₁ x₂ y h,
    rw comp_closure_eq_self at h,
    change (functor r).map (x₁+y) = (functor r).map (x₂+y),
    rw functor_map_eq_iff,
    exact add h (refl _), },
end

omit add

include neg

def preadditive.neg {X Y : quotient r} (φ : X ⟶ Y) : X ⟶ Y :=
begin
  refine quot.lift (λ x, quot.mk _ (-x)) _ φ,
  intros x y h,
  rw comp_closure_eq_self at h,
  change (functor r).map (-x) = (functor r).map (-y),
  rw functor_map_eq_iff,
  exact neg h,
end

include add
variable (r)

def preadditive.hom_group (X Y : quotient r) : add_comm_group (X ⟶ Y) :=
{ add := preadditive.add add,
  add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact (functor r).congr_map (add_assoc x y z), },
  zero := (functor r).map 0,
  zero_add := by { rintro ⟨x⟩, exact (functor r).congr_map (zero_add x), },
  add_zero := by { rintro ⟨x⟩, exact (functor r).congr_map (add_zero x), },
  neg := preadditive.neg neg,
  add_left_neg := by { rintro ⟨x⟩, exact (functor r).congr_map (add_left_neg x), },
  add_comm := by { rintros ⟨x⟩ ⟨y⟩, exact (functor r).congr_map (add_comm x y), }, }

@[protected]
def preadditive :
  preadditive (quotient r) :=
{ hom_group := preadditive.hom_group r add neg,
  add_comp' := λ X Y Z, begin
    rintros ⟨x₁⟩ ⟨x₂⟩ ⟨y⟩,
    exact (functor r).congr_map (preadditive.add_comp _ _ _ x₁ x₂ y),
  end,
  comp_add' := λ X Y Z, begin
    rintros ⟨x⟩ ⟨y₁⟩ ⟨y₂⟩,
    exact (functor r).congr_map (preadditive.comp_add _ _ _ x y₁ y₂),
  end, }

lemma functor_additive :
  @functor.additive C (quotient r) _ _ _ (quotient.preadditive r add neg) (functor r) := { }

omit add neg

lemma lift_additive {D : Type*} [category D] [preadditive D] [preadditive (quotient r)]
  [(functor r).additive] (F : C ⥤ D) [F.additive]
  (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) :
  (lift r F H).additive :=
⟨begin
  rintro ⟨X⟩ ⟨Y⟩ ⟨f₁ : X ⟶ Y⟩ ⟨f₂ : X ⟶ Y⟩,
  change (lift r F H).map ((functor r).map f₁ + (functor r).map f₂) = F.map f₁ + F.map f₂,
  simpa only [← functor.map_add],
end⟩

end preadditive

end quotient

end category_theory
