import category_theory.quotient

namespace category_theory

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

end quotient

end category_theory
