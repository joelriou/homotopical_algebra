import category_theory.limits.shapes.finite_products
import category_theory.preadditive.additive_functor
import category_theory.limits.preserves.shapes.binary_products

noncomputable theory

namespace category_theory

open limits category

variables (C : Type*) [category C] [has_finite_products C]

structure add_comm_group_object :=
(X : C)
(zero : ⊤_ C ⟶ X)
(add : prod X X ⟶ X)
(neg : X ⟶ X)
(add_assoc' : prod.lift (limits.prod.map (𝟙 X) limits.prod.fst ≫ add) (limits.prod.snd ≫ limits.prod.snd) ≫ add =
  (limits.prod.map (𝟙 X) add) ≫ add)
(add_zero' : (prod.lift (terminal.from X ≫ zero) (𝟙 X)) ≫ add = 𝟙 X)
(comm' : prod.lift limits.prod.snd limits.prod.fst ≫ add = add)
(add_left_neg' : prod.lift neg (𝟙 X) ≫ add = terminal.from X ≫ zero)

instance (A : C) (G : add_comm_group_object C) : add_comm_group (A ⟶ G.X) :=
begin
  let zero : A ⟶ G.X := terminal.from A ≫ G.zero,
  let add := λ (g₁ g₂ : A ⟶ G.X), prod.lift g₁ g₂ ≫ G.add,
  have zero_add : ∀ (g : A ⟶ G.X), add zero g = g,
  { intro g,
    dsimp [add, zero],
    have h := g ≫= G.add_zero',
    simp only [← assoc, comp_id] at h,
    convert h,
    ext,
    { simp only [prod.comp_lift, prod.lift_fst, ← assoc],
      congr' 1, },
    { tidy, }, },
  have comm : ∀ (g₁ g₂ : A ⟶ G.X), add g₁ g₂ = add g₂ g₁,
  { intros g₁ g₂,
    dsimp [add],
    have h := prod.lift g₁ g₂ ≫= G.comm',
    simp only [← assoc] at h,
    convert h.symm,
    tidy, },
  exact
  { add := add,
    add_assoc := λ g₁ g₂ g₃, begin
      dsimp,
      have h := prod.lift g₁ (prod.lift g₂ g₃) ≫= G.add_assoc',
      simp only [← assoc] at h,
      convert h,
      tidy,
    end,
    add_comm := comm,
    zero := zero,
    neg := λ g, g ≫ G.neg,
    zero_add := zero_add,
    add_zero := λ g, begin
      change add g zero = g,
      rw [comm, zero_add],
    end,
    add_left_neg := λ g, begin
      change prod.lift (g ≫ G.neg) g ≫ G.add = terminal.from A ≫ G.zero,
      have h := g ≫= G.add_left_neg',
      simp only [← assoc] at h,
      convert h,
      tidy,
    end, },
end

namespace add_comm_group_object

lemma add_eq {A : C} {G : add_comm_group_object C} (g₁ g₂ : A ⟶ G.X) :
  g₁ + g₂ = prod.lift g₁ g₂ ≫ G.add := rfl

lemma comp_add {A A': C} (f : A ⟶ A') {G : add_comm_group_object C}
  (g₁ g₂ : A' ⟶ G.X) : f ≫ (g₁ + g₂) = f ≫ g₁ + f ≫ g₂ :=
by simp only [add_eq, prod.comp_lift_assoc]

variable {C}

def hom (G₁ G₂ : add_comm_group_object C) :=
{ f : G₁.X ⟶ G₂.X // G₁.add ≫ f = limits.prod.map f f ≫ G₂.add }

@[simps]
def hom.id (G : add_comm_group_object C) : hom G G :=
⟨𝟙 G.X, by tidy⟩

@[simps]
def hom.comp {G₁ G₂ G₃ : add_comm_group_object C} (f : hom G₁ G₂) (g : hom G₂ G₃) :
  hom G₁ G₃ :=
⟨ f.1 ≫ g.1, begin
  slice_lhs 1 2 { rw f.2,},
  rw [assoc, g.2, prod.map_map_assoc],
end⟩

instance : category (add_comm_group_object C) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z, hom.comp, }

@[ext]
lemma hom_ext {G₁ G₂ : add_comm_group_object C} (f g : G₁ ⟶ G₂) (h : f.1 = g.1) : f = g := by tidy

variable (C)

@[simps]
def forget : add_comm_group_object C ⥤ C :=
{ obj := λ G, G.X,
  map := λ G₁ G₂ f, f.1, }

variables {C} (F : C ⥤ add_comm_group_object C) (e : F ⋙ forget C ≅ 𝟭 C)

lemma add_comp {A : C} {G G' : add_comm_group_object C} (f₁ f₂ : A ⟶ G.X) (g : G ⟶ G') :
  (f₁ + f₂) ≫ g.1 = f₁ ≫ g.1 + f₂ ≫ g.1 :=
by simp only [add_eq, assoc, g.2, prod.lift_map_assoc]

namespace preadditive_of

include e

def hom_group (X Y : C) : add_comm_group (X ⟶ Y) :=
begin
  let add : (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y) :=
    λ f₁ f₂, ((f₁ ≫ e.inv.app Y : X ⟶ (F.obj Y).X) + (f₂ ≫ e.inv.app Y : X ⟶ (F.obj Y).X)) ≫ e.hom.app Y,
  have add_comm : ∀ (f₁ f₂), add f₁ f₂ = add f₂ f₁ := λ f₁ f₂, begin
    dsimp [add],
    rw add_comm,
  end,
  let neg : (X ⟶ Y) → (X ⟶ Y) :=
    λ f, (-(f ≫ e.inv.app Y : X ⟶ (F.obj Y).X)) ≫ e.hom.app Y,
  exact
  { add := add,
    add_comm := add_comm,
    add_assoc := λ f₁ f₂ f₃, begin
      change add (add _ _ ) _ = add _ (add _ _ ),
      dsimp [add],
      simp only [assoc, iso.hom_inv_id_app],
      dsimp,
      rw [comp_id, comp_id, add_assoc],
    end,
    zero := (0 : X ⟶ (F.obj Y).X) ≫ e.hom.app Y,
    zero_add := λ f, begin
      change add _ _ = _,
      dsimp [add],
      simp only [assoc, iso.hom_inv_id_app],
      dsimp,
      rw [comp_id, zero_add, assoc, iso.inv_hom_id_app],
      dsimp,
      rw comp_id,
    end,
    add_zero := λ f, begin
      change add _ _ = _,
      dsimp [add],
      simp only [assoc, iso.hom_inv_id_app],
      dsimp,
      rw [comp_id, add_zero, assoc, iso.inv_hom_id_app],
      dsimp,
      rw comp_id,
    end,
    neg := neg,
    add_left_neg := λ f, begin
      change add (neg f) f = _,
      dsimp [add, neg],
      simp only [assoc, iso.hom_inv_id_app],
      dsimp,
      simpa only [comp_id, add_left_neg],
    end, },
end

lemma add_comp_inv_app {X Y : C} (f₁ f₂ : X ⟶ Y) :
  (hom_group F e X Y).add f₁ f₂ ≫ e.inv.app Y =
    (f₁ ≫ e.inv.app Y + f₂ ≫ e.inv.app Y : X ⟶ (F.obj Y).X) :=
begin
  rw [← cancel_mono (e.hom.app Y), assoc, iso.inv_hom_id_app],
  dsimp,
  simpa only [comp_id],
end

end preadditive_of

def preadditive_of : preadditive C :=
{ hom_group := λ X Y, preadditive_of.hom_group F e X Y,
  comp_add' := λ X₁ X₂ X₃ f g₁ g₂, begin
    change f ≫ (preadditive_of.hom_group F e _ _).add _ _ =
      (preadditive_of.hom_group F e _ _).add _ _,
    rw ← cancel_mono (e.inv.app X₃),
    dsimp,
    simp only [preadditive_of.add_comp_inv_app, comp_add, assoc],
  end,
  add_comp' := λ X₁ X₂ X₃ f₁ f₂ g, begin
    change (preadditive_of.hom_group F e _ _).add _ _ ≫ g =
      (preadditive_of.hom_group F e _ _).add _ _,
    rw ← cancel_mono (e.inv.app X₃),
    dsimp,
    have hg := e.inv.naturality g,
    simp only [functor.id_map, functor.comp_map, forget_map] at hg,
    simp only [preadditive_of.add_comp_inv_app, assoc, hg,
      reassoc_of (preadditive_of.add_comp_inv_app F e f₁ f₂)],
    simp only [← assoc],
    apply add_comp,
  end, }

end add_comm_group_object

namespace preadditive

@[simps]
def to_add_comm_group_object [preadditive C] : C ⥤ add_comm_group_object C :=
{ obj := λ X,
  { X := X,
    zero := 0,
    add := limits.prod.fst + limits.prod.snd,
    neg := -𝟙 X,
    add_assoc' := begin
      simp only [comp_add, limits.prod.map_fst, comp_id, limits.prod.map_snd, prod.lift_fst, prod.lift_snd],
      apply add_assoc,
    end,
    add_zero' := by tidy,
    comm' := by simpa only [comp_add, prod.lift_fst, prod.lift_snd] using add_comm _ _,
    add_left_neg' := by simp, },
  map := λ X Y f, ⟨f, by simp⟩, }

@[simps]
def to_add_comm_group_object_comp_forget_iso [preadditive C] :
  (to_add_comm_group_object C) ⋙ add_comm_group_object.forget C ≅ 𝟭 C := iso.refl _

instance : reflects_isomorphisms (add_comm_group_object.forget C) := sorry

end preadditive

namespace functor

variables {C} {D : Type*} [category D]
  [has_finite_products C] [has_finite_products D] (F : C ⥤ D)
  [hF₀ : preserves_limit (functor.empty.{0} C) F]
  [hF₂ : preserves_limits_of_shape (discrete (walking_pair)) F]

include F hF₀ hF₂

@[simps]
def map_add_comm_group_object.obj (G : add_comm_group_object C) : add_comm_group_object D :=
{ X := F.obj G.X,
  zero := (preserves_terminal.iso F).inv ≫ F.map G.zero,
  add := (preserves_limit_pair.iso F G.X G.X).inv ≫ F.map G.add,
  neg := F.map G.neg,
  add_assoc' := sorry,
  add_zero' := sorry,
  comm' := sorry,
  add_left_neg' := sorry, }

@[simps]
def map_add_comm_group_object :
  add_comm_group_object C ⥤ add_comm_group_object D :=
{ obj := λ G, map_add_comm_group_object.obj F G,
  map := λ G₁ G₂ f, ⟨F.map f.1, sorry⟩, }

lemma additive_of_preserves_binary_products [preadditive C] [preadditive D] : F.additive :=
begin
  sorry,
end

end functor

end category_theory
