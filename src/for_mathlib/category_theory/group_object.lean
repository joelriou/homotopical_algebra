import category_theory.limits.shapes.finite_products
import category_theory.preadditive.additive_functor
import category_theory.limits.preserves.shapes.binary_products

noncomputable theory

namespace category_theory

open category

namespace limits

variables {C : Type*} [category C] [preadditive C]

variables (X Y : C) [has_binary_coproduct X Y] [has_binary_product X Y]

def coprod_iso_prod :
  X ⨿ Y ≅ X ⨯ Y :=
{ hom := prod.lift (coprod.desc (𝟙 X) 0) (coprod.desc 0 (𝟙 Y)),
  inv := limits.prod.fst ≫ coprod.inl + limits.prod.snd ≫ coprod.inr, }

@[simp, reassoc]
lemma coprod_inl_coprod_iso_prod_hom :
  coprod.inl ≫ (coprod_iso_prod X Y).hom = prod.lift (𝟙 X) 0 :=
begin
  dsimp [coprod_iso_prod],
  simp only [prod.comp_lift, coprod.inl_desc],
end

@[simp, reassoc]
lemma coprod_inr_coprod_iso_prod_hom :
  coprod.inr ≫ (coprod_iso_prod X Y).hom = prod.lift 0 (𝟙 Y) :=
begin
  dsimp [coprod_iso_prod],
  simp only [prod.comp_lift, coprod.inr_desc],
end

end limits

open limits

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

variable {C}

def add_comm_group_object.add_comm_group_hom
  (A : C) (G : add_comm_group_object C) : add_comm_group (A ⟶ G.X) :=
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

lemma add_comm_group_object_add [preadditive C] (G : add_comm_group_object C) :
  G.add = limits.prod.fst + limits.prod.snd :=
begin
  haveI : has_finite_biproducts C := limits.has_finite_biproducts.of_has_finite_products,
  let s₀ := terminal.from G.X ≫ G.zero,
  let s₁ := coprod.inl ≫ (coprod_iso_prod G.X G.X).hom ≫ G.add,
  let s₂ := coprod.inr ≫ (coprod_iso_prod G.X G.X).hom ≫ G.add,
  have hs₀ : ∃ t₀, t₀ = s₀ := ⟨s₀, rfl⟩,
  have hs₁ : ∃ t₁, t₁ = s₁ := ⟨s₁, rfl⟩,
  have hs₂ : ∃ t₂, t₂ = s₂ := ⟨s₂, rfl⟩,
  rcases hs₀ with ⟨t₀, ht₀⟩,
  rcases hs₁ with ⟨t₁, ht₁⟩,
  rcases hs₂ with ⟨t₂, ht₂⟩,
  have Gadd : G.add = limits.prod.fst ≫ t₁ + limits.prod.snd ≫ t₂,
  { rw [ht₁, ht₂],
    rw ← cancel_epi (coprod_iso_prod G.X G.X).hom,
    ext,
    { simp only [s₁, coprod_inl_coprod_iso_prod_hom_assoc, preadditive.comp_add,
        prod.lift_fst_assoc, id_comp, prod.lift_snd_assoc, zero_comp, add_zero], },
    { simp only [s₂, coprod_inr_coprod_iso_prod_hom_assoc, preadditive.comp_add,
        prod.lift_fst_assoc, zero_comp, prod.lift_snd_assoc, id_comp, zero_add], }, },
  have h₀ : t₁ ≫ t₁ = t₁ := by simpa only [Gadd, preadditive.comp_add, prod.map_fst_assoc,
    id_comp, prod.map_snd_assoc, prod.lift_fst_assoc, preadditive.add_comp, assoc,
    prod.lift_snd_assoc, zero_comp, add_zero]
      using prod.lift (𝟙 G.X) (prod.lift 0 0) ≫= G.add_assoc',
  have h₁ : t₁ = t₂ := by simpa only [Gadd, preadditive.comp_add,
    prod.lift_fst_assoc, prod.lift_snd_assoc, id_comp, zero_comp,
    add_zero, zero_add] using prod.lift 0 (𝟙 G.X) ≫= G.comm',
  subst h₁,
  have h₂ : t₀ ≫ t₁ + t₁ = 𝟙 G.X := by simpa only [ht₀, ← assoc, Gadd,
    preadditive.comp_add, prod.lift_fst_assoc, prod.lift_snd_assoc, id_comp] using G.add_zero',
  have h₃ : G.neg ≫ t₁ + t₁ = t₀ := by simpa only [ht₀, Gadd, preadditive.comp_add,
    prod.lift_fst_assoc, prod.lift_snd_assoc, id_comp] using G.add_left_neg',
  have h₄ : t₀ + t₁ = 𝟙 G.X,
  { rw [← h₃, preadditive.add_comp, h₀, assoc, h₀, h₃] at h₂,
    exact h₂, },
  have h₅ : t₀ = 𝟙 G.X -t₁ := by simp only [← h₄, add_sub_cancel],
  have h₆ : t₁ = 𝟙 G.X := by simpa only [h₀, h₅, preadditive.sub_comp,
    id_comp, sub_self, zero_add] using h₂,
  subst h₆,
  simpa only [comp_id] using Gadd,
end

local attribute [instance] add_comm_group_object.add_comm_group_hom

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

@[simp]
lemma id_val (G : add_comm_group_object C) : subtype.val (𝟙 G) = 𝟙 G.X := rfl

@[simp]
lemma comp_val {G₁ G₂ G₃ : add_comm_group_object C} (f : G₁ ⟶ G₂) (g : G₂ ⟶ G₃) :
  (f ≫ g).1 = f.1 ≫ g.1 := rfl

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

variable (C)

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

instance : reflects_isomorphisms (add_comm_group_object.forget C) :=
⟨λ G₁ G₂ f hf, begin
  haveI : is_iso f.1 := hf,
  refine ⟨⟨⟨inv f.1, _⟩, _, _⟩⟩,
  { simp only [← cancel_mono f.1, ← cancel_epi (limits.prod.map f.1 f.1), f.2, assoc,
    is_iso.inv_hom_id, comp_id, prod.map_map_assoc, is_iso.hom_inv_id, prod.map_id_id, id_comp], },
  { apply add_comm_group_object.hom_ext,
    exact is_iso.hom_inv_id f.1, },
  { apply add_comm_group_object.hom_ext,
    exact is_iso.inv_hom_id f.1, },
end⟩

variable {C}

lemma add_eq_of_add_comm_group [hC : preadditive C] {X Y : C} {G : add_comm_group_object C} (e : G.X ≅ Y)
  (f₁ f₂ : X ⟶ Y) : f₁ + f₂ = prod.lift (f₁ ≫ e.inv) (f₂ ≫ e.inv) ≫ G.add ≫ e.hom :=
by simp only [G.add_comm_group_object_add, add_comp, comp_add, prod.lift_fst_assoc, assoc,
    iso.inv_hom_id, comp_id, prod.lift_snd_assoc]

end preadditive

namespace functor

variables {C} {D : Type*} [category D]
  [has_finite_products D] (F : C ⥤ D)
  [hF₀ : preserves_limit (functor.empty.{0} C) F]
  [hF₂ : preserves_limits_of_shape (discrete (walking_pair)) F]

include F hF₀ hF₂

lemma preserves_limit_pair_compatibility₁ {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
  limits.prod.map (F.map f₁) (F.map f₂) = (preserves_limit_pair.iso F X₁ X₂).inv ≫
    F.map (limits.prod.map f₁ f₂) ≫ (preserves_limit_pair.iso F Y₁ Y₂).hom :=
begin
  rw [← cancel_epi ((preserves_limit_pair.iso F X₁ X₂).hom), iso.hom_inv_id_assoc],
  ext,
  { simp only [preserves_limit_pair.iso_hom, assoc, limits.prod.map_fst, prod_comparison_fst_assoc,
      prod_comparison_fst, ← F.map_comp], },
  { simp only [preserves_limit_pair.iso_hom, assoc, limits.prod.map_snd, prod_comparison_snd_assoc,
      prod_comparison_snd, ← F.map_comp], },
end

lemma preserves_limit_pair_compatibility₂ {X₁ X₂ : C} :
  limits.prod.lift (limits.prod.snd : F.obj X₁ ⨯ F.obj X₂ ⟶ F.obj X₂) (limits.prod.fst : F.obj X₁ ⨯ F.obj X₂ ⟶ F.obj X₁)
  = (preserves_limit_pair.iso F X₁ X₂).inv ≫
  F.map (limits.prod.lift (limits.prod.snd : X₁ ⨯ X₂ ⟶ X₂) (limits.prod.fst : X₁ ⨯ X₂ ⟶ X₁)) ≫
    (preserves_limit_pair.iso F X₂ X₁).hom :=
begin
  rw [← cancel_epi ((preserves_limit_pair.iso F X₁ X₂).hom), iso.hom_inv_id_assoc],
  ext,
  { simp only [preserves_limit_pair.iso_hom, prod_comparison_snd, prod_comparison_fst,
      prod.lift_fst, assoc, ← F.map_comp], },
  { simp only [preserves_limit_pair.iso_hom, prod_comparison_snd, prod_comparison_fst,
      prod.lift_snd, assoc, ← F.map_comp], },
end

lemma preserves_limit_pair_compatibility₃ {X Y₁ Y₂ : C} (f₁ : X ⟶ Y₁) (f₂ : X ⟶ Y₂) :
  limits.prod.lift (F.map f₁) (F.map f₂) =
    F.map (limits.prod.lift f₁ f₂) ≫ (preserves_limit_pair.iso F Y₁ Y₂).hom :=
begin
  ext,
  { simp only [prod.lift_fst, preserves_limit_pair.iso_hom, assoc, prod_comparison_fst,
      ← F.map_comp], },
  { simp only [prod.lift_snd, preserves_limit_pair.iso_hom, assoc, prod_comparison_snd,
      ← F.map_comp], },
end

lemma preserves_limit_pair_compatibility_fst (X₁ X₂ : C) :
  limits.prod.fst = (preserves_limit_pair.iso F X₁ X₂).inv ≫ F.map limits.prod.fst  :=
by rw [← cancel_epi (preserves_limit_pair.iso F X₁ X₂).hom,
    iso.hom_inv_id_assoc, preserves_limit_pair.iso_hom, prod_comparison_fst]

lemma preserves_limit_pair_compatibility_snd (X₁ X₂ : C) :
  limits.prod.snd = (preserves_limit_pair.iso F X₁ X₂).inv ≫ F.map limits.prod.snd  :=
by rw [← cancel_epi (preserves_limit_pair.iso F X₁ X₂).hom,
    iso.hom_inv_id_assoc, preserves_limit_pair.iso_hom, prod_comparison_snd]

lemma preserves_terminal_compatibility (X : C) :
  terminal.from (F.obj X) = F.map (terminal.from X) ≫ (preserves_terminal.iso F).hom :=
subsingleton.elim _ _

@[simps]
def map_add_comm_group_object.obj (G : add_comm_group_object C) : add_comm_group_object D :=
{ X := F.obj G.X,
  zero := (preserves_terminal.iso F).inv ≫ F.map G.zero,
  add := (preserves_limit_pair.iso F G.X G.X).inv ≫ F.map G.add,
  neg := F.map G.neg,
  add_assoc' := begin
    rw ← cancel_epi (limits.prod.map (𝟙 (F.obj G.X)) (preserves_limit_pair.iso F G.X G.X).hom),
    rw ← cancel_epi (preserves_limit_pair.iso F G.X (G.X ⨯ G.X)).hom,
    convert F.congr_map G.add_assoc',
    { simp only [F.map_comp, ← assoc],
      congr' 1,
      simp only [assoc, ← cancel_mono (preserves_limit_pair.iso F G.X G.X).hom,
        iso.inv_hom_id, comp_id],
      ext,
      { rw [assoc, assoc, assoc, prod.lift_fst, prod.map_map_assoc, comp_id,
          preserves_limit_pair_compatibility_fst, iso.hom_inv_id_assoc,
          ← F.map_id, preserves_limit_pair_compatibility₁, assoc, assoc,
          iso.hom_inv_id_assoc, iso.hom_inv_id_assoc, ← F.map_comp,
          ← F.map_comp, prod.lift_fst], },
      { rw [assoc, assoc, assoc, prod.lift_snd, prod.map_snd_assoc,
          preserves_limit_pair_compatibility_snd, assoc, iso.hom_inv_id_assoc,
          preserves_limit_pair_compatibility_snd, iso.hom_inv_id_assoc,
          ← F.map_comp, ← F.map_comp, prod.lift_snd], }, },
    { rw [prod.map_map_assoc, id_comp, iso.hom_inv_id_assoc, F.map_comp, ← assoc, ← assoc],
      conv_lhs { rw ← F.map_id, },
      simp only [preserves_limit_pair_compatibility₁, assoc, iso.hom_inv_id_assoc], },
  end,
  add_zero' := begin
    simp only [preserves_terminal_compatibility, assoc, iso.hom_inv_id_assoc, ← F.map_comp],
    nth_rewrite 0 ← F.map_id,
    rw [preserves_limit_pair_compatibility₃, assoc, iso.hom_inv_id_assoc, ← F.map_comp,
      G.add_zero', F.map_id],
  end,
  comm' := by simp only [preserves_limit_pair_compatibility₂, assoc,
    iso.hom_inv_id_assoc, ← F.map_comp, G.comm'],
  add_left_neg' := begin
    rw [← F.map_id, preserves_limit_pair_compatibility₃, assoc, iso.hom_inv_id_assoc,
      ← F.map_comp, G.add_left_neg', preserves_terminal_compatibility, assoc,
      iso.hom_inv_id_assoc, F.map_comp],
  end, }

@[simps]
def map_add_comm_group_object :
  add_comm_group_object C ⥤ add_comm_group_object D :=
{ obj := λ G, map_add_comm_group_object.obj F G,
  map := λ G₁ G₂ f, ⟨F.map f.1, by simp only [map_add_comm_group_object.obj_add, assoc,
    ← F.map_comp, f.2, preserves_limit_pair_compatibility₁, assoc, iso.hom_inv_id_assoc]⟩, }

lemma map_add_comm_group_object_add_compatibility {X : C} (G : add_comm_group_object C)
  (f₁ f₂ : X ⟶ G.X) : F.map (prod.lift f₁ f₂ ≫ G.add) =
  prod.lift (F.map f₁) (F.map f₂) ≫ (F.map_add_comm_group_object.obj G).add :=
begin
  dsimp [map_add_comm_group_object.obj],
  simp only [assoc, preserves_limit_pair_compatibility₃, iso.hom_inv_id_assoc, ← F.map_comp],
end

lemma additive_of_preserves_binary_products [hC : preadditive C] [hD : preadditive D] : F.additive :=
⟨λ X Y f₁ f₂, begin
  let G := (preadditive.to_add_comm_group_object C).obj Y,
  let e : G.X ≅ Y := iso.refl _,
  let G' := F.map_add_comm_group_object.obj G,
  let e' : G'.X ≅ F.obj Y := iso.refl _,
  rw preadditive.add_eq_of_add_comm_group e,
  rw preadditive.add_eq_of_add_comm_group e',
  dsimp [e, e'],
  repeat { erw comp_id, },
  exact map_add_comm_group_object_add_compatibility F G f₁ f₂,
end⟩

end functor

end category_theory
