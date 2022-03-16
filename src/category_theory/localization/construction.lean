/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow_class
import category_theory.quotient
import category_theory.path_category
import category_theory.category.Quiv
import category_theory.equivalence

noncomputable theory

open category_theory
open category_theory.category

namespace category_theory

namespace quotient

lemma functor_map_surj {C : Type*} [category C] (r : hom_rel C) (s t : C) :
  function.surjective (λ (f : s ⟶ t), (functor r).map f) :=
begin
  intro f,
  cases surjective_quot_mk _ f with g hg,
  use [g, hg],
end

end quotient

namespace functor

--lemma congr_obj {D₁ D₂ : Type*} [category D₁] [category D₂] {F G : D₁ ⥤ D₂}
--(h : F = G) : ∀ X : D₁, F.obj X = G.obj X :=
--by { intro X, rw h, }

lemma congr_map_conjugate {D₁ D₂ : Type*} [category D₁] [category D₂] {F G : D₁ ⥤ D₂}
(h : F = G) {X Y : D₁} (f : X ⟶ Y) : F.map f =
eq_to_hom (by rw h) ≫ G.map f ≫ eq_to_hom (by rw h) :=
by { subst h, erw [id_comp, comp_id], }

lemma conjugate_inv_of_congr_map_conjugate {D₁ D₂ : Type*} [category D₁] [category D₂] (F G : D₁ ⥤ D₂)
  {X Y : D₁} (e : X ≅ Y) (hX : F.obj X = G.obj X) (hY : F.obj Y = G.obj Y)
  (h₂ : F.map e.hom = eq_to_hom (by rw hX) ≫ G.map e.hom ≫ eq_to_hom (by rw hY)) :
F.map e.inv = eq_to_hom (by rw hY) ≫ G.map e.inv ≫ eq_to_hom (by rw hX) :=
by simp only [← is_iso.iso.inv_hom e, functor.map_inv, h₂, is_iso.inv_comp, inv_eq_to_hom, assoc]

lemma congr_map {D D' : Type*} [category D] [category D'] (F : D ⥤ D')
{X Y : D} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g :=
by { subst h, }

lemma assoc {C D E F : Type*} [category C] [category D]
  [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl

end functor

universes v v' v₃ u u' u₃

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]
variables {E : Type u₃} [category.{v₃} E]

namespace arrow

def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

def is_inverted_by_of_comp (f : arrow C) (F : C ⥤ D) (G : D ⥤ E) (hf : f.is_inverted_by F) : f.is_inverted_by (F ⋙ G) :=
begin
  haveI : is_iso (F.map f.hom) := hf,
  exact (infer_instance : is_iso (G.map (F.map f.hom))),
end

end arrow

namespace arrow_class

def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : W), f.1.is_inverted_by F

def is_inverted_by_of_comp (W : arrow_class C) (F : C ⥤ D) (G : D ⥤ E) (hW : W.is_inverted_by F) : W.is_inverted_by (F ⋙ G) :=
by { intro w, exact w.1.is_inverted_by_of_comp F G (hW w), }


structure loc_quiver (W : arrow_class C) := (obj : C)

variable (W : arrow_class C)

instance : quiver (loc_quiver W) :=
{ hom := λ A B, (A.obj ⟶ B.obj) ⊕ { f : B.obj ⟶ A.obj // arrow.mk f ∈ W} }

@[simps]
def ι_loc_quiver (X : C) : paths (loc_quiver W) := paths.of.obj ⟨X⟩

namespace localization

structure relation := (X Y : paths (loc_quiver W)) (f₁ f₂ : X ⟶ Y)

namespace relation

variable (W)
@[simps]
def mk' {X Y : paths (loc_quiver W)} (f₁ f₂ : X ⟶ Y) := relation.mk X Y f₁ f₂
variable {W}

lemma congr_X_obj {r₁ r₂ : relation W} (h : r₁ = r₂) : r₁.X.obj = r₂.X.obj := by subst h
lemma congr_Y_obj {r₁ r₂ : relation W} (h : r₁ = r₂) : r₁.Y.obj = r₂.Y.obj := by subst h
lemma congr_f₁_heq {r₁ r₂ : relation W} (h : r₁ = r₂) : r₁.f₁ == r₂.f₁ := by subst h
lemma congr_f₂_heq {r₁ r₂ : relation W} (h : r₁ = r₂) : r₁.f₂ == r₂.f₂ := by subst h
lemma congr_f₁ {X Y : paths (loc_quiver W)} {f₁ f₂ f₁' f₂' : X ⟶ Y}
  (h : mk' W f₁ f₂ = mk' W f₁' f₂') : f₁ = f₁' := eq_of_heq (congr_f₁_heq h)
lemma congr_f₂ {X Y : paths (loc_quiver W)} {f₁ f₂ f₁' f₂' : X ⟶ Y}
  (h : mk' W f₁ f₂ = mk' W f₁' f₂') : f₂ = f₂' := eq_of_heq (congr_f₂_heq h)

end relation

def ψ₁ (f : arrow C) : W.ι_loc_quiver f.left ⟶ W.ι_loc_quiver f.right := paths.of.map (sum.inl f.hom)

def ψ₂' (g : arrow C) (hg : g ∈ W) : W.ι_loc_quiver g.right ⟶ W.ι_loc_quiver g.left :=
paths.of.map (sum.inr ⟨g.hom, (by { convert hg, rw arrow.mk_eq, })⟩)

variable {W}
def ψ₂ (w : W) : W.ι_loc_quiver w.1.right ⟶ W.ι_loc_quiver w.1.left := ψ₂' W w.1 w.2

variable (W)
@[simps]
def relations₀ : C → relation W := λ X, relation.mk' W (ψ₁ W (arrow.mk (𝟙 X))) (𝟙 _)

variable (C)
def R₁ := { t : arrow C × arrow C // t.1.right = t.2.left }
variable {C}

def ρ₁ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : R₁ C := ⟨⟨arrow.mk f, arrow.mk g⟩, rfl⟩

@[simps]
def relations₁ : R₁ C → relation W := λ t,
{ X := W.ι_loc_quiver t.1.1.left,
  Y := W.ι_loc_quiver t.1.2.right,
  f₁ := ψ₁ W (arrow.mk (t.1.1.hom ≫ eq_to_hom t.2 ≫ t.1.2.hom)),
  f₂ := ψ₁ W t.1.1 ≫ eq_to_hom (by { congr, exact t.2,}) ≫ ψ₁ W t.1.2, }

@[simps]
def relations₂ (w : W) : relation W := relation.mk' W (ψ₁ W w.1 ≫ ψ₂ w) (𝟙 _)

@[simps]
def relations₃ (w : W) : relation W := relation.mk' W (ψ₂ w ≫ ψ₁ W w.1) (𝟙 _)

variable {W}
def belongs_to {A B : paths (loc_quiver W)} (f g : A ⟶ B)
  {D : Type*} (relations : D → relation W) : Prop := ∃ (r : D), relations r = relation.mk' W f g

variable (W)
def relations : hom_rel (paths (loc_quiver W)) :=
λ X Y f g, belongs_to f g (relations₀ W) ∨ belongs_to f g (relations₁ W) ∨
  belongs_to f g (relations₂ W) ∨ belongs_to f g (relations₃ W)

end localization

@[derive category]
def localization := category_theory.quotient (localization.relations W)

open localization

namespace localization

variable (W)

def Q : C ⥤ W.localization :=
{ obj := λ X, (quotient.functor (relations W)).obj (W.ι_loc_quiver X),
  map := λ X Y f, (quotient.functor (relations W)).map (ψ₁ W f),
  map_id' := λ X, begin
    apply quotient.sound (localization.relations W),
    exact or.inl ⟨X, rfl⟩,
  end,
  map_comp' := λ X Y Z f g, begin
    apply quotient.sound (localization.relations W),
    exact or.inr (or.inl (begin
      use localization.ρ₁ f g, dsimp only [localization.relations₁],
      congr,
      erw id_comp,refl,
    end)),
  end }

variable {W}

def Wiso (w : W) : iso ((Q W).obj w.1.left) ((Q W).obj w.1.right) :=
{ hom := (Q W).map w.1.hom,
  inv := (quotient.functor (relations W)).map (ψ₂ w),
  hom_inv_id' := begin
    erw ← (quotient.functor _).map_comp,
    apply quotient.sound,
    refine or.inr (or.inr (or.inl ⟨w, rfl⟩)),
  end,
  inv_hom_id' := begin
    erw ← (quotient.functor _).map_comp,
    apply quotient.sound,
    exact or.inr (or.inr (or.inr ⟨w, rfl⟩)),
  end }

@[simps]
def lift_to_loc_quiver {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  prefunctor (loc_quiver W) D :=
{ obj := by { rintro ⟨X⟩, exact G.obj X, },
  map := begin
    rintros ⟨X⟩ ⟨Y⟩ (f|⟨g, hg⟩),
    { exact G.map f, },
    { haveI : is_iso (G.map g) := hG ⟨arrow.mk g, hg⟩,
      exact inv (G.map g), },
  end }

/-- Fix category_theory.theory.Quiv.lean-/
@[simps]
def lift_to_path_category {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  paths (loc_quiver W) ⥤ D :=
{ obj := λ X, (lift_to_loc_quiver G hG).obj X,
  map := λ X Y f, compose_path ((lift_to_loc_quiver G hG).map_path f), }

@[simp]
lemma lift_ψ₁_eq {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G)
  (f : arrow C) : (lift_to_path_category G hG).map (ψ₁ W f) = G.map f.hom :=
begin
  dsimp [lift_to_path_category, ψ₁, quiver.hom.to_path],
  simpa only [id_comp],
end

@[simp]
lemma lift_ψ₂_eq {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G)
  (w : W) : (lift_to_path_category G hG).map (ψ₂ w) = 
  (by { haveI : is_iso (G.map w.1.hom) := hG w, exact inv (G.map w.1.hom), }) :=
begin
  dsimp [lift_to_loc_quiver, lift_to_path_category, ψ₂, ψ₂', quiver.hom.to_path],
  simpa only [id_comp],
end

lemma W_is_inverted_by_Q : W.is_inverted_by (Q W) := λ w, is_iso.of_iso (Wiso w)

def lift {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  localization W ⥤ D :=
begin
  apply quotient.lift (relations W) (lift_to_path_category G hG),
  { rintro ⟨X⟩ ⟨Y⟩ f₁ f₂ r,
    rcases r with (_|_|_|_),
    work_on_goal 1 { rcases r with ⟨X', r⟩, },
    work_on_goal 2 { rcases r with ⟨⟨⟨⟨X',Z,f⟩,⟨Z',Y',g⟩⟩, h⟩, r⟩, },
    work_on_goal 3 { rcases r with ⟨w, r⟩, },
    work_on_goal 4 { rcases r with ⟨w, r⟩, },
    all_goals {
      have eqX := relation.congr_X_obj r,
      have eqY := relation.congr_Y_obj r,
      dsimp at eqX eqY,
      substs eqX eqY,
      have eqf₁ := relation.congr_f₁ r,
      have eqf₂ := relation.congr_f₂ r,
      substs eqf₁ eqf₂, clear r, },
    { erw [lift_ψ₁_eq, functor.map_id, functor.map_id],
      refl, },
    { dsimp at h,
      substs h,
      dsimp only [arrow.mk],
      simp only [functor.map_comp, lift_ψ₁_eq,
        eq_to_hom_refl, functor.map_id, id_comp], },
    all_goals
    { erw [functor.map_comp, functor.map_id, lift_ψ₁_eq, lift_ψ₂_eq], },
    { apply is_iso.hom_inv_id, },
    { apply is_iso.inv_hom_id, }, },
end

@[simp]
lemma fac {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  Q W ⋙ lift G hG = G :=
begin
  apply functor.ext,
  { intros X Y f,
    dsimp [lift, lift_to_path_category, lift_to_loc_quiver, Q, ψ₁, quiver.hom.to_path,
      ι_loc_quiver],
    erw [id_comp, comp_id, id_comp],
    refl, },
  { intro X,
    refl, }
end

lemma uniq {D : Type*} [category D] (G₁ G₂ : localization W ⥤ D) (h : Q W ⋙ G₁ = Q W ⋙ G₂) : G₁ = G₂ :=
begin
  suffices h' : (quotient.functor (relations W)) ⋙ G₁ = (quotient.functor (relations W)) ⋙ G₂,
  { apply functor.ext,
    { rintros ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ ⟨f⟩,
      convert functor.congr_map_conjugate h' f, },
    { rintro ⟨⟨X⟩⟩,
      convert functor.congr_obj h X, }, },
  { apply paths.ext_functor,
    { rintro ⟨X⟩ ⟨Y⟩ f,
      cases f,
      { convert functor.congr_map_conjugate h f, },
      { rcases f with ⟨g, hg⟩,
        dsimp at g hg,
        have hα : (Wiso ⟨arrow.mk g, hg⟩).hom = (Q W).map g := rfl,
        have h' := functor.congr_map_conjugate h g,
        simp only [functor.comp_map, ← hα] at h',
        refine functor.conjugate_inv_of_congr_map_conjugate G₁ G₂ _ _ _ h',
        { convert functor.congr_obj h Y, },
        { convert functor.congr_obj h X, }, }, },
    { ext X,
      cases X,
      have eq := functor.congr_obj h X,
      dsimp at ⊢ eq,
      convert eq, }, },
end

instance (w : W) : is_iso ((Q W).map w.1.hom) := is_iso.of_iso (Wiso w)

variable (W)

def Q_obj_bijection : C ≃ W.localization :=
{ to_fun := (Q W).obj,
  inv_fun := λ X, X.as.1,
  left_inv := λ X, begin refl, end,
  right_inv := λ X, by { cases X, cases X, refl, }, }

variable {W}

end localization

variable (L : C ⥤ D)

structure is_localization (W : arrow_class C) (L : C ⥤ D) :=
(inverts_W : W.is_inverted_by L)
(is_equivalence : is_equivalence (localization.lift L inverts_W))

structure is_strict_localization (W : arrow_class C) (L : C ⥤ D) extends is_localization W L :=
(is_isomorphism : (localization.lift L inverts_W ⋙ is_equivalence.inverse) = 𝟭 _
  ∧ (is_equivalence.inverse ⋙ localization.lift L inverts_W) = 𝟭 _)

structure is_strict_localization_fixed_target
(W : arrow_class C) (F : C ⥤ D)  (E : Type u₃) [category.{v₃} E] :=
  (inverts_W : W.is_inverted_by F)
  (lift : Π (G : C ⥤ E) (hG : W.is_inverted_by G), D ⥤ E)
  (fac : ∀ (G : C ⥤ E) (hG : W.is_inverted_by G), F ⋙ lift G hG = G)
  (uniq : ∀ (G₁ G₂ : D ⥤ E), F ⋙ G₁ = F ⋙ G₂ → G₁ = G₂)

namespace localization

def universal_property {E : Type u₃} [category.{v₃} E] :
  W.is_strict_localization_fixed_target (localization.Q W) E :=
{ inverts_W := W_is_inverted_by_Q,
  lift := lift,
  fac := fac,
  uniq := uniq }

end localization

lemma strict_localization_is_ess_unique_on_obj {W : arrow_class C} {D' : Type*} [category D']
  (F₁ : C ⥤ D) (F₂ : C ⥤ D')
  (L₁ : W.is_strict_localization_fixed_target F₁ D') (L₂ : W.is_strict_localization_fixed_target F₂ D)
  (L₁' : W.is_strict_localization_fixed_target F₁ D) (L₂' : W.is_strict_localization_fixed_target F₂ D') :
  L₁.lift F₂ L₂.inverts_W ⋙ L₂.lift F₁ L₁.inverts_W = 𝟭 _ :=
begin
  apply L₁'.uniq,
  rw [← functor.assoc, L₁.fac F₂ L₂.inverts_W, L₂.fac F₁ L₁.inverts_W, functor.comp_id],
end

@[simps]
def strict_localization_is_ess_unique {W : arrow_class C} {D' : Type*} [category D']
  (F₁ : C ⥤ D) (F₂ : C ⥤ D')
  (L₁ : W.is_strict_localization_fixed_target F₁ D') (L₂ : W.is_strict_localization_fixed_target F₂ D)
  (L₁' : W.is_strict_localization_fixed_target F₁ D) (L₂' : W.is_strict_localization_fixed_target F₂ D') : D ≌ D' :=
{ functor := L₁.lift F₂ L₂.inverts_W,
  inverse := L₂.lift F₁ L₁.inverts_W,
  unit_iso := eq_to_iso 
    (strict_localization_is_ess_unique_on_obj F₁ F₂ L₁ L₂ L₁' L₂').symm,
  counit_iso := eq_to_iso 
    (strict_localization_is_ess_unique_on_obj F₂ F₁ L₂ L₁ L₂' L₁'),
  functor_unit_iso_comp' := begin
    intro X,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans, eq_to_hom_refl],
  end }

namespace is_strict_localization

def mk' (W : arrow_class C) (L : C ⥤ D)
  (h₁ : W.is_strict_localization_fixed_target L W.localization)
  (h₂ : W.is_strict_localization_fixed_target L D) :
  is_strict_localization W L :=
begin
  let e := (strict_localization_is_ess_unique (localization.Q W) L
      (localization.universal_property W) h₁ (localization.universal_property W) h₂),
  have eq₁ := strict_localization_is_ess_unique_on_obj (localization.Q W) L
      (localization.universal_property W) h₁ (localization.universal_property W) h₂,
  have eq₂ := strict_localization_is_ess_unique_on_obj L (localization.Q W)
      h₁ (localization.universal_property W) h₂ (localization.universal_property W),
  exact 
  { inverts_W := h₁.inverts_W,
    is_equivalence := is_equivalence.of_equivalence e,
    is_isomorphism := ⟨eq₁, eq₂⟩, }
end

@[simps]
def lift_functor {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) : W.localization ⥤ D :=
localization.lift L hL.inverts_W

lemma arrow.mk_comp_eq_to_hom {X Y Z : D} (f : X ⟶ Y) (h : Y = Z) : arrow.mk (f ≫ eq_to_hom h) = arrow.mk f :=
by { subst h, erw comp_id, }
lemma arrow.mk_eq_to_hom_comp {X Y Z : D} (f : Y ⟶ Z) (h : X = Y) : arrow.mk (eq_to_hom h ≫ f) = arrow.mk f :=
by { subst h, erw id_comp, }

lemma arrow_class_is_top {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L)
  (A : arrow_class D)
  (hA₁ : ∀ {X Y : C} (f : X ⟶ Y), arrow.mk (L.map f) ∈ A)
  (hA₂ : ∀ {X Y : D} (e : X ≅ Y), arrow.mk e.hom ∈ A → arrow.mk e.inv ∈ A)
  (hA₃ : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : arrow.mk f ∈ A) (hg : arrow.mk g ∈ A),
  arrow.mk (f ≫ g) ∈ A) : A = set.univ :=
begin
  haveI hF₁: is_equivalence hL.lift_functor := hL.is_equivalence,
  suffices : ∀ {X Y : W.localization} (f : X ⟶ Y), arrow.mk (hL.lift_functor.map f) ∈ A,
  { ext f,
    split,
    { intro h, apply set.mem_univ, },
    { intro hf,
      have h := this (hL.is_equivalence.inverse.map f.hom),
      erw [← functor.comp_map, functor.congr_map_conjugate hL.is_isomorphism.2 f.hom, functor.id_map] at h,
      convert h,
      ext,
      { simp only [arrow.mk_hom, assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id, eq_to_hom_trans_assoc, id_comp], },
      { simpa only [arrow.mk_comp_eq_to_hom, arrow.mk_eq_to_hom_comp], },
      { simpa only [arrow.mk_comp_eq_to_hom, arrow.mk_eq_to_hom_comp], }, }, },
  suffices : ∀ {X Y : C} (g : (localization.Q W).obj X ⟶ (localization.Q W).obj Y), arrow.mk (hL.lift_functor.map g) ∈ A,
  { intros X Y g,
    let X' := (localization.Q_obj_bijection W).inv_fun X,
    let Y' := (localization.Q_obj_bijection W).inv_fun Y,
    let g' : (localization.Q W).obj X' ⟶ (localization.Q W).obj Y' := eq_to_hom _ ≫ g ≫ eq_to_hom _, rotate,
    { exact (localization.Q_obj_bijection W).right_inv X, },
    { exact ((localization.Q_obj_bijection W).right_inv Y).symm, },
    simpa only [functor.map_comp, eq_to_hom_map, arrow.mk_eq_to_hom_comp, arrow.mk_comp_eq_to_hom] using this g', },
  suffices : ∀ {X Y : paths W.loc_quiver} (φ : X ⟶ Y), arrow.mk (hL.lift_functor.map ((quotient.functor (relations W)).map φ)) ∈ A,
  { intros X Y g,
    cases quotient.functor_map_surj _ _ _ g with φ hφ,
    rw ← hφ,
    exact this φ, },
  intros X Y φ,
  induction φ with Z₁ Z₂ γ f hγ,
  { simp,
    cases X,
    simpa only [L.map_id] using hA₁ (𝟙 X), },
  { refine hA₃ _ _ hγ _,
    cases Z₁,
    cases Z₂,
    cases f,
    { exact hA₁ f, },
    { rcases f with ⟨f, hf⟩,
      haveI : is_iso (L.map f) := hL.inverts_W ⟨arrow.mk f, hf⟩,
      apply hA₂ (as_iso (L.map f)),
      apply hA₁, }, },
end

def obj_bijection_lift {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) : W.localization ≃ D :=
{ to_fun := hL.lift_functor.obj,
  inv_fun := hL.is_equivalence.inverse.obj,
  left_inv := functor.congr_obj hL.is_isomorphism.1,
  right_inv := functor.congr_obj hL.is_isomorphism.2, }

def obj_bijection {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) : C ≃ D :=
begin
  calc C ≃ W.localization : localization.Q_obj_bijection W
  ... ≃ D : hL.obj_bijection_lift,
end

def naturality_condition {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) : arrow_class C :=
λ w, F.map w.hom ≫ app w.right = app w.left ≫ G.map w.hom

def naturality_condition_iff {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) {X Y : C} (f : X ⟶ Y) :
  arrow.mk f ∈ naturality_condition app ↔ (F.map f ≫ app Y = app X ≫ G.map f) := by refl

def naturality_condition_inv {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) (X Y : C) (e : X ≅ Y)
(he : arrow.mk e.hom ∈ naturality_condition app) : arrow.mk e.inv ∈ naturality_condition app :=
begin
  rw naturality_condition_iff at ⊢ he,
  rw [← cancel_mono (G.map e.hom), assoc, ← he, ← assoc, ← F.map_comp, assoc, ← G.map_comp,
    e.inv_hom_id, F.map_id, G.map_id, id_comp, comp_id],
end

def naturality_condition_comp {F G : C ⥤ D} (app : Π (X : C), F.obj X ⟶ G.obj X) (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
(hf : arrow.mk f ∈ naturality_condition app) (hg : arrow.mk g ∈ naturality_condition app) :
  arrow.mk (f ≫ g) ∈ naturality_condition app :=
begin
  rw naturality_condition_iff at ⊢ hf hg,
  rw [F.map_comp, G.map_comp, assoc, hg, ← assoc, hf, assoc],
end

namespace nat_trans_extension

def app {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) (X : D) :
  F.obj X ⟶ G.obj X :=
begin
  have eq := λ X, (hL.obj_bijection.right_inv X).symm,
  refine eq_to_hom _ ≫ τ.app (hL.obj_bijection.inv_fun X) ≫ eq_to_hom _,
  { congr, apply eq, },
  { symmetry, congr, apply eq, },
end

lemma app_eq {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) (X : C) :
  (app hL τ) (L.obj X) = τ.app X :=
begin
  dsimp only [app],
  have h := τ.naturality (eq_to_hom (hL.obj_bijection.left_inv X)),
  simp only [eq_to_hom_map] at h,
  erw ← h,
  simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp],
end

end nat_trans_extension

def nat_trans_extension {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) :
  F ⟶ G :=
begin
  have h := arrow_class_is_top hL (naturality_condition (nat_trans_extension.app hL τ)) _
    (naturality_condition_inv _) (naturality_condition_comp _), rotate,
  { intros X Y f,
    simp only [naturality_condition_iff, nat_trans_extension.app_eq],
    exact τ.naturality f, },
  exact
  { app := nat_trans_extension.app hL τ,
    naturality' := λ X Y f, begin
      have hf : arrow.mk f ∈ naturality_condition (nat_trans_extension.app hL τ),
      { rw h,
        apply set.mem_univ, },
      exact hf,
    end, }
end

lemma nat_trans_extension_hcomp {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) {F G : D ⥤ E} (τ : L ⋙ F ⟶ L ⋙ G) :
  (𝟙 L) ◫ nat_trans_extension hL τ = τ :=
begin
  ext X,
  simp only [nat_trans.hcomp_app, nat_trans.id_app, functor.map_id, comp_id],
  apply nat_trans_extension.app_eq,
end

end is_strict_localization

end arrow_class

def composable_morphisms (n : ℕ) (D : Type*) [category D] := fin (n+1) ⥤ D

namespace composable_morphisms

def composition {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : arrow D :=
F.map (hom_of_le (fin.last _).zero_le)

def ith_arrow {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) (i : fin n) : arrow D :=
F.map (hom_of_le (show fin.cast_succ i ≤ i.succ,
by simp only [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.coe_succ, le_add_iff_nonneg_right, zero_le_one]))

end composable_morphisms

namespace arrow_class

namespace is_strict_localization

@[simps]
def inv {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (w : W) : arrow D :=
begin
  haveI : is_iso (L.map (w.1.hom)) := hL.inverts_W w,
  exact inv (L.map (w.1.hom)),
end

lemma description_arrows {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (f : arrow D) :
  ∃ (n : ℕ) (F : composable_morphisms n D), F.composition = f ∧
  ∀ (i : fin (n)), (∃ g : arrow C, F.ith_arrow i = L.map_arrow.obj g) ∨ (∃ (w : W), F.ith_arrow i = hL.inv w) :=
begin
  sorry
end

end is_strict_localization

end arrow_class

end category_theory
