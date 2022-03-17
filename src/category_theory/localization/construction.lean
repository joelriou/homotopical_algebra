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
  map := λ X Y f, (quotient.functor (relations W)).map (ψ₁ W (arrow.mk f)),
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

lemma Q_map_eq {X Y : C} (f : X ⟶ Y) : (Q W).map f = (quotient.functor (relations W)).map (ψ₁ W (arrow.mk f)) := by refl

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

lemma Wiso_inv_eq (w : W) : (quotient.functor (relations W)).map (ψ₂ w) = (Wiso w).inv := by refl

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
    erw [id_comp, comp_id, id_comp], },
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

@[simp]
lemma lift_functor_fac {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) :
  localization.Q W ⋙ hL.lift_functor = L :=
localization.fac _ _

lemma arrow.mk_comp_eq_to_hom {X Y Z : D} (f : X ⟶ Y) (h : Y = Z) : arrow.mk (f ≫ eq_to_hom h) = arrow.mk f :=
by { subst h, erw comp_id, }
lemma arrow.mk_eq_to_hom_comp {X Y Z : D} (f : Y ⟶ Z) (h : X = Y) : arrow.mk (eq_to_hom h ≫ f) = arrow.mk f :=
by { subst h, erw id_comp, }

lemma arrow_class_is_univ {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L)
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
  have h := arrow_class_is_univ hL (naturality_condition (nat_trans_extension.app hL τ)) _
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

namespace arrow

@[simps]
def composition {D : Type*} [category D] (w₁ w₂ : arrow D) (e : w₁.right = w₂.left) : arrow D :=
{ left := w₁.left,
  right := w₂.right,
  hom := w₁.hom ≫ eq_to_hom e ≫ w₂.hom }

@[simp]
lemma map_arrow_comp {D E : Type*} [category D] [category E] (F : D ⥤ E) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map_arrow.obj (arrow.mk (f ≫ g)) = composition (F.map_arrow.obj (arrow.mk f)) (F.map_arrow.obj (arrow.mk g)) rfl :=
begin
  ext,
  { simp only [functor.map_arrow_obj_hom, arrow.mk_hom, functor.map_comp, eq_to_hom_refl, composition_hom, id_comp, comp_id], },
  { refl, },
  { refl, },
end

@[simp]
lemma map_arrow_of_mk {D E : Type*} [category D] [category E] (F : D ⥤ E) {X Y : D} (f : X ⟶ Y) :
  F.map_arrow.obj (arrow.mk f) = arrow.mk (F.map f) := by refl

end arrow

def composable_morphisms (n : ℕ) (D : Type*) [category D] := fin (n+1) ⥤ D

namespace composable_morphisms

def mk_0 {D : Type*} [category D] (X : D) : composable_morphisms 0 D :=
{ obj := λ i, X,
  map := λ i j f, 𝟙 X }

lemma fin.eq_one_of_geq_one {i : fin 2} (hi : 1 ≤ i) : i = 1 := le_antisymm i.is_le hi

lemma fin.eq_one_of_neq_zero {i : fin 2} (hi : i ≠ 0) : i = 1 :=
begin
  apply fin.eq_one_of_geq_one,
  by_contradiction,
  apply hi,
  ext,
  simpa only [fin.le_iff_coe_le_coe, fin.coe_one, not_le, nat.lt_one_iff] using h,
end

@[simps]
def mk_1 {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : composable_morphisms 1 D :=
{ obj := λ i, if i = 0 then X₀ else X₁,
  map := λ i j g, begin
    split_ifs with hi hj hj,
    { exact 𝟙 X₀, },
    { exact f, },
    { exfalso,
      apply hi,
      ext,
      simpa only [hj, fin.le_iff_coe_le_coe, fin.coe_zero, nonpos_iff_eq_zero] using le_of_hom g, },
    { exact 𝟙 X₁, },
  end,
  map_id' := λ X, begin
    split_ifs,
    { subst h, refl, },
    { have h' := fin.eq_one_of_neq_zero h, subst h', refl, },
  end,
  map_comp' := λ i j k ij jk, begin
    split_ifs with hi,
    { subst hi,
      by_cases hj : j = 0,
      { subst hj,
        have hij : 𝟙 _ = ij  := hom_of_le_le_of_hom _,
        subst hij,
        erw id_comp,
        refl, },
      { have hj' := fin.eq_one_of_neq_zero hj,
        subst hj',
        have hk' := fin.eq_one_of_geq_one (le_of_hom jk),
        subst hk',
        exact (comp_id _).symm, }, },
    { have hi' := fin.eq_one_of_neq_zero hi,
      subst hi',
      have hj' := fin.eq_one_of_geq_one (le_of_hom ij),
      subst hj',
      have hk' := fin.eq_one_of_geq_one (le_of_hom jk),
      subst hk',
      have hij : 𝟙 _ = ij := hom_of_le_le_of_hom _,
      have hjk : 𝟙 _ = jk := hom_of_le_le_of_hom _,
      substs hij hjk,
      exact (id_comp (𝟙 _)).symm, }
  end, }


@[simp]
def left {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : D := F.obj 0
@[simp]
def right {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : D := F.obj (fin.last _)

@[simp]
lemma mk_1_left {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).left = X₀ := by refl
@[simp]
lemma mk_1_right {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).right = X₁ := by refl

@[simp]
def composition {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : arrow D :=
F.map (hom_of_le (fin.last _).zero_le)
@[simp]
lemma mk_1_composition {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).composition = arrow.mk f := by refl

@[simp]
def ith_arrow {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) (i : fin n) : arrow D :=
F.map (hom_of_le (show fin.cast_succ i ≤ i.succ,
by simp only [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.coe_succ, le_add_iff_nonneg_right, zero_le_one]))

namespace join

def obj {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₁+n₂+1)) : D :=
begin
  by_cases hi : (i : ℕ) ≤ n₁,
  { exact F₁.obj ⟨(i : ℕ), nat.lt_succ_iff.mpr hi⟩, },
  { refine F₂.obj ⟨(i : ℕ)-n₁, _⟩,
    cases nat.le.dest (le_of_not_ge hi) with k hk,
    simpa only [← hk, add_tsub_cancel_left, add_assoc, add_lt_add_iff_left n₁] using i.is_lt, },
end

@[simp]
def ι₁ {n₁ n₂ : ℕ} (i : fin (n₁+1)) : fin (n₁+n₂+1) := fin.cast_le (by { rw [add_assoc, add_comm n₂, ← add_assoc], exact le_self_add, }) i
@[simp]
def ι₂ {n₁ n₂ : ℕ} (i : fin (n₂+1)) : fin (n₁+n₂+1) := ⟨n₁+i, by { rw add_assoc, exact add_lt_add_left (i.is_lt) n₁, }⟩

def obj₁ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₁+1)) : obj F₁ F₂ e (ι₁ i) = F₁.obj i :=
begin
  have hi := i.is_le,
  dsimp [obj],
  split_ifs,
  congr,
  ext,
  simp only [ι₁, fin.eta],
end

def ρ₁ {n₁ n₂ : ℕ} (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : fin (n₁+1) := ⟨(i : ℕ), nat.lt_succ_iff.mpr hi⟩
def ρ₂ {n₁ n₂ : ℕ} (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : fin (n₂+1) := ⟨(i : ℕ)-n₁, begin 
  cases nat.le.dest (le_of_not_ge hi) with k hk,
  simpa only [← hk, add_tsub_cancel_left, add_assoc, add_lt_add_iff_left n₁] using i.is_lt,
end⟩

def obj₁' {n₁ n₂ : ℕ} {D : Type*} [category D] {F₁ : composable_morphisms n₁ D} {F₂ : composable_morphisms n₂ D}
  {e : F₁.right = F₂.left} (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : obj F₁ F₂ e i = F₁.obj (ρ₁ i hi) :=
begin
  rw ← obj₁ F₁ F₂ e,
  congr,
  simp only [ι₁, ρ₁, fin.cast_le_mk, fin.eta],
end

def obj₂ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₂+1)) : obj F₁ F₂ e (ι₂ i) = F₂.obj i :=
begin
  dsimp [obj],
  split_ifs with hi,
  { simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hi,
    have hi' : i = 0 := by { ext, exact hi, },
    subst hi',
    exact e, },
  { congr,
    ext,
    simp only [add_tsub_cancel_left, fin.eta], },
end

def obj₂' {n₁ n₂ : ℕ} {D : Type*} [category D] {F₁ : composable_morphisms n₁ D} {F₂ : composable_morphisms n₂ D}
  {e : F₁.right = F₂.left} (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : obj F₁ F₂ e i = F₂.obj (ρ₂ i hi) :=
begin
  rw ← obj₂ F₁ F₂ e,
  congr,
  ext,
  simp only [ι₂, ρ₂, add_tsub_cancel_left, add_lt_add_iff_left, fin.coe_mk, add_comm n₁, nat.sub_add_cancel (le_of_not_ge hi)],
end

def map {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hij : i ≤ j) : obj F₁ F₂ e i ⟶ obj F₁ F₂ e j :=
begin
  by_cases hj : (j : ℕ) ≤ n₁,
  { have hi : (i : ℕ) ≤ n₁ := ((fin.coe_fin_le.mpr hij).trans hj),
    refine eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le _) ≫ eq_to_hom (obj₁' j hj).symm,
    simpa only [subtype.mk_le_mk, fin.coe_fin_le] using hij, },
  by_cases hi : (i : ℕ) ≤ n₁,
  { exact eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (fin.le_last _)) ≫ eq_to_hom e ≫ F₂.map (hom_of_le (fin.zero_le _)) ≫ eq_to_hom (obj₂' j hj).symm, },
  { refine eq_to_hom (obj₂' i hi) ≫ F₂.map (hom_of_le _) ≫ eq_to_hom (obj₂' j hj).symm,
    simp only [ρ₂, subtype.mk_le_mk, tsub_le_iff_right],
    rw nat.sub_add_cancel (le_of_not_ge hj),
    simpa only [fin.coe_fin_le] using hij, },
end

lemma map₁₁' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : (j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (by exact hij)) ≫ eq_to_hom (obj₁' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma hι₁ {n₁ : ℕ} (i : fin (n₁+1)) (n₂ : ℕ) : ((ι₁ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ := i.is_le
lemma hι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : ¬((ι₂ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ :=
begin
  simp only [ι₂, fin.coe_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero],
  intro h,
  apply hi,
  ext,
  exact h,
end

lemma ρ₁ι₁ {n₁ : ℕ} (i : fin (n₁+1)) (n₂ : ℕ) : i = ρ₁ (ι₁ i : fin (n₁+n₂+1)) (hι₁ i n₂) :=
by { ext, refl, }
lemma ρ₂ι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : i = ρ₂ (ι₂ i : fin (n₁+n₂+1)) (hι₂ i hi n₁) :=
begin
  ext,
  simp only [ρ₂, ι₂, fin.coe_mk, add_tsub_cancel_left],
end

lemma map₁₁ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+1)) (hij : (ι₁ i : fin (n₁+n₂+1)) ≤ ι₁ j) : map F₁ F₂ e (ι₁ i) (ι₁ j) hij =
eq_to_hom (obj₁ F₁ F₂ e i) ≫ F₁.map (hom_of_le hij) ≫ eq_to_hom (obj₁ F₁ F₂ e j).symm :=
begin
  have eqi := ρ₁ι₁ i n₁,
  have eqj := ρ₁ι₁ j n₁,
  convert map₁₁' F₁ F₂ e (ι₁ i) (ι₁ j) (hι₁ i n₂) (hι₁ j n₂) hij,
end

lemma map₁₂' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (fin.le_last _)) ≫ eq_to_hom e ≫
  F₂.map (hom_of_le (fin.zero_le _)) ≫ eq_to_hom (obj₂' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma map₂₂' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₂' i hi) ≫ F₂.map (hom_of_le begin
  dsimp [ρ₂],
  simpa only [subtype.mk_le_mk, tsub_le_iff_right, nat.sub_add_cancel (le_of_not_ge hj)] using fin.coe_fin_le.mpr hij,
end) ≫ eq_to_hom (obj₂' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma find_i₂ {n₁ n₂ : ℕ} (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : ∃ (i₂ : fin (n₂+1)), i = ι₂ i₂ :=
begin
  use ρ₂ i hi,
  ext,
  dsimp [ι₂, ρ₂],
  simp only [add_comm n₁, nat.sub_add_cancel (le_of_not_ge hi)],
end

end join

@[simps]
def join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) :
  composable_morphisms (n₁+n₂) D :=
{ obj := join.obj F₁ F₂ e,
  map := λ i j ij, join.map F₁ F₂ e i j (le_of_hom ij),
  map_id' := λ i, begin
    by_cases hi : (i : ℕ) ≤ n₁,
    { erw [join.map₁₁' F₁ F₂ e i i hi hi rfl.le, F₁.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { erw [join.map₂₂' F₁ F₂ e i i hi hi rfl.le, F₂.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
  end,
  map_comp' := λ i j k ij jk, begin
    by_cases hk : (k : ℕ) ≤ n₁,
    { have hj : (j : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp (le_of_hom jk)) hk,
      have hi : (i : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp (le_of_hom ij)) hj,
      erw join.map₁₁' F₁ F₂ e i j hi hj (le_of_hom ij),
      erw join.map₁₁' F₁ F₂ e j k hj hk (le_of_hom jk),
      erw join.map₁₁' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
      slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
      erw id_comp,
      slice_rhs 2 3 { rw ← F₁.map_comp, },
      refl, },
    { by_cases hi : (i : ℕ) ≤ n₁,
      { by_cases hj : (j : ℕ) ≤ n₁,
        { erw join.map₁₁' F₁ F₂ e i j hi hj (le_of_hom ij),
          erw join.map₁₂' F₁ F₂ e j k hj hk (le_of_hom jk),
          erw join.map₁₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
          slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 2 3 { rw ← F₁.map_comp, },
          simpa only [assoc], },
        { erw join.map₁₂' F₁ F₂ e i j hi hj (le_of_hom ij),
          erw join.map₂₂' F₁ F₂ e j k hj hk (le_of_hom jk),
          erw join.map₁₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
          slice_rhs 5 6 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 4 5 { rw ← F₂.map_comp, },
          refl, }, },
      { have hj : ¬(j : ℕ) ≤ n₁,
        { simp only [not_le] at ⊢ hi,
          exact lt_of_lt_of_le hi (le_of_hom ij), },
        erw join.map₂₂' F₁ F₂ e i j hi hj (le_of_hom ij),
        erw join.map₂₂' F₁ F₂ e j k hj hk (le_of_hom jk),
        erw join.map₂₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
        slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
        erw id_comp,
        slice_rhs 2 3 { rw ← F₂.map_comp, },
        refl, }, },

  end }

lemma composition_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) : (join F₁ F₂ e).composition = arrow.composition F₁.composition F₂.composition e :=
begin
  sorry
end

def last_arrow_of_join {n₁ : ℕ} {D : Type*} [category D] (F : composable_morphisms n₁ D) {Y Z : D} (f : Y ⟶ Z) (e : F.right = Y) :
  (F.join (mk_1 f) e).ith_arrow (fin.last _) = arrow.mk f :=
begin
  sorry,
end

lemma i₁th_arrow_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin n₁) : (join F₁ F₂ e).ith_arrow (fin.cast_le le_self_add i) = F₁.ith_arrow i :=
begin
  sorry
end

end composable_morphisms

namespace arrow_class

namespace is_strict_localization

def inv {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (w : W) :
  L.obj w.1.right ⟶ L.obj w.1.left :=
begin
  haveI : is_iso (L.map (w.1.hom)) := hL.inverts_W w,
  exact inv (L.map w.1.hom),
end

@[simp]
def lift_functor_map_Winv {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (w : W) :
  hL.lift_functor.map (localization.Wiso w).inv = hL.inv w :=
begin
  sorry
end

lemma description_arrows {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (f : arrow D) :
  ∃ (n : ℕ) (F : composable_morphisms n D), F.composition = f ∧
  ∀ (i : fin (n)), (∃ g : arrow C, F.ith_arrow i = L.map_arrow.obj g) ∨ (∃ (w : W), F.ith_arrow i = arrow.mk (hL.inv w)) :=
begin
  suffices : ∀ {X Y : paths W.loc_quiver} (φ : X ⟶ Y), 
    ∃ (n : ℕ) (F : composable_morphisms n D), F.composition = (quotient.functor _ ⋙ hL.lift_functor).map_arrow.obj (arrow.mk φ) ∧
    ∀ (i : fin (n)), (∃ g : arrow C, F.ith_arrow i = L.map_arrow.obj g) ∨ (∃ (w : W), F.ith_arrow i = arrow.mk (hL.inv w)),
  { let f' := hL.is_equivalence.inverse.map f.hom,
    have eq : f = hL.lift_functor.map_arrow.obj (arrow.mk f'),
    { dsimp [f'],
      have h := hL.is_isomorphism.2.symm,
      ext,
      { exact functor.congr_map_conjugate h f.hom, },
      { exact functor.congr_obj h f.right, }, },
    cases quotient.functor_map_surj _ _ _ f' with φ hφ,
    rw [eq, ← hφ],
    exact this φ, },
  intros X Y φ,
  induction φ with Y Z φ f hφ,
  { use [0, composable_morphisms.mk_0 ((quotient.functor _ ⋙ hL.lift_functor).obj X)],
    split,
    { refl, },
    { intro i,
      exfalso,
      exact nat.not_lt_zero _ i.is_lt, }, },
  { cases X with X,
    cases Y with Y,
    cases Z with Z,
    let X' : paths W.loc_quiver := ⟨X⟩,
    let Y' : paths W.loc_quiver := ⟨Y⟩,
    let Z' : paths W.loc_quiver := ⟨Z⟩,
    let φ' : X' ⟶ Y' := φ,    
    rcases hφ with ⟨n, F, h₁, h₂⟩,
    cases f with f w,
    work_on_goal 1
    { let h : (_ : W.loc_quiver) ⟶ _ := sum.inl f,
      let F' := F.join (composable_morphisms.mk_1 (L.map f)) (arrow.congr_right h₁), },
    work_on_goal 2
    { let h : (_ : W.loc_quiver) ⟶ _ := sum.inr w,
      let F' := F.join (composable_morphisms.mk_1 (hL.inv ⟨arrow.mk w.1, w.2⟩)) (arrow.congr_right h₁), },
    all_goals
    { use [n+1, F'],
      split,
      work_on_goal 2 
      { intro i,
        by_cases hi : i = fin.last _, swap,
        { let i' : fin n := ⟨(i : ℕ), _⟩, swap,
          { by_contradiction,
            apply hi,
            ext,
            exact le_antisymm i.is_le (not_lt.mp h), },
          have eqF : F'.ith_arrow i = F.ith_arrow i' := begin
            convert composable_morphisms.i₁th_arrow_of_join _ _ _ i',
            ext,
            refl,
          end,
          erw eqF,
          exact h₂ i', }, },
        work_on_goal 2 { rw hi, erw composable_morphisms.last_arrow_of_join, }, },
      work_on_goal 2
      { apply or.inl,
        use arrow.mk f,
        ext,
        { erw [id_comp, comp_id], refl, },
        { refl, },
        { refl, }, },
      work_on_goal 3
      { apply or.inr,
        use ⟨_, w.2⟩, },
      all_goals
      { simp only [← show φ' ≫ paths.of.map h = φ.cons h, by refl, arrow.map_arrow_comp,
          composable_morphisms.composition_of_join, h₁],
        congr,
        simp only [composable_morphisms.mk_1_composition, arrow.map_arrow_of_mk], },
      { simp only [functor.congr_map_conjugate hL.lift_functor_fac.symm f,
          arrow.mk_eq_to_hom_comp, arrow.mk_comp_eq_to_hom, functor.comp_map, localization.Q_map_eq, localization.ψ₁,
          arrow.mk_hom], },
      { simp only [functor.comp_map],
        dsimp only [h],
        rw [← hL.lift_functor_map_Winv, ← localization.Wiso_inv_eq],
        simp only [localization.ψ₂, localization.ψ₂', arrow.mk_hom, subtype.val_eq_coe, subtype.coe_eta], }, },
end

end is_strict_localization

end arrow_class

end category_theory
