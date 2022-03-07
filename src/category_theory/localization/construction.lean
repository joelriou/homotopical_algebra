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

universes v v' u u'

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]

namespace arrow

def is_inverted_by (f : arrow C) (F : C ⥤ D) : Prop := is_iso (F.map f.hom)

end arrow

namespace arrow_class

def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : W), f.1.is_inverted_by F

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

/-- to be moved somewhere else -/
lemma congr_obj {D₁ D₂ : Type*} [category D₁] [category D₂] {F G : D₁ ⥤ D₂}
(h : F = G) : ∀ X : D₁, F.obj X = G.obj X :=
by { intro X, rw h, }

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

/- end of block -/

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
      convert congr_map_conjugate h' f, },
    { rintro ⟨⟨X⟩⟩,
      convert congr_obj h X, }, },
  { apply paths.ext_functor,
    { rintro ⟨X⟩ ⟨Y⟩ f,
      cases f,
      { convert congr_map_conjugate h f, },
      { rcases f with ⟨g, hg⟩,
        dsimp at g hg,
        have hα : (Wiso ⟨arrow.mk g, hg⟩).hom = (Q W).map g := rfl,
        have h' := congr_map_conjugate h g,
        simp only [functor.comp_map, ← hα] at h',
        refine conjugate_inv_of_congr_map_conjugate G₁ G₂ _ _ _ h',
        { convert congr_obj h Y, },
        { convert congr_obj h X, }, }, },
    { ext X,
      cases X,
      have eq := congr_obj h X,
      dsimp at ⊢ eq,
      convert eq, }, },
end

instance (w : W) : is_iso ((Q W).map w.1.hom) := is_iso.of_iso (Wiso w)

end localization

variable (L : C ⥤ D)

structure is_localization (W : arrow_class C) (L : C ⥤ D) :=
(inverts_W : W.is_inverted_by L)
(is_equivalence : is_equivalence (localization.lift L inverts_W))

structure is_strict_localization (W : arrow_class C) (L : C ⥤ D) extends is_localization W L :=
(is_isomorphism : (localization.lift L inverts_W ⋙ is_equivalence.inverse).obj = id
  ∧ (is_equivalence.inverse ⋙ localization.lift L inverts_W).obj = id)

end arrow_class

end category_theory
