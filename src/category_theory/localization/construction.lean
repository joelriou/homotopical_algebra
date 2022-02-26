/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.basic
import category_theory.arrow_class
import category_theory.quotient
import category_theory.path_category
import category_theory.category.Quiv

open category_theory
open category_theory.category

namespace category_theory

universes v v' u u'

variables {C : Type u} [category.{v} C] (W : arrow_class C)

namespace localization

lemma arrow_mk (f : arrow C) : arrow.mk f.hom = f :=
by { cases f, dsimp [arrow.mk], refl, }

include W

structure preloc := (as : C)

instance : quiver (preloc W) :=
{ hom := λ A B,  (A.as ⟶ B.as) ⊕ { f : B.as ⟶ A.as // arrow.mk f ∈ W} }

omit W

def R₁ := Σ (T : C × C × C), (T.1 ⟶ T.2.1) × (T.2.1 ⟶ T.2.2)
def R₂ := Σ (T : C × C), { f : T.1 ⟶ T.2 // arrow.mk f ∈ W }
def R₃ := R₂ W

def ρ₁ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : R₁ := ⟨⟨X, ⟨Y, Z⟩⟩, ⟨f, g⟩⟩

def F := Σ (D : paths (preloc W) × paths (preloc W)), (D.1 ⟶ D.2) × (D.1 ⟶ D.2)

def φ (X : C) : paths (preloc W) := paths.of.obj { as := X }
def ψ₁ (f : arrow C) : φ W f.left ⟶ φ W f.right := paths.of.map (sum.inl f.hom)
def ψ₂' (g : arrow C) (hg : g ∈ W) : φ W g.right ⟶ φ W g.left := paths.of.map (sum.inr ⟨g.hom, (by { convert hg, rw arrow_mk, })⟩)
def ψ₂ (w : W) : φ W w.1.right ⟶ φ W w.1.left :=
paths.of.map (sum.inr ⟨w.1.hom, (by { convert w.2, rw arrow_mk, })⟩)

def relations₀ : C → F W := by { intro X, exact ⟨⟨⟨X⟩, ⟨X⟩⟩, ⟨ψ₁ W (arrow.mk (𝟙 _)), 𝟙 _⟩⟩, }
def relations₁ : R₁ → F W :=
by { rintro ⟨⟨X,⟨Y,Z⟩⟩, ⟨f,g⟩⟩, exact ⟨⟨⟨X⟩, ⟨Z⟩⟩, ⟨ψ₁ W (arrow.mk (f ≫ g)), ψ₁ W (arrow.mk f) ≫ ψ₁ W (arrow.mk g)⟩⟩, }
def relations₂ (w : W) : F W :=
by { refine ⟨⟨⟨w.1.left⟩, ⟨w.1.left⟩⟩ , ψ₁ W w.1 ≫ ψ₂ W w, 𝟙 _⟩, }
def relations₃ (w : W) : F W :=
by { refine ⟨⟨⟨w.1.right⟩, ⟨w.1.right⟩⟩ , ψ₂ W w ≫ ψ₁ W w.1, 𝟙 _⟩, }

variable {W}
def belongs_to {A B : paths (preloc W)} (f g : A ⟶ B) {D : Type*} (relations : D → F W) : Prop :=
∃ (r : D), relations r = ⟨⟨A, B⟩, ⟨f, g⟩⟩

variable (W)
def relations : hom_rel (paths (preloc W)) :=
λ X Y f g, belongs_to f g (relations₀ W) ∨ belongs_to f g (relations₁ W) ∨
  belongs_to f g (relations₂ W) ∨ belongs_to f g (relations₃ W)

end localization

variable (W)

def localization : Type u := category_theory.quotient (localization.relations W)

instance : category (localization W) :=
(infer_instance : category (category_theory.quotient (localization.relations W)))

namespace localization

def Q : C ⥤ localization W :=
{ obj := λ X, (quotient.functor (relations W)).obj (φ W X),
  map := λ X Y f, (quotient.functor (relations W)).map (ψ₁ W f),
  map_id' := λ X, begin
    apply quotient.sound (relations W),
    exact or.inl ⟨X, rfl⟩,
  end,
  map_comp' := λ X Y Z f g, begin
    apply quotient.sound (relations W),
    exact or.inr (or.inl (⟨ρ₁ f g, rfl⟩)),
  end }

variable {W}

def Wiso (w : W) : iso ((Q W).obj w.1.left) ((Q W).obj w.1.right) :=
{ hom := (Q W).map w.1.hom,
  inv := (quotient.functor (relations W)).map (paths.of.map
    (sum.inr ⟨w.1.hom, (by { convert w.2, rw arrow_mk, })⟩)),
  hom_inv_id' := begin
    erw ← (quotient.functor (relations W)).map_comp (ψ₁ W w.1) (ψ₂ W w),
    apply quotient.sound (relations W),
    refine or.inr (or.inr (or.inl ⟨w, rfl⟩)),
  end,
  inv_hom_id' := begin
    erw ← (quotient.functor (relations W)).map_comp (ψ₂ W w) (ψ₁ W w.1),
    apply quotient.sound (relations W),
    exact or.inr (or.inr (or.inr ⟨w, rfl⟩)),
  end }

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

noncomputable def lift_quiver {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  prefunctor (preloc W) D :=
{ obj := by { rintro ⟨X⟩, exact G.obj X, },
  map := begin
    rintros ⟨X⟩ ⟨Y⟩ (f|⟨g, hg⟩),
    { exact G.map f, },
    { haveI : is_iso (G.map g) := hG ⟨arrow.mk g, hg⟩,
      exact inv (G.map g), },
  end }

/-- Fix category_theory.theory.Quiv.lean-/
noncomputable def functor_quiver {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  paths (preloc W) ⥤ D :=
{ obj := λ X, (lift_quiver G hG).obj X,
  map := λ X Y f, compose_path ((lift_quiver G hG).map_path f), }

@[simp]
lemma lift_quiver_map_ψ₁ {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G)
  (f : arrow C) : (functor_quiver G hG).map (ψ₁ W f) = G.map f.hom :=
by { dsimp [functor_quiver, ψ₁, quiver.hom.to_path], simpa only [id_comp], }

@[simp]
lemma lift_quiver_map_ψ₂ {D : Type*} [category D] (G : C ⥤ D) (hG : W.is_inverted_by G)
  (w : W) : (functor_quiver G hG).map (ψ₂ W w) = 
  (by { haveI : is_iso (G.map w.1.hom) := hG w, exact inv (G.map w.1.hom), }) :=
by { dsimp [functor_quiver, ψ₂, quiver.hom.to_path, lift_quiver], simpa only [id_comp], }

noncomputable def lift {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  localization W ⥤ D :=
begin
  apply quotient.lift (relations W) (functor_quiver G hG),
  { rintro ⟨X⟩ ⟨Y⟩ f f' r,
    rcases r with (_|_|_|_),
    { rcases r with ⟨X', r⟩,
      have eq₁ := congr_arg sigma.fst r,
      have eqX : X = X' := congr_arg preloc.as (prod.mk.inj eq₁).1.symm,
      have eqY : X' = Y := congr_arg preloc.as (prod.mk.inj eq₁).2,
      substs eqX eqY,
      have eq₂ := eq_of_heq (sigma.mk.inj r).2,
      rw [← (prod.mk.inj eq₂).1, ← (prod.mk.inj eq₂).2],
      simp only [lift_quiver_map_ψ₁, functor.map_id, arrow.mk_hom],
      exact G.map_id X, },
    { rcases r with ⟨⟨⟨X', ⟨Z, Y'⟩⟩, ⟨g, g'⟩⟩, r⟩,
      have eq₁ := congr_arg sigma.fst r,
      have eqX : X = X' := congr_arg preloc.as (prod.mk.inj eq₁).1.symm,
      have eqY : Y = Y' := congr_arg preloc.as (prod.mk.inj eq₁).2.symm,
      substs eqX eqY,
      have eq₂ := eq_of_heq (sigma.mk.inj r).2,
      rw [← (prod.mk.inj eq₂).1, ← (prod.mk.inj eq₂).2, functor.map_comp],
      simpa only [lift_quiver_map_ψ₁, ← G.map_comp], },
    { rcases r with ⟨w, r⟩,
      have eq₁ := congr_arg sigma.fst r,
      have eqX : w.1.left = X := congr_arg preloc.as (prod.mk.inj eq₁).1,
      have eqY : w.1.left = Y := congr_arg preloc.as (prod.mk.inj eq₁).2,
      substs eqX eqY,
      have eq₂ := eq_of_heq (sigma.mk.inj r).2,
      rw [← (prod.mk.inj eq₂).1, ← (prod.mk.inj eq₂).2],
      simp only [functor.map_comp, functor.map_id, lift_quiver_map_ψ₁, lift_quiver_map_ψ₂,
        is_iso.hom_inv_id], },
    { rcases r with ⟨⟨g, hg⟩, r⟩,
      have eq₁ := congr_arg sigma.fst r,
      have eqX : g.right = X := congr_arg preloc.as (prod.mk.inj eq₁).1,
      have eqY : g.right = Y := congr_arg preloc.as (prod.mk.inj eq₁).2,
      substs eqX eqY,
      have eq₂ := eq_of_heq (sigma.mk.inj r).2,
      rw [← (prod.mk.inj eq₂).1, ← (prod.mk.inj eq₂).2],
      simp only [functor.map_comp, functor.map_id, lift_quiver_map_ψ₁, lift_quiver_map_ψ₂,
        is_iso.inv_hom_id], }, },
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

noncomputable
def localisation_is_localisation : is_localization (Q W) W :=
{ inverts_W := λ w, is_iso.of_iso (Wiso w),
  lift := begin
    intro D,
    introI,
    intros G hG,
    exact lift G hG,
  end,
  fac := begin
    intro D,
    introI,
    intros G hG,
    apply functor.ext,
    { intros X Y f,
      dsimp [lift, functor_quiver, lift_quiver, Q, ψ₁, quiver.hom.to_path],
      erw [id_comp, comp_id, id_comp],
      refl, },
    { intro X,
      refl, }
  end,
  uniq := λ D, by { introI, exact uniq, } }

instance (w : W) : is_iso ((Q W).map w.1.hom) := is_iso.of_iso (Wiso w)

end localization

end category_theory
