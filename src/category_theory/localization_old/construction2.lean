/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.quotient
import category_theory.path_category
import category_theory.category.Quiv
import category_theory.equivalence
import category_theory.nerve

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

lemma congr_inv_of_congr_hom {D₁ D₂ : Type*} [category D₁] [category D₂] (F G : D₁ ⥤ D₂)
  {X Y : D₁} (e : X ≅ Y) (hX : F.obj X = G.obj X) (hY : F.obj Y = G.obj Y)
  (h₂ : F.map e.hom = eq_to_hom (by rw hX) ≫ G.map e.hom ≫ eq_to_hom (by rw hY)) :
F.map e.inv = eq_to_hom (by rw hY) ≫ G.map e.inv ≫ eq_to_hom (by rw hX) :=
by simp only [← is_iso.iso.inv_hom e, functor.map_inv, h₂, is_iso.inv_comp, inv_eq_to_hom, category.assoc]

lemma congr_map {D D' : Type*} [category D] [category D'] (F : D ⥤ D')
{X Y : D} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g :=
by { subst h, }

end functor

universes v v' v'' u u' u''

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]
variables {E : Type u''} [category.{v''} E]

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

namespace localization

def ι (X : C) : paths (loc_quiver W) := ⟨X⟩

@[simp]
def ψ₁' {X Y : paths (loc_quiver W)} (f : X.obj ⟶ Y.obj) : X ⟶ Y := paths.of.map (sum.inl f)
@[simp]
def ψ₁ {X Y : C} (f : X ⟶ Y) : ι W X ⟶ ι W Y := paths.of.map (sum.inl f)
@[simp]
def ψ₂' {X Y : paths (loc_quiver W)} (w : X.obj ⟶ Y.obj) (hw : arrow.mk w ∈ W) : Y ⟶ X := paths.of.map (sum.inr ⟨w, hw⟩)
@[simp]
def ψ₂ {X Y : C} (w : X ⟶ Y) (hw : arrow.mk w ∈ W) : ι W Y ⟶ ι W X := ψ₂' W w hw

inductive relations ⦃X Y : (paths (loc_quiver W))⦄ : (X ⟶ Y) → (X ⟶ Y) → Prop
| id (φ : X ⟶ Y) : relations (ψ₁' W (𝟙 X.obj) ≫ φ) φ
| comp {Z : paths (loc_quiver W)} (f : X.obj ⟶ Z.obj) (g : Z.obj ⟶ Y.obj) : relations (ψ₁' W (f ≫ g)) (ψ₁' W f ≫ ψ₁' W g)
| Winv₁ {Z : paths (loc_quiver W)} (w : X.obj ⟶ Z.obj) (hw : arrow.mk w ∈ W) (φ : X ⟶ Y) : relations (ψ₁' W w ≫ ψ₂' W w hw ≫ φ) φ
| Winv₂ {Z : paths (loc_quiver W)} (w : Z.obj ⟶ Y.obj) (hw : arrow.mk w ∈ W) (φ : X ⟶ Y) : relations (φ ≫ ψ₂' W w hw ≫ ψ₁' W w) φ

end localization

@[derive category]
def localization := category_theory.quotient (localization.relations W)

open localization

namespace localization

variable (W)

def Q : C ⥤ W.localization :=
{ obj := λ X, (quotient.functor _).obj (paths.of.obj ⟨X⟩),
  map := λ X Y f, (quotient.functor _).map (ψ₁ W f),
  map_id' := λ X, by convert quotient.sound _ (@relations.id _ _ W (paths.of.obj ⟨X⟩) _ (𝟙 _)),
  map_comp' := λ X Z Y f g, quotient.sound _
    (@relations.comp _ _ W (paths.of.obj ⟨X⟩) (paths.of.obj ⟨Y⟩) (paths.of.obj ⟨Z⟩) f g), }

variable {W}

def Wiso {X Y : C} (w : X ⟶ Y) (hw : arrow.mk w ∈ W) : iso ((Q W).obj X) ((Q W).obj Y) :=
{ hom := (Q W).map w,
  inv := (quotient.functor _).map (paths.of.map (sum.inr ⟨w, hw⟩)),
  hom_inv_id' := quotient.sound _ (@relations.Winv₁ _ _ W
    (paths.of.obj ⟨X⟩) _ (paths.of.obj ⟨Y⟩) w hw (𝟙 _)),
  inv_hom_id' := quotient.sound _ (@relations.Winv₂ _ _ W
    (paths.of.obj ⟨Y⟩) (paths.of.obj ⟨Y⟩) (paths.of.obj ⟨X⟩) w hw (𝟙 _)), }

def Wiso' (w : W) : iso ((Q W).obj w.1.left) ((Q W).obj w.1.right) :=
Wiso w.1.hom (by { rw arrow.mk_eq w.1, exact w.2, })


--lemma Wiso_inv_eq {X Y : C} (w : X ⟶ Y) (hw : arrow.mk w ∈ W) : (quotient.functor (relations W)).map (ψ₂ w) = (Wiso w).inv := by refl

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

lemma W_is_inverted_by_Q : W.is_inverted_by (Q W) := λ w, is_iso.of_iso (Wiso' w)

def lift {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  localization W ⥤ D :=
begin
  apply quotient.lift (relations W) (lift_to_path_category G hG),
  rintro ⟨X⟩ ⟨Y⟩ f₁ f₂ r,
  rcases r with (_|⟨⟨Z⟩, f, g⟩|⟨⟨Z⟩, w, hw⟩|⟨⟨Z⟩, w, hw⟩),
  tidy,
end
/-
  { dsimp,
    simp only [prefunctor.map_path_comp, prefunctor.map_path_comp', compose_path_comp],
    dsimp,
    simp only [functor.map_id, id_comp], },
  { dsimp,
    simp only [functor.map_comp, id_comp], },
  { dsimp,
    simp only [prefunctor.map_path_comp, prefunctor.map_path_comp', compose_path_comp],
    dsimp,
    simp only [id_comp, is_iso.hom_inv_id_assoc], },
  { dsimp,
    simp only [assoc, is_iso.inv_hom_id, comp_id], }, -/

@[simp]
lemma fac {D : Type u'} [category.{v'} D] (G : C ⥤ D) (hG : W.is_inverted_by G) :
  Q W ⋙ lift G hG = G :=
begin
  apply functor.ext,
  { intros X Y f,
    simp only [functor.comp_map, eq_to_hom_refl, comp_id, id_comp],
    dsimp [lift, lift_to_path_category, Q],
    rw id_comp, },
  { intro X,
    refl, }
end

lemma uniq {D : Type*} [category D] (G₁ G₂ : localization W ⥤ D) (h : Q W ⋙ G₁ = Q W ⋙ G₂) : G₁ = G₂ :=
begin
  suffices h' : (quotient.functor (relations W)) ⋙ G₁ = (quotient.functor (relations W)) ⋙ G₂,
  { apply functor.ext,
    { rintros ⟨⟨X⟩⟩ ⟨⟨Y⟩⟩ ⟨f⟩,
      convert functor.congr_hom h' f, },
    { rintro ⟨⟨X⟩⟩,
      convert functor.congr_obj h X, }, },
  { apply paths.ext_functor,
    { rintro ⟨X⟩ ⟨Y⟩ f,
      cases f,
      { convert functor.congr_hom h f, },
      { rcases f with ⟨w, hw⟩,
        dsimp at w,
        have hα : (Wiso w hw).hom = (Q W).map w := rfl,
        have h' := functor.congr_hom h w,
        simp only [functor.comp_map, ← hα] at h',
        refine functor.congr_inv_of_congr_hom G₁ G₂ _ _ _ h',
        { convert functor.congr_obj h Y, },
        { convert functor.congr_obj h X, }, }, },
    { ext X,
      cases X,
      have eq := functor.congr_obj h X,
      exact eq, }, }
end
#exit

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
(W : arrow_class C) (F : C ⥤ D)  (E : Type u'') [category.{v''} E] :=
  (inverts_W : W.is_inverted_by F)
  (lift : Π (G : C ⥤ E) (hG : W.is_inverted_by G), D ⥤ E)
  (fac : ∀ (G : C ⥤ E) (hG : W.is_inverted_by G), F ⋙ lift G hG = G)
  (uniq : ∀ (G₁ G₂ : D ⥤ E), F ⋙ G₁ = F ⋙ G₂ → G₁ = G₂)

namespace localization

def universal_property {E : Type u''} [category.{v''} E] :
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

end is_strict_localization

end arrow_class

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
  dsimp only [inv],
  have h := functor.map_inv hL.lift_functor ((localization.Wiso w).hom),
  rw is_iso.iso.inv_hom at h,
  convert h,
  erw [functor.congr_hom hL.lift_functor_fac.symm w.1.hom, comp_id, id_comp],
  refl,
end

lemma description_arrows {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L) (f : arrow D) :
  ∃ (n : ℕ) (F : composable_morphisms n D), F.arrow = f ∧
  ∀ (i : fin (n)), (∃ g : arrow C, F.ith_arrow i = L.map_arrow.obj g) ∨ (∃ (w : W), F.ith_arrow i = arrow.mk (hL.inv w)) :=
begin
  suffices : ∀ {X Y : paths W.loc_quiver} (φ : X ⟶ Y), 
    ∃ (n : ℕ) (F : composable_morphisms n D), F.arrow = (quotient.functor _ ⋙ hL.lift_functor).map_arrow.obj (arrow.mk φ) ∧
    ∀ (i : fin (n)), (∃ g : arrow C, F.ith_arrow i = L.map_arrow.obj g) ∨ (∃ (w : W), F.ith_arrow i = arrow.mk (hL.inv w)),
  { let f' := hL.is_equivalence.inverse.map f.hom,
    have eq : f = hL.lift_functor.map_arrow.obj (arrow.mk f'),
    { dsimp [f'],
      have h := hL.is_isomorphism.2.symm,
      ext,
      { exact functor.congr_hom h f.hom, }, },
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
        work_on_goal 2
        { erw [hi, ← composable_morphisms.last_arrow, composable_morphisms.last_arrow_of_join], }, },
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
          composable_morphisms.arrow_of_join, h₁],
        congr,
        simp only [composable_morphisms.mk_1_arrow, arrow.map_arrow_of_mk], },
      { simp only [functor.congr_hom hL.lift_functor_fac.symm f,
          arrow.mk_eq_to_hom_comp, arrow.mk_comp_eq_to_hom, functor.comp_map, localization.Q_map_eq, localization.ψ₁,
          arrow.mk_hom], },
      { simp only [functor.comp_map],
        dsimp only [h],
        rw [← hL.lift_functor_map_Winv, ← localization.Wiso_inv_eq],
        simp only [localization.ψ₂, localization.ψ₂', arrow.mk_hom, subtype.val_eq_coe, subtype.coe_eta], }, },
end

lemma arrow_class_is_univ {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L)
  (A : arrow_class D)
  (hA₁ : ∀ (f : arrow C), L.map_arrow.obj f ∈ A)
  (hA₂ : ∀ (w : W), arrow.mk (hL.inv w) ∈ A)
  (hA₃ : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : arrow.mk f ∈ A) (hg : arrow.mk g ∈ A),
    arrow.mk (f ≫ g) ∈ A) :
  A = set.univ :=
begin
  ext f,
  split,
  { intro h,
    exact set.mem_univ _, },
  { intro h,
    rcases hL.description_arrows f with ⟨n, F, hF₁, hF₂⟩,
    suffices H : ∀ (k : ℕ) (hk : k < n+1),
      arrow.mk (F.map_of_le (show (0 : fin (n+1)) ≤ ⟨k, hk⟩, by exact fin.zero_le _)) ∈ A,
    { simpa only [← hF₁] using H n (lt_add_one _), },
    intro k,
    induction k with k hk,
    { intro H,
      erw [F.map_of_le_eq_id, ← hL.obj_bijection.right_inv (F.ith_object 0)],
      convert hA₁ (arrow.mk (𝟙 _)),
      erw L.map_id,
      refl, },
    { intro hk',
      let hk'' : k < n+1 := lt_trans (lt_add_one _) hk',
      have ineg₁ := fin.zero_le ⟨k, hk''⟩,
      have ineg₂ : (⟨k, hk''⟩ : fin(n+1)) ≤ ⟨k+1, hk'⟩ :=
        by simp only [subtype.mk_le_mk, le_add_iff_nonneg_right, zero_le_one],
      rw F.map_of_le_trans ineg₁ ineg₂,
      apply hA₃,
      { exact hk hk'', },
      { rcases hF₂ ⟨k, by simpa only [nat.succ_eq_add_one, add_lt_add_iff_right] using hk'⟩
          with (⟨g, hg⟩|⟨w, hw⟩),
        { simpa only [← hg] using hA₁ g, },
        { simpa only [← hw] using hA₂ w, }, }, }, }
end

lemma arrow_class_is_univ' {W : arrow_class C} {L : C ⥤ D} (hL : is_strict_localization W L)
  (A : arrow_class D)
  (hA₁ : ∀ {X Y : C} (f : X ⟶ Y), arrow.mk (L.map f) ∈ A)
  (hA₂ : ∀ {X Y : D} (e : X ≅ Y), arrow.mk e.hom ∈ A → arrow.mk e.inv ∈ A)
  (hA₃ : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : arrow.mk f ∈ A) (hg : arrow.mk g ∈ A),
  arrow.mk (f ≫ g) ∈ A) : A = set.univ :=
begin
  apply hL.arrow_class_is_univ,
  { intro f,
    exact hA₁ f.hom, },
  { intro w,
    haveI : is_iso (L.map (w.1.hom)) := hL.inverts_W w,
    apply hA₂ (as_iso (L.map (w.1.hom))),
    exact hA₁ w.1.hom, },
  { intros X Y Z,
    exact hA₃, },
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
  have h := arrow_class_is_univ' hL (naturality_condition (nat_trans_extension.app hL τ)) _
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

end category_theory
