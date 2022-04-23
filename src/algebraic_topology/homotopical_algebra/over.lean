/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.model_category
import category_theory.limits.comma

universes v u

noncomputable theory

namespace category_theory

namespace limits

variables {C : Type u} [category.{v} C]
variables {J : Type v} [category J]

@[simp]
def under.nat_trans {X : C} (F : J ⥤ under X) : (functor.const J).obj X ⟶ F ⋙ under.forget X :=
nat_trans.hcomp (𝟙 F) (comma.nat_trans _ _)

@[simp]
def under.arrow₁ {X : C} (F : J ⥤ under X) [has_colimit (F ⋙ under.forget _)]
  [has_colimit ((functor.const J).obj X)] : colimit ((functor.const J).obj X) ⟶ colimit (F ⋙ under.forget _) :=
colim_map (under.nat_trans F)

@[simp]
def under.arrow₂ {X : C} (F : J ⥤ under X) [has_colimit ((functor.const J).obj X)] :
  colimit ((functor.const J).obj X) ⟶ X := colimit.desc _ (cocone.mk X (𝟙 _))

def under.cocone {X : C} (F : J ⥤ under X) [has_colimit (F ⋙ under.forget _)]
  [has_colimit ((functor.const J).obj X)] [has_pushout (under.arrow₁ F) (under.arrow₂ F)] : cocone F :=
begin
  apply cocone.mk (under.mk (pushout.inr : X ⟶ pushout (under.arrow₁ F) (under.arrow₂ F))),
  exact
  { app := λ j, under.hom_mk ((colimit.ι (F ⋙ under.forget X) j) ≫ pushout.inl) begin
      dsimp,
      have eq : (F.obj j).hom = (under.nat_trans F).app j := (category.comp_id _).symm,
      erw [eq, ← category.assoc, ← ι_colim_map, category.assoc, pushout.condition, ← category.assoc,
        colimit.ι_desc, nat_trans.id_app, category.id_comp],
    end,
    naturality' := λ j j' f, begin
      ext,
      simp only [category.assoc, under.comp_right, under.hom_mk_right, functor.const.obj_map],
      erw [category.comp_id, ← category.assoc],
      congr,
      convert colimit.w _ f,
      refl,
    end },
end

def under.colimit_cocone {X : C} (F : J ⥤ under X) [has_colimit (F ⋙ under.forget _)]
  [has_colimit ((functor.const J).obj X)] [has_pushout (under.arrow₁ F) (under.arrow₂ F)] : colimit_cocone F := sorry

instance under.has_colimit {X : C} (F : J ⥤ under X) [has_colimit (F ⋙ under.forget _)]
  [has_colimit ((functor.const J).obj X)] [has_pushout (under.arrow₁ F) (under.arrow₂ F)] : has_colimit F :=
⟨nonempty.intro (under.colimit_cocone F)⟩

lemma under.has_colimits_of_shape (X : C) [has_colimits_of_shape J C] [has_pushouts C] :
  has_colimits_of_shape J (under X) := {}

end limits

end category_theory

open category_theory

namespace algebraic_topology

namespace model_category

def under (M : model_category) (X : M.C) : model_category :=
{ C := under X,
  fib_cof_we :=
  { W := M.W.inverse_image (under.forget _),
    cof := M.cof.inverse_image (under.forget _),
    fib := M.fib.inverse_image (under.forget _), },
  CM1 := begin
    split,
    { constructor,
      intros J hJ hJ',
      haveI := M.CM1.1,
      apply comma.has_limits_of_shape, },
    { constructor,
      intros J hJ hJ',
      haveI := M.CM1.2,
      apply limits.under.has_colimits_of_shape, },
  end,
  CM2 := M.CM2.inverse_image (under.forget _),
  CM3 :=
  { W := M.CM3.W.inverse_image (under.forget _),
    cof := M.CM3.cof.inverse_image (under.forget _),
    fib := M.CM3.fib.inverse_image (under.forget _), },
  CM4 := ⟨M.CM4a.under X, M.CM4b.under X⟩,
  CM5 := ⟨M.CM5a.under X, M.CM5b.under X⟩, }

end model_category

end algebraic_topology

