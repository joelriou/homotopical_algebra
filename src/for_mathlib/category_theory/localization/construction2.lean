/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.localization.construction
import for_mathlib.category_theory.morphism_property_misc

noncomputable theory

open category_theory category_theory.category

variables {C : Type*} [category C] (W : morphism_property C)
variables {D : Type*} [category D]

namespace category_theory

variables (D)

@[derive category]
def morphism_property.functors_inverting := full_subcategory (λ (F : C ⥤ D), W.is_inverted_by F)

variables {D W}

def morphism_property.functors_inverting.mk (F : C ⥤ D) (hF : W.is_inverted_by F) :
  W.functors_inverting D := ⟨F, hF⟩

variables (D W)
namespace morphism_property

lemma Q_inverts : W.is_inverted_by W.Q :=
λ X Y w hw, is_iso.of_iso (localization.construction.Wiso w hw)

end morphism_property

namespace localization

namespace construction

lemma nat_trans_hcomp_injective {F G : W.localization ⥤ D} (τ₁ τ₂ : F ⟶ G)
  (h : 𝟙 W.Q ◫ τ₁ = 𝟙 W.Q ◫ τ₂) : τ₁ = τ₂ :=
begin
  ext X,
  have eq := (obj_equiv W).right_inv X,
  simp only [obj_equiv] at eq,
  rw [← eq, ← nat_trans.id_hcomp_app, ← nat_trans.id_hcomp_app, h],
end

namespace whiskering_left_equivalence

@[simps]
def functor : (W.localization ⥤ D) ⥤ (W.functors_inverting D) :=
full_subcategory.lift _ ((whiskering_left _ _ D).obj W.Q)
  (λ F, morphism_property.is_inverted_by.of_comp W W.Q W.Q_inverts _)

@[simps]
def inverse : (W.functors_inverting D) ⥤ (W.localization ⥤ D) :=
{ obj := λ G, lift G.obj G.property,
  map := λ G₁ G₂ τ, nat_trans_extension (eq_to_hom (by rw fac) ≫ τ ≫ eq_to_hom (by rw fac)),
  map_id' := λ G, nat_trans_hcomp_injective _ _ _ _ begin
    rw nat_trans_extension_hcomp,
    ext X,
    simpa only [nat_trans.comp_app, eq_to_hom_app, eq_to_hom_refl, comp_id, id_comp,
      nat_trans.hcomp_id_app, nat_trans.id_app, functor.map_id],
  end,
  map_comp' := λ G₁ G₂ G₃ τ₁ τ₂, nat_trans_hcomp_injective _ _ _ _ begin
    ext X,
    simpa only [nat_trans_extension_hcomp, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_refl,
      id_comp, comp_id, nat_trans.hcomp_app, nat_trans.id_app, functor.map_id,
      nat_trans_extension_app, nat_trans_extension.app_eq],
  end, }

@[simps]
lemma unit_iso : 𝟭 (W.localization ⥤ D) ≅ functor W D ⋙ inverse W D := eq_to_iso
begin
  refine functor.ext (λ G, _) (λ G₁ G₂ τ, _),
  { apply uniq,
    dsimp [functor],
    rw fac, },
  { apply nat_trans_hcomp_injective,
    ext X,
    simp only [functor.id_map, nat_trans.hcomp_app, comp_id, functor.comp_map,
      inverse_map, nat_trans.comp_app, eq_to_hom_app, eq_to_hom_refl, nat_trans_extension_app,
      nat_trans_extension.app_eq, functor_map_app, id_comp], },
end

@[simps]
lemma counit_iso : inverse W D ⋙ functor W D ≅ 𝟭 (W.functors_inverting D) := eq_to_iso
begin
  refine functor.ext _ _,
  { rintro ⟨G, hG⟩,
    ext1,
    apply fac, },
  { rintros ⟨G₁, hG₁⟩ ⟨G₂, hG₂⟩ f,
    ext X,
    apply nat_trans_extension.app_eq, },
end

end whiskering_left_equivalence

def whiskering_left_equivalence : (W.localization ⥤ D) ≌ W.functors_inverting D :=
{ functor := whiskering_left_equivalence.functor W D,
  inverse := whiskering_left_equivalence.inverse W D,
  unit_iso := whiskering_left_equivalence.unit_iso W D,
  counit_iso := whiskering_left_equivalence.counit_iso W D,
  functor_unit_iso_comp' := λ F, begin
    ext X,
    simpa only [eq_to_hom_app, whiskering_left_equivalence.unit_iso_hom,
      whiskering_left_equivalence.counit_iso_hom, eq_to_hom_map, eq_to_hom_trans,
      eq_to_hom_refl],
  end, }

end construction

end localization

end category_theory
