import for_mathlib.category_theory.lifting_properties.continuous_functor
import for_mathlib.category_theory.retracts

universes w v u

namespace category_theory

open limits

namespace morphism_property

variables {C : Type u} [category.{v} C] (I : morphism_property C)

def pushouts : morphism_property C :=
λ X Y f, ∃ (A B : C) (i : A ⟶ B) (hi : I i) (g : A ⟶ X) (g' : B ⟶ Y),
  is_pushout i g g' f

#exit
inductive transfinite_composition : morphism_property C
| transfinite {α : Type v} [linear_order α] [is_well_order α (<)] [order_bot α]
  (F : α ⥤ C) (hF₁ : F.well_order_continuous)
  (hF₂ : ∀ (a : α) (ha : ∃ (b : α), a < b), I (F.map (hom_of_le (le_succ a)))) (c : cocone F)
  (hc : is_colimit c) : transfinite_composition (c.ι.app ⊥)

def cell := I.pushouts.transfinite_composition

def cof : morphism_property C :=
λ X Y c, ∃ (Z : C) (r : X ⟶ Z) (hr : I.cell r), is_retract (under.mk c) (under.mk r)

@[protected]
structure is_set (W : morphism_property C) :=
(S : Type w)
(σ : S → arrow C)
(iff : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ ∃ (s : S), nonempty (arrow.mk f ≅ σ s))

def solution_set_condition (W : morphism_property C) {A B : C} (i : A ⟶ B) : Prop :=
∃ (S : Type w) (σ : S → arrow C) (hσ : ∀ (s : S), W (σ s).hom),
∀ ⦃X Y : C⦄ (f : A ⟶ X) (w : X ⟶ Y) (g : B ⟶ Y) (fac : f ≫ w = i ≫ g) (hw : W w),
  ∃ (s : S) (α : arrow.mk i ⟶ σ s) (β : σ s ⟶ arrow.mk w), α ≫ β = arrow.hom_mk fac

end morphism_property

end category_theory
