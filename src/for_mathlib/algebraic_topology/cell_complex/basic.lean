import category_theory.morphism_property
import for_mathlib.category_theory.lifting_properties.continuous_functor

universes v u

namespace category_theory

open limits

namespace morphism_property

variables {C : Type u} [category.{v} C] (I : morphism_property C)

def pushouts : morphism_property C :=
λ X Y f, ∃ (A B : C) (i : A ⟶ B) (hi : I i) (g : A ⟶ X) (g' : B ⟶ Y),
  is_pushout i g g' f

inductive transfinite_composition : morphism_property C
| transfinite {α : Type v} [linear_order α] [is_well_order α (<)] [order_bot α]
  (F : α ⥤ C) (hF₁ : F.well_order_continuous)
  (hF₂ : ∀ (a : α) (ha : ∃ (b : α), a < b), I (F.map (hom_of_le (le_succ a)))) (c : cocone F)
  (hc : is_colimit c) : transfinite_composition (c.ι.app ⊥)

def relative_cell_complex := I.pushouts.transfinite_composition

end morphism_property

end category_theory
