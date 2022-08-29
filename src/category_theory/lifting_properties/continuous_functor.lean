import category_theory.limits.is_limit
import set_theory.ordinal.basic
import order.category.Preorder
import category_theory.morphism_property
import for_mathlib.category_theory.lifting_properties.morphism_property

import order.initial_seg

universe u

namespace category_theory

open limits

variables {C : Type*} [category C] (P : morphism_property C)
  {α : Type u} [linear_order α] [is_well_order α (<)] (F : α ⥤ C)
  {β : Type*} [linear_order β] (h : principal_seg ((<) : β → β → Prop) ((<) : α → α → Prop))

@[simps]
def functor.well_order_inclusion_functor'
  (h : initial_seg ((<) : β → β → Prop) ((<) : α → α → Prop)) : β ⥤ α :=
begin
  refine monotone.functor (_ : monotone h.to_rel_embedding.1.1),
  intros b₁ b₂ r,
  obtain (h₁ | h₂) := lt_or_eq_of_le r,
  { rw ← h.to_rel_embedding.2 at h₁,
    exact le_of_lt h₁, },
  { subst h₂, },
end

include h

@[simps]
def functor.well_order_inclusion_functor : β ⥤ α :=
begin
  refine monotone.functor (_ : monotone h.to_rel_embedding.1.1),
  intros b₁ b₂ r,
  obtain (h₁ | h₂) := lt_or_eq_of_le r,
  { rw ← h.to_rel_embedding.2 at h₁,
    exact le_of_lt h₁, },
  { subst h₂, },
end

def functor.well_order_cocone : limits.cocone (functor.well_order_inclusion_functor h ⋙ F) :=
{ X := F.obj h.top,
  ι :=
  { app := λ b, F.map (hom_of_le (le_of_lt (by { dsimp, rw h.down, use b, }))),
    naturality' := λ b₁ b₂ hb, by { dsimp, simpa only [← F.map_comp, category.comp_id], }, }, }

omit h

def functor.well_order_continuous₀ (F : α ⥤ C) (β : Type u) [linear_order β] :=
  Π (h : principal_seg ((<): β → β → Prop) ((<) : α → α → Prop)),
    limits.is_colimit (F.well_order_cocone h)

def functor.well_order_continuous (F : α ⥤ C) := Π (β : Type u) [hβ : linear_order β],
  @functor.well_order_continuous₀ _ _ _ _ _ F _ hβ

namespace morphism_property

lemma le_succ (a : α) : a ≤ (is_well_founded.wf : well_founded ((<) : α → α → Prop)).succ a :=
begin
  by_cases ∃ b, a < b,
  { refine le_of_lt _,
    exact is_well_founded.wf.lt_succ h, },
  { dsimp [well_founded.succ],
    rw dif_neg,
    exact h, },
end

variables (α) [order_bot α]
def is_stable_under_transfinite_composition (P : morphism_property C) : Prop :=
  ∀ (F : α ⥤ C) (hF₁ : F.well_order_continuous)
    (hF₂ : ∀ (a : α), P (F.map (hom_of_le (le_succ a))))
    (c : cocone F) (hc : is_colimit c), P (c.ι.app ⊥)

structure initial_seg' := (β : Type u) [lo : linear_order β]
(h : initial_seg ((<) : β → β → Prop) ((<) : α → α → Prop))

instance (B : initial_seg' α) : linear_order B.β := B.lo

lemma llp_is_stable_under_transfinite_composition (P : morphism_property C) :
  P.llp_with.is_stable_under_transfinite_composition α :=
λ F hF₁ hF₂ c hc X Y p hp, ⟨λ f g, begin
  dsimp at g,
  intro sq,
  suffices : ∀ (B : initial_seg' α),
    ∃ (L : functor.well_order_inclusion_functor' B.h ⋙ F ⟶ (functor.const B.β).obj X)
    (hL₁ : ∀ (b : B.β), f = F.map (hom_of_le bot_le) ≫ nat_trans.app L b),
    ∀ (b : B.β), nat_trans.app L b ≫ p = c.ι.app (B.h b) ≫ g,
  { rcases this (initial_seg'.mk α (by refl)) with ⟨L, hL₁, hL₂⟩,
    dsimp [initial_seg.refl, functor.well_order_inclusion_functor'] at L hL₁ hL₂,
    exact ⟨nonempty.intro
    { l := begin
        refine hc.desc (cocone.mk _ _),
        exact
        { app := L.app,
          naturality' := λ a₁ a₂ r, by convert L.naturality r, },
      end,
      fac_left' := begin
        have eq : (hom_of_le bot_le : (⊥ : α) ⟶ _) = 𝟙 ⊥ := subsingleton.elim _ _,
        simp only [is_colimit.fac, hL₁ ⊥, eq, F.map_id, category.id_comp],
      end,
      fac_right' := hc.hom_ext (λ a, by simp only [is_colimit.fac_assoc, hL₂]), }⟩, },
  sorry,
end⟩


end morphism_property

end category_theory
