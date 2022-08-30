import category_theory.limits.is_limit
import set_theory.ordinal.basic
import order.category.Preorder
import category_theory.morphism_property
import for_mathlib.category_theory.lifting_properties.morphism_property
import category_theory.limits.shapes.functor_category
import category_theory.limits.types

import order.initial_seg

universes u v

namespace category_theory

open limits

variables {C : Type*} [category.{v} C] (P : morphism_property C)
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

section

variables {α} (X : αᵒᵖ ⥤ Type v)

@[simps]
def inclusion (b : α) : { a : α // a < b} ⥤ α :=
begin
  let φ : { a : α // a < b} → α := subtype.val,
  have hφ : monotone φ := λ x y h, h,
  exact monotone.functor hφ,
end

def solutions := (functor.const αᵒᵖ).obj (terminal (Type v)) ⟶ X

def compatible_system (b : α) := (functor.const { a : α // a < b}ᵒᵖ).obj (terminal (Type v)) ⟶
  (inclusion b).op ⋙ X

lemma X_map_comp {a b c : αᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ c) (φψ : a ⟶ c)
  (x : X.obj a) : X.map ψ (X.map φ x) = X.map (φψ) x :=
begin
  rw subsingleton.elim φψ (φ ≫ ψ),
  simp only [functor_to_types.map_comp_apply],
end

def restriction (b : α) (x : X.obj (opposite.op b)) : compatible_system X b :=
{ app := λ z n, X.map (hom_of_le (le_of_lt z.unop.2)).op x,
  naturality' := λ z₁ z₂ θ, begin
    ext n,
    dsimp [inclusion, monotone.functor],
    rw X_map_comp,
  end, }

lemma induction_principle (x₀ : X.obj (opposite.op ⊥))
  (hX : ∀ (b : α), function.surjective (restriction X b)) :
  ∃ (S : solutions X), S.app (opposite.op ⊥) = λ n, x₀ := sorry

end

@[simp]
lemma hom_of_le_self_eq_id (a : α) : hom_of_le (show a ≤ a, by refl) = 𝟙 a := subsingleton.elim _ _

@[simp]
lemma hom_of_le_le_of_hom {a b : α} (f : a ⟶ b) : hom_of_le (le_of_hom f) = f := subsingleton.elim _ _

noncomputable
instance : inhabited (⊤_ (Type v)) :=
by { let φ := terminal.from (ulift.{v} (fin 1)), exact ⟨φ (ulift.up 0)⟩ }

lemma llp_is_stable_under_transfinite_composition (P : morphism_property C) :
  P.llp_with.is_stable_under_transfinite_composition α :=
λ F hF₁ hF₂ c hc X Y p hp, ⟨λ f g, begin
  dsimp at g,
  intro sq,
  have sqs : Π (a : α), comm_sq f (F.map (hom_of_le (bot_le : ⊥ ≤ a))) p (c.ι.app a ≫ g) :=
    λ a, comm_sq.mk (by rw [sq.w, cocone.w_assoc]),
  let τ : Π (a b : α) (h : a ≤ b), (sqs b).lift_struct → (sqs a).lift_struct := λ a b h l,
  { l := F.map (hom_of_le h) ≫ l.l,
    fac_left' := by simpa only [← l.fac_left, ← F.map_comp_assoc],
    fac_right' := by simp only [category.assoc, l.fac_right, cocone.w_assoc], },
  let X : αᵒᵖ ⥤ Type v :=
  { obj := λ b, (sqs b.unop).lift_struct,
    map := λ a b h, τ b.unop a.unop (le_of_hom h.unop),
    map_id' := λ a, begin
      ext,
      dsimp [τ],
      simp only [hom_of_le_self_eq_id, functor.map_id, category.id_comp],
    end,
    map_comp' := λ a b c φ₁ φ₂, begin
      ext,
      dsimp [τ],
      rw [← F.map_comp_assoc],
      congr,
    end, },
  let x₀ : X.obj (opposite.op ⊥) :=
  { l := f,
    fac_left' := by { dsimp, rw [hom_of_le_self_eq_id, F.map_id, category.id_comp], },
    fac_right' := sq.w, },
  let n : ⊤_ (Type v) := arbitrary _,
  cases induction_principle X x₀ _ with L hL,
  { exact ⟨nonempty.intro
    { l := begin
        refine hc.desc (cocone.mk _ _),
        exact
        { app := λ b, (L.app (opposite.op b) n).l,
          naturality' := λ a b h, begin
            dsimp,
            simpa only [types_comp_apply, functor.const_obj_map, types_id_apply,
              category.comp_id, comm_sq.lift_struct.ext_iff, hom_of_le_le_of_hom]
              using congr_fun (L.naturality h.op).symm n,
          end },
      end,
      fac_left' := by simp only [is_colimit.fac, hL],
      fac_right' := hc.hom_ext (λ b, by simpa only [is_colimit.fac_assoc]
        using (L.app (opposite.op b) n).fac_right), }⟩, },
  { intros b s,
    by_cases ∃ (b₀ : α) (h₀ : b₀ < b), ∀ (a : α), a < b → a ≤ b₀,
    { rcases h with ⟨b₀, h₀, h₁⟩,
      let L := (s.app (opposite.op ⟨b₀, h₀⟩) n),
      have H := hF₂ b₀ p hp,
      let e : arrow.mk (F.map (hom_of_le (le_succ b₀))) ≅ arrow.mk (F.map (hom_of_le (le_of_lt h₀))) :=
        arrow.iso_mk' (F.map (hom_of_le (le_succ b₀))) (F.map (hom_of_le (le_of_lt h₀))) (iso.refl _)
          (F.map_iso (eq_to_iso begin
            dsimp [well_founded.succ],
            rw dif_pos,
            { apply le_antisymm,
              { exact well_founded.min_le _ h₀, },
              { sorry, }, },
          end)) begin
            simp only [iso.refl_hom, category.id_comp, functor.map_iso_hom, eq_to_iso.hom, ← F.map_comp],
            congr,
          end,
      rw has_lifting_property.iff_of_arrow_iso_left e at H,
      haveI := H,
      let s' : X.obj (opposite.op b) := sorry,
      sorry, },
    sorry, },
end⟩

end morphism_property

end category_theory
