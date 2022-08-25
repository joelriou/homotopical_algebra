import for_mathlib.category_theory.morphism_property_misc
import category_theory.lifting_properties.basic
import for_mathlib.category_theory.lifting_properties.pullbacks
import for_mathlib.category_theory.lifting_properties.products

open category_theory.limits

namespace category_theory

variables {C : Type*} [category C]

namespace morphism_property

variables (F G : morphism_property C)

def has_lifting_property : Prop :=
∀ ⦃A B X Y : C⦄ (i : A ⟶ B) (hi : F i) (p : X ⟶ Y) (hp : G p), has_lifting_property i p

namespace has_lifting_property

variables {F G}

lemma property (h : has_lifting_property F G)
{A B X Y : C} {i : A ⟶ B} (hi : F i) {p : X ⟶ Y} (hp : G p) :
  category_theory.has_lifting_property i p := h i hi p hp

lemma op (h : has_lifting_property F G) :
  has_lifting_property G.op F.op :=
λ A B X Y i hi p hp, (h p.unop hp i.unop hi).op

lemma unop {F G : morphism_property Cᵒᵖ} (h : has_lifting_property F G) :
  has_lifting_property G.unop F.unop :=
λ A B X Y i hi p hp, (h p.op hp i.op hi).unop

variables (F G)
lemma iff_op : has_lifting_property F G ↔ has_lifting_property G.op F.op := ⟨op, unop⟩
lemma iff_unop (F' G' : morphism_property Cᵒᵖ) :
  has_lifting_property F' G' ↔ has_lifting_property G'.unop F'.unop := ⟨unop, op⟩

end has_lifting_property

@[simp]
def llp_with : morphism_property C :=
λ A B i, ∀ ⦃X Y : C⦄ (p : X ⟶ Y) (hp : G p), category_theory.has_lifting_property i p

@[simp]
def rlp_with : morphism_property C :=
λ X Y p, ∀ ⦃A B : C⦄ (i : A ⟶ B) (hi : F i), category_theory.has_lifting_property i p

lemma llp_with_op :
  F.op.llp_with = F.rlp_with.op :=
begin
  ext A B i,
  split,
  { intros h X Y p hp,
    rw category_theory.has_lifting_property.iff_op,
    exact h p.op hp, },
  { intros h X Y p hp,
    rw category_theory.has_lifting_property.iff_unop,
    exact h p.unop hp, },
end

lemma rlp_with_op :
  G.op.rlp_with = G.llp_with.op :=
begin
  ext A B i,
  split,
  { intros h X Y p hp,
    rw category_theory.has_lifting_property.iff_op,
    exact h p.op hp, },
  { intros h X Y p hp,
    rw category_theory.has_lifting_property.iff_unop,
    exact h p.unop hp, },
end

lemma llp_with_unop (G : morphism_property Cᵒᵖ) :
  G.unop.llp_with = G.rlp_with.unop :=
begin
  have h := rlp_with_op G.unop,
  rw G.op_unop at h,
  rw [h, unop_op],
end

lemma rlp_with_unop (F : morphism_property Cᵒᵖ) :
  F.unop.rlp_with = F.llp_with.unop :=
begin
  have h := llp_with_op F.unop,
  rw F.op_unop at h,
  rw [h, unop_op],
end

namespace llp_with

lemma contains_iso : isomorphisms C ⊆ G.llp_with :=
λ A B i hi X Y p hp, by { haveI : is_iso i := hi, apply_instance, }

lemma stable_under_composition : G.llp_with.stable_under_composition :=
λ A₁ A₂ A₃ i j hi hj X Y p hp, by { haveI := hi p hp, haveI := hj p hp, apply_instance, }

lemma respects_iso : G.llp_with.respects_iso :=
respects_iso.of_stable_under_composition_and_contains_iso
    (llp_with.stable_under_composition G) (llp_with.contains_iso G)

lemma stable_under_cobase_change : G.llp_with.stable_under_cobase_change :=
λ A A' B B' f g f' g' h hf X Y p hp, h.has_lifting_property_imp p (hf p hp)

lemma stable_under_coproducts : G.llp_with.stable_under_coproducts :=
⟨llp_with.respects_iso G,
  λ J A B hA hB i hi X Y p hp, by { haveI := λ j, hi j p hp, apply_instance, }⟩

end llp_with

namespace rlp_with

lemma contains_iso : isomorphisms C ⊆ F.rlp_with :=
λ X Y p hp A B i hi, by { haveI : is_iso p := hp, apply_instance, }

lemma stable_under_composition : F.rlp_with.stable_under_composition :=
λ X Y Z p q hp hq A B i hi, by { haveI := hp i hi, haveI := hq i hi, apply_instance, }

lemma respects_iso : F.rlp_with.respects_iso :=
respects_iso.of_stable_under_composition_and_contains_iso
    (rlp_with.stable_under_composition F) (rlp_with.contains_iso F)

lemma stable_under_base_change : F.rlp_with.stable_under_base_change :=
λ X' Y Y' X f g f' g' h hg A B i hi, h.has_lifting_property_imp i (hg i hi)

lemma stable_under_products : F.rlp_with.stable_under_products :=
⟨rlp_with.respects_iso F,
λ J X Y hX hY p hp A B i hi, by { haveI := λ j, hp j i hi, apply_instance, }⟩

end rlp_with

namespace stable_under_cobase_change

lemma coprod_inl {P : morphism_property C}
  (h : P.stable_under_cobase_change) (A B : C) [has_binary_coproduct A B]
  [has_initial C] (hB : P (initial.to B)) :
  P (coprod.inl : A ⟶ A ⨿ B) :=
h (is_pushout.of_has_binary_coproduct' A B) hB

lemma coprod_inr {P : morphism_property C}
  (h : P.stable_under_cobase_change) (A B : C) [has_binary_coproduct A B]
  [has_initial C] (hA : P (initial.to A)) :
  P (coprod.inr : B ⟶ A ⨿ B) :=
h (is_pushout.of_has_binary_coproduct' A B).flip hA

end stable_under_cobase_change

namespace stable_under_base_change

lemma prod_fst {P : morphism_property C}
  (h : P.stable_under_base_change) (X Y : C) [has_binary_product X Y]
  [has_terminal C] (hY : P (terminal.from Y)) :
  P (limits.prod.fst : X ⨯ Y ⟶ X) :=
h (is_pullback.of_has_binary_product' X Y).flip hY

lemma prod_snd {P : morphism_property C}
  (h : P.stable_under_base_change) (X Y : C) [has_binary_product X Y]
  [has_terminal C] (hX : P (terminal.from X)) :
  P (limits.prod.snd : X ⨯ Y ⟶ Y) :=
h (is_pullback.of_has_binary_product' X Y) hX

end stable_under_base_change

end morphism_property

end category_theory
