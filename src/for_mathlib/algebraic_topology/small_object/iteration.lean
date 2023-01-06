import for_mathlib.category_theory.lifting_properties.continuous_functor

noncomputable theory

universes w v u

open category_theory category_theory.category category_theory.limits

section

variables {α : Type*} [linear_order α] [is_well_order α (<)] (a b : α)

def is_well_order.is_succ : Prop := (a < b) ∧
  (b = (is_well_founded.wf : well_founded ((<) : α → α → Prop)).succ a)

variables {a b}

lemma is_well_order.is_succ.lt (h : is_well_order.is_succ a b) :
  a < b := h.1

lemma is_well_order.is_succ.le (h : is_well_order.is_succ a b) :
  a ≤ b := h.1.le

lemma is_well_order.is_succ.hom (h : is_well_order.is_succ a b) :
  a ⟶ b := hom_of_le h.le

end

namespace category_theory

namespace functor

variables {C : Type u} [category.{v} C] {Φ : C ⥤ C} (τ : 𝟭 C ⟶ Φ)
  (α : Type w) [linear_order α] [is_well_order α (<)]

structure transfinite_iteration :=
(F : α ⥤ C)
(hF : F.well_order_continuous)
(iso : Π (a b : α) (hab : is_well_order.is_succ a b),
  under.mk (F.map hab.hom) ≅ under.mk (τ.app (F.obj a)))

namespace transfinite_iteration

variables {τ} {α}

@[ext]
structure hom (I₁ I₂ : transfinite_iteration τ α) :=
(f : I₁.F ⟶ I₂.F)
(commτ : Π (a b : α) (hab : is_well_order.is_succ a b),
  (I₁.iso a b hab).hom.right ≫ Φ.map (by exact f.app a) =
    f.app b ≫ (I₂.iso a b hab).hom.right)

@[simps]
def hom.id (I : transfinite_iteration τ α) :
  hom I I :=
{ f := 𝟙 _,
  commτ := by tidy, }

@[simps]
def hom.comp {I₁ I₂ I₃ : transfinite_iteration τ α} (f : hom I₁ I₂) (g : hom I₂ I₃) :
  hom I₁ I₃ :=
{ f := f.f ≫ g.f,
  commτ := λ a b hab, by simp only [nat_trans.comp_app, map_comp, assoc,
      reassoc_of (f.commτ a b hab), g.commτ a b hab], }

instance : category (transfinite_iteration τ α) :=
{ hom := hom,
  id := hom.id,
  comp := λ I₁ I₂ I₃, hom.comp, }

end transfinite_iteration

end functor

end category_theory
