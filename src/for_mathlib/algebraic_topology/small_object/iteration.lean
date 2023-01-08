import for_mathlib.category_theory.lifting_properties.continuous_functor

noncomputable theory

universes w v u

open category_theory category_theory.category category_theory.limits

section

variables {α : Type*} [partial_order α] (a b : α)

def order.is_bot : Prop := ∀ (b : α), a ≤ b
def order.is_top : Prop := ∀ (a : α), a ≤ b

variables {a b}

lemma order.is_bot.unique (ha : order.is_bot a) (hb : order.is_bot b) :
  a = b :=
le_antisymm (ha _) (hb _)

lemma order.is_top.unique (ha : order.is_top a) (hb : order.is_top b) :
  a = b :=
le_antisymm (hb _) (ha _)

variables (a b)

variable (α)

def order.exists_min : Prop := ∃ (x : α), order.is_bot x

def order.exists_max : Prop := ∃ (y : α), order.is_top y

variable {α}

def order.are_succ : Prop := (a < b) ∧
  ∀ (c : α) (hc₁ : a ≤ c) (hc₂ : c < b), c = a

def order.is_succ : Prop :=
  ∃ (a : α), order.are_succ a b

def order.is_limit : Prop :=
  (¬order.is_bot a) ∧ (¬order.is_succ a)

variables {a b}

def order.are_succ.lt (h : order.are_succ a b) : a < b := h.1

def order.are_succ.hom (h : order.are_succ a b) :
  a ⟶ b := hom_of_le h.1.le

@[simps, nolint unused_arguments]
def order.lt_inclusion_functor (m : α) :
  { a : α // a < m } ⥤ α :=
monotone.functor (subtype.mono_coe _)

@[simps]
def order.lt_cocone (m : α) {C : Type*} [category C] (F : α ⥤ C) :
  cocone (order.lt_inclusion_functor m ⋙ F) :=
{ X := F.obj m,
  ι :=
  { app := λ a, F.map (hom_of_le a.2.le),
    naturality' := λ a b f, begin
      dsimp,
      simp only [comp_id, ← F.map_comp],
      congr,
    end, }, }

end

lemma is_well_order.three_cases {α : Type*} [linear_order α] [is_well_order α (<)]
  (a : α) : order.is_bot a ∨ order.is_succ a ∨ order.is_limit a :=
begin
  by_cases h₁ : order.is_bot a,
  { exact or.inl h₁, },
  { by_cases h₂ : order.is_succ a,
    { exact or.inr (or.inl h₂), },
    { exact or.inr (or.inr ⟨h₁, h₂⟩), }, },
end

instance is_well_order_subtype {α : Type*} [linear_order α] [is_well_order α (<)]
  (P : α → Prop) : is_well_order { a : α // P a } (<) :=
begin
  haveI : is_trichotomous { a : α // P a } (<) := ⟨λ a b, begin
    rcases @is_trichotomous.trichotomous α (<) _ a.1 b.1 with h₁ | (h₂ | h₃),
    { exact or.inl h₁, },
    { exact or.inr (or.inl (by { ext, exact h₂, })), },
    { exact or.inr (or.inr h₃), },
  end⟩,
  haveI : is_trans { a : α // P a } (<) := ⟨λ a b c hab hbc, hab.trans hbc⟩,
  haveI : is_well_founded { a : α // P a } (<) := ⟨⟨begin
    rintro ⟨a, ha⟩,
    apply @well_founded.induction α (<) is_well_founded.wf (λ (a : α),
      ∀ (ha : P a), acc (<) (⟨a, ha⟩ : { b : α // P b})),
    refine λ b H hb, acc.intro _ _,
    rintro ⟨a, ha⟩ hab,
    exact H a hab ha,
  end⟩⟩,
  constructor,
end

namespace category_theory

namespace functor

variables {C : Type u} [category.{v} C] {α : Type*}
  {Φ : C ⥤ C} (τ : 𝟭 C ⟶ Φ)

structure transfinite_iteration [partial_order α] (m : α) :=
(F : { a : α // a ≤ m } ⥤ C)
(hF : ∀ (b : { a : α // a ≤ m }) (hb : order.is_limit b),
  is_colimit (order.lt_cocone b F))
(iso : Π (a b : { a : α // a ≤ m }) (hab : order.are_succ a b),
  under.mk (F.map hab.hom) ≅ under.mk (τ.app (F.obj a)))

namespace transfinite_iteration

variables {τ} {α}

section

variables [partial_order α] {m : α}

@[ext]
structure hom (I₁ I₂ : transfinite_iteration τ m) :=
(f : I₁.F ⟶ I₂.F)
(commτ : Π (a b : { a : α // a ≤ m}) (hab : order.are_succ a b),
  (I₁.iso a b hab).hom.right ≫ Φ.map (f.app a) =
    f.app b ≫ (I₂.iso a b hab).hom.right)

@[simps]
def hom.id (I : transfinite_iteration τ m) :
  hom I I :=
{ f := 𝟙 _,
  commτ := by tidy, }

@[simps]
def hom.comp {I₁ I₂ I₃ : transfinite_iteration τ m} (f : hom I₁ I₂) (g : hom I₂ I₃) :
  hom I₁ I₃ :=
{ f := f.f ≫ g.f,
  commτ := λ a b hab, by simp only [nat_trans.comp_app, map_comp, assoc,
      reassoc_of (f.commτ a b hab), g.commτ a b hab], }

instance : category (transfinite_iteration τ m) :=
{ hom := hom,
  id := hom.id,
  comp := λ I₁ I₂ I₃, hom.comp, }

variables (τ m)

@[simps]
def eval (a : { b : α // b ≤ m}) : transfinite_iteration τ m ⥤ C :=
{ obj := λ I, I.F.obj a,
  map := λ I₁ I₂ f, f.f.app a, }

end

variables [linear_order α] [is_well_order α (<)] (m : α) (a₀ : { b : α // b ≤ m})
  (ha₀ : order.is_bot a₀)

include ha₀

lemma faithful_eval_zero : faithful (eval τ m a₀) :=
⟨λ I₁ I₂ f g h, begin
  ext b,
  apply @well_founded.induction { b : α // b ≤ m } (<) is_well_founded.wf
    (λ b, f.f.app b = g.f.app b),
  intros b H,
  rcases is_well_order.three_cases b with h₁ | (h₂ | h₃),
  { have eq := order.is_bot.unique ha₀ h₁,
    subst eq,
    exact h, },
  { obtain ⟨a, hab⟩ := h₂,
    simp only [← cancel_mono ((under.forget _).map (I₂.iso a b hab).hom),
      under.forget_map, ← f.commτ a b hab, H a hab.lt, g.commτ a b hab], },
  { apply (I₁.hF b h₃).hom_ext,
    intro a,
    simp only [order.lt_cocone_ι_app, nat_trans.naturality],
    congr' 1,
    exact H a a.2, },
end⟩

end transfinite_iteration

end functor

end category_theory
