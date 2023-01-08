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

lemma order.are_succ.of_le_iff {m : α} (a b : { x : α // x ≤ m}) :
  order.are_succ a b ↔ order.are_succ a.1 b.1 :=
begin
  split,
  { intro h,
    exact ⟨h.1, λ c hc₁ hc₂, subtype.ext_iff.1 (h.2 ⟨c, hc₂.le.trans b.2⟩ hc₁ hc₂)⟩, },
  { intro h,
    exact ⟨h.1, λ c hc₁ hc₂, by { ext, exact h.2 c.1 hc₁ hc₂}⟩, },
end

lemma order.is_succ.of_le_iff {m : α} (b : { x : α // x ≤ m}) :
  order.is_succ b ↔ order.is_succ b.1 :=
begin
  split,
  { rintro ⟨a, ha⟩,
    rw order.are_succ.of_le_iff at ha,
    exact ⟨_, ha⟩, },
  { rintro ⟨a, ha⟩,
    let a' : { x // x ≤ m} := ⟨a, ha.1.le.trans b.2⟩,
    exact ⟨_, (order.are_succ.of_le_iff a' b).2 ha⟩, },
end

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

@[simps]
def order.le_inclusion_functor_of_le (m₁ m₂ : α) (h : m₁ ≤ m₂) :
  { a : α // a ≤ m₁ } ⥤ { a : α // a ≤ m₂ } :=
begin
  let φ : { a : α // a ≤ m₁ } → { a : α // a ≤ m₂ } := λ a, ⟨a.1, a.2.trans h⟩,
  have hφ : monotone φ := λ a b hab, hab,
  exact monotone.functor hφ,
end

@[simps]
def order.order_iso_lt_le (m₁ m₂ : α) (h : m₁ ≤ m₂) (b : { x // x ≤ m₁}) :
  order_iso { y : { x // x ≤ m₁ } // y < b } { y : { x // x ≤ m₂ } // y < ⟨b.1, b.2.trans h⟩ } :=
{ to_fun := λ y, ⟨⟨y.1.1, y.1.2.trans h⟩, y.2⟩,
  inv_fun := λ y, ⟨⟨y.1, (show y.1.1 ≤ b.1, by exact y.2.le).trans (b.2 : b.1 ≤ m₁)⟩, y.2⟩,
  left_inv := λ y, by { ext, refl, },
  right_inv := λ y, by { ext, refl, },
  map_rel_iff' := λ x y, ⟨λ h, h, λ h, h⟩, }

@[simps]
def order_iso.to_equivalence {α : Type u } {β : Type v} [preorder α] [preorder β]
  (e : order_iso α β) : α ≌ β :=
{ functor := monotone.functor e.monotone,
  inverse := monotone.functor e.symm.monotone,
  unit_iso := eq_to_iso (category_theory.functor.ext (λ a, (e.left_inv a).symm)
    (λ a₁ a₂ f, subsingleton.elim _ _)),
  counit_iso := eq_to_iso (category_theory.functor.ext (λ b, (e.right_inv b))
    (λ b₁ b₂ f, subsingleton.elim _ _)),
  functor_unit_iso_comp' := λ X, subsingleton.elim _ _, }

@[simps]
def order.lt_inclusion_functor_iso_of_le (m₁ m₂ : α) (h : m₁ ≤ m₂) (b : { x // x ≤ m₁}) :
  order.lt_inclusion_functor b ⋙ order.le_inclusion_functor_of_le m₁ m₂ h ≅
    (order.order_iso_lt_le m₁ m₂ h b).to_equivalence.functor ⋙
      order.lt_inclusion_functor (⟨b, b.2.trans h⟩ : { x // x ≤ m₂ }) := iso.refl _

end

section

variables {α : Type*} [linear_order α]

lemma order.is_bot.of_le_iff {m : α} (a : { x : α // x ≤ m}) :
  order.is_bot a ↔ order.is_bot a.1 :=
begin
  split,
  { intros h b,
    by_cases hb : b ≤ m,
    { exact h ⟨b, hb⟩, },
    { exact a.2.trans (not_le.1 hb).le, }, },
  { intros h b,
    exact h b.1, },
end

lemma order.is_limit.of_le_iff {m : α} (a : { x : α // x ≤ m}) :
  order.is_limit a ↔ order.is_limit a.1 :=
begin
  dsimp only [order.is_limit],
  rw [order.is_bot.of_le_iff, order.is_succ.of_le_iff],
end


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

section

variables [linear_order α] {m : α}

def restriction (m₁ m₂ : α) (h : m₁ ≤ m₂) :
  transfinite_iteration τ m₂ ⥤ transfinite_iteration τ m₁ :=
{ obj := λ I,
  { F := order.le_inclusion_functor_of_le _ _ h ⋙ I.F,
    hF := begin
      rintro ⟨b, hb⟩ hb',
      have hc := I.hF ⟨b, hb.trans h⟩ (by simpa only [order.is_limit.of_le_iff] using hb'),
      let e := order.lt_inclusion_functor_iso_of_le m₁ m₂ h ⟨b, hb⟩,
      let e' := iso_whisker_right e I.F,
      sorry,
    end,
    iso := λ a b hab, I.iso ⟨a.1, a.2.trans h⟩ ⟨b.1, b.2.trans h⟩
      (by simpa only [order.are_succ.of_le_iff] using hab), },
  map := λ I₁ I₂ f,
  { f := whisker_left (order.le_inclusion_functor_of_le _ _ h) f.f,
    commτ := λ a b hab, f.commτ ⟨a.1, a.2.trans h⟩ ⟨b.1, b.2.trans h⟩
      (by simpa only [order.are_succ.of_le_iff] using hab), }, }

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

lemma full_eval_zero : full (eval τ m a₀) :=
begin
  sorry,
end

end transfinite_iteration

end functor

end category_theory
