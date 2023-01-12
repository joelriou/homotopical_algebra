import for_mathlib.category_theory.lifting_properties.continuous_functor

noncomputable theory

universes w v u

open category_theory category_theory.category category_theory.limits

section

variables {α : Type w} [partial_order α] {a b : α}

lemma is_bot.unique (ha : is_bot a) (hb : is_bot b) :
  a = b :=
le_antisymm (ha _) (hb _)

lemma is_bot.of_le (ha : is_bot b) (a : α) (h : a ≤ b) : is_bot a :=
λ c, h.trans (ha c)

lemma is_top.unique (ha : is_top a) (hb : is_top b) :
  a = b :=
le_antisymm (hb _) (ha _)

variables (a b)

def order.are_succ : Prop := (a < b) ∧
  ∀ (c : α) (hc₁ : a ≤ c) (hc₂ : c < b), c = a

def order.is_succ : Prop :=
  ∃ (a : α), order.are_succ a b

def order.is_limit : Prop :=
  (¬is_bot a) ∧ (¬order.is_succ a)

variables {a b}

def order.are_succ.lt (h : order.are_succ a b) : a < b := h.1

def order.are_succ.le (h : order.are_succ a b) : a ≤ b := h.1.le

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

@[simps]
def order.lt_inclusion_functor_iso_of_le' (m₁ m₂ : α) (h : m₁ ≤ m₂) (b : { x // x ≤ m₁}) :
  (order.order_iso_lt_le m₁ m₂ h b).to_equivalence.inverse ⋙
    order.lt_inclusion_functor b ⋙ order.le_inclusion_functor_of_le m₁ m₂ h ≅
      order.lt_inclusion_functor (⟨b, b.2.trans h⟩ : { x // x ≤ m₂ }) :=
iso_whisker_left (order.order_iso_lt_le m₁ m₂ h b).to_equivalence.inverse
  (order.lt_inclusion_functor_iso_of_le m₁ m₂ h b) ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right (order.order_iso_lt_le m₁ m₂ h b).to_equivalence.counit_iso _ ≪≫
  functor.left_unitor _

lemma is_bot.subsingleton_le {m : α} (hm : is_bot m) :
  subsingleton {a // a ≤ m} :=
⟨λ x₁ x₂, begin
  have eq : ∀ (x : {x // x ≤ m}), x = ⟨m, hm m⟩ := λ x, le_antisymm x.2 (hm _),
  rw [eq x₁, eq x₂],
end⟩

end

section

variables {α : Type*} [linear_order α]

@[simp]
lemma is_bot.of_le_iff {m : α} (a : { x : α // x ≤ m}) :
  is_bot a ↔ is_bot a.1 :=
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
  rw [is_bot.of_le_iff, order.is_succ.of_le_iff],
end

lemma order.are_succ.lt_iff_le {a b : α} (h : order.are_succ a b) (c : α) : c < b ↔ c ≤ a :=
begin
  split,
  { intro hc,
    by_contra',
    simpa only [h.2 c this.le hc, lt_self_iff_false] using this, },
  { intro hc,
    exact lt_of_le_of_lt hc h.lt, },
end

lemma order.are_succ.pred_uniq {a a' b : α} (h₁ : order.are_succ a b) (h₂ : order.are_succ a' b) :
  a = a' :=
le_antisymm (by simpa only [← h₂.lt_iff_le] using h₁.lt)
  (by simpa only [← h₁.lt_iff_le] using h₂.lt)

section

variables {C : Type*} [category C] {m : α} (hm : is_top m)
  (F G : α ⥤ C) (φ : order.lt_inclusion_functor m ⋙ F ⟶ order.lt_inclusion_functor m ⋙ G)
  (φm : F.obj m ⟶ G.obj m)
  (comm : ∀ (a : { x // x < m }), F.map (hom_of_le (hm a.1)) ≫ φm =
    φ.app a ≫ G.map (hom_of_le (hm a.1)))

include comm

def is_top.mk_nat_trans : F ⟶ G :=
{ app := λ a, begin
    by_cases a < m,
    { exact φ.app ⟨a, h⟩, },
    { refine eq_to_hom _ ≫ φm ≫ eq_to_hom _,
      all_goals
      { rw le_antisymm (hm _) (not_lt.1 h), }, },
  end,
  naturality' := λ a₁ a₂ ψ, begin
    by_cases h₂ : a₂ < m,
    { have h₁ := lt_of_le_of_lt (le_of_hom ψ) h₂,
      rw [dif_pos h₁, dif_pos h₂],
      let b₁ : { x // x < m} := ⟨a₁, h₁⟩,
      let b₂ : { x // x < m} := ⟨a₂, h₂⟩,
      have ψ' : b₁ ≤ b₂ := le_of_hom ψ,
      convert φ.naturality (hom_of_le ψ'), },
    { have h₂' := le_antisymm (not_lt.1 h₂) (hm a₂),
      subst h₂',
      rw dif_neg (lt_irrefl m),
      by_cases h₁ : a₁ < m,
      { simp only [dif_pos h₁, eq_to_hom_refl, id_comp, comp_id],
        convert comm ⟨a₁ ,h₁⟩, },
      { have h₁' := le_antisymm (not_lt.1 h₁) (hm a₁),
        subst h₁',
        simp only [dif_neg (lt_irrefl m), subsingleton.elim ψ (𝟙 _),
          category_theory.functor.map_id, comp_id, id_comp], }, },
  end, }

lemma is_top.mk_nat_trans_eq (a : α) (ha : a < m) :
  (is_top.mk_nat_trans hm F G φ φm comm).app a = φ.app ⟨a, ha⟩ :=
begin
  dsimp only [is_top.mk_nat_trans],
  rw dif_pos ha,
end

@[simp]
lemma is_top.mk_nat_trans_eq' :
  (is_top.mk_nat_trans hm F G φ φm comm).app m = φm :=
begin
  dsimp only [is_top.mk_nat_trans],
  simp only [dif_neg (lt_irrefl m), eq_to_hom_refl, comp_id, id_comp],
end

end

section

variables {C : Type*} [category C] {m₁ m₂ : α} (hm₁₂ : order.are_succ m₁ m₂)
  (hm₂ : is_top m₂)
  (F G : α ⥤ C) (φ : order.lt_inclusion_functor m₂ ⋙ F ⟶ order.lt_inclusion_functor m₂ ⋙ G)
  (φm : F.obj m₂ ⟶ G.obj m₂)
  (comm : F.map hm₁₂.hom ≫ φm = φ.app ⟨m₁, hm₁₂.lt⟩ ≫ G.map hm₁₂.hom)

include comm

def order.are_succ.mk_nat_trans : F ⟶ G :=
hm₂.mk_nat_trans F G φ φm (λ a, begin
  have r : a.1 ≤ m₁ := (hm₁₂.lt_iff_le _).1 a.2,
  have r' : a ≤ ⟨m₁, hm₁₂.lt⟩ := r,
  simp only [subsingleton.elim (hom_of_le (r.trans hm₁₂.le)) (hom_of_le r ≫ hom_of_le hm₁₂.le),
    functor.map_comp, assoc],
  erw comm,
  apply φ.naturality_assoc (hom_of_le r'),
end)

lemma order.are_succ.mk_nat_trans_eq (a : α) (ha : a < m₂) :
  (order.are_succ.mk_nat_trans hm₁₂ hm₂ F G φ φm comm).app a = φ.app ⟨a, ha⟩ :=
begin
  dsimp only [order.are_succ.mk_nat_trans],
  apply is_top.mk_nat_trans_eq,
end

@[simp]
lemma order.are_succ.mk_nat_trans_eq' :
  (order.are_succ.mk_nat_trans hm₁₂ hm₂ F G φ φm comm).app m₂ = φm :=
begin
  dsimp only [order.are_succ.mk_nat_trans],
  apply is_top.mk_nat_trans_eq',
end

end

end

lemma is_well_order.three_cases {α : Type*} [linear_order α] [is_well_order α (<)]
  (a : α) : is_bot a ∨ order.is_succ a ∨ order.is_limit a :=
begin
  by_cases h₁ : is_bot a,
  { exact or.inl h₁, },
  { by_cases h₂ : order.is_succ a,
    { exact or.inr (or.inl h₂), },
    { exact or.inr (or.inr ⟨h₁, h₂⟩), }, },
end

lemma is_well_order.two_cases {α : Type*} [linear_order α] [is_well_order α (<)]
  (a : α) (ha : ¬is_bot a) : order.is_succ a ∨ order.is_limit a :=
begin
  by_cases order.is_succ a,
  { exact or.inl h, },
  { exact or.inr ⟨ha, h⟩, },
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
      apply limits.is_colimit.of_whisker_equivalence
        (order.order_iso_lt_le m₁ m₂ h ⟨b, hb⟩).to_equivalence.symm,
      let e := order.lt_inclusion_functor_iso_of_le' m₁ m₂ h ⟨b, hb⟩,
      let e' := iso_whisker_right e I.F,
      let e'' : (order.order_iso_lt_le m₁ m₂ h ⟨b, hb⟩).to_equivalence.inverse ⋙
        order.lt_inclusion_functor ⟨b, hb⟩ ⋙ order.le_inclusion_functor_of_le m₁ m₂ h ⋙
        I.F ≅ _ := e',
      equiv_rw (limits.is_colimit.precompose_hom_equiv e''.symm _).symm,
      refine is_colimit.of_iso_colimit hc (cocones.ext (iso.refl _) (λ a, _)),
      dsimp,
      simpa only [comp_id, ← I.F.map_comp],
    end,
    iso := λ a b hab, I.iso ⟨a.1, a.2.trans h⟩ ⟨b.1, b.2.trans h⟩
      (by simpa only [order.are_succ.of_le_iff] using hab), },
  map := λ I₁ I₂ f,
  { f := whisker_left (order.le_inclusion_functor_of_le _ _ h) f.f,
    commτ := λ a b hab, f.commτ ⟨a.1, a.2.trans h⟩ ⟨b.1, b.2.trans h⟩
      (by simpa only [order.are_succ.of_le_iff] using hab), }, }

end

variables (τ) [linear_order α] [is_well_order α (<)] (m : α) (a₀ : { b : α // b ≤ m})
  (ha₀ : is_bot a₀)

include ha₀

lemma faithful_eval_zero : faithful (eval τ m a₀) :=
⟨λ I₁ I₂ f g h, begin
  ext b,
  apply @well_founded.induction { b : α // b ≤ m } (<) is_well_founded.wf
    (λ b, f.f.app b = g.f.app b),
  intros b H,
  rcases is_well_order.three_cases b with h₁ | (h₂ | h₃),
  { have eq := is_bot.unique ha₀ h₁,
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

variable {m}

lemma eval_injective (I₁ I₂ : transfinite_iteration τ m) (m₁ m₂ : { x // x ≤ m})
  (f₁ : (restriction m₁.1 m m₁.2).obj I₁ ⟶ (restriction m₁.1 m m₁.2).obj I₂)
  (f₂ : (restriction m₂.1 m m₂.2).obj I₁ ⟶ (restriction m₂.1 m m₂.2).obj I₂)
  (eq : f₁.f.app ⟨a₀.1, ha₀ _⟩ = f₂.f.app ⟨a₀.1, ha₀ _⟩)
  (a : { x // x ≤ m}) (ha₁ : a ≤ m₁) (ha₂ : a ≤ m₂) :
  f₁.f.app ⟨a.1, ha₁⟩ = f₂.f.app ⟨a.1, ha₂⟩ :=
begin
  suffices : (restriction a.1 m₁.1 ha₁).map f₁ = (restriction a.1 m₂.1 ha₂).map f₂,
  { exact congr_app (congr_arg transfinite_iteration.hom.f this) ⟨a.1, le_refl _⟩, },
  haveI := faithful_eval_zero τ a.1 ⟨a₀, ha₀ _⟩
    (by simpa only [is_bot.of_le_iff] using ha₀),
  exact (eval τ a.1 ⟨a₀, ha₀ _⟩).map_injective eq,
end

variable (m)

lemma full_eval_zero : full (eval τ m a₀) :=
nonempty.some begin
  rcases a₀ with ⟨a₀, ha₁⟩,
  rw is_bot.of_le_iff at ha₀,
  dsimp at ha₀,
  apply @well_founded.induction α (<) is_well_founded.wf (λ (m' : α), nonempty
    (full (eval τ m' ⟨a₀, ha₀ _⟩))),
  clear ha₁ m,
  intros m H,
  refine ⟨full_of_surjective _ (λ I₁ I₂ f, _)⟩,
  dsimp at f,
  by_cases hm : is_bot m,
  { haveI : subsingleton { x // x ≤ m},
    { have hm : ∀ (a : { x // x ≤ m}), a = ⟨a₀, ha₀ _⟩ :=
        λ a, le_antisymm (a.2.trans (hm _)) (ha₀ _),
      exact ⟨λ x y, by rw [hm x, hm y]⟩, },
    refine
    ⟨{ f :=
      { app := λ a, eq_to_hom (by congr) ≫ f ≫ eq_to_hom (by congr),
        naturality' := λ a₁ a₂ φ, begin
          have h₁₂ := subsingleton.elim a₁ a₂,
          subst h₁₂,
          simp only [subsingleton.elim φ (𝟙 _), map_id, id_comp, comp_id],
        end, },
      commτ := λ a b hab, begin
        exfalso,
        rw subsingleton.elim a b at hab,
        simpa only [lt_self_iff_false] using hab.1,
      end, }, _⟩,
    dsimp,
    simp only [comp_id, id_comp], },
  { let X := { x // x < m},
    let R₁ := λ (a : X), (restriction a.1 m a.2.le).obj I₁,
    let R₂ := λ (a : X), (restriction a.1 m a.2.le).obj I₂,
    have h : ∀ (a : X), ∃ (Φ : R₁ a ⟶ R₂ a),
      (eval τ a.1 ⟨a₀, ha₀ _⟩).map Φ = f,
    { intros a,
      haveI := (H a.1 a.2).some,
      apply (eval τ a.1 ⟨a₀, ha₀ _⟩).map_surjective, },
    let Ψ := λ (a : X), (h a).some,
    have hΨ : ∀ (a : X), (Ψ a).f.app ⟨a₀, ha₀ _⟩ = f := λ a, (h a).some_spec,
    have hΨ' : ∀ (a₁ a₂ : X) (ha₁₂ : a₁ ≤ a₂) (b : α) (hb : b ≤ a₁.1),
      (Ψ a₁).f.app ⟨b, hb⟩ = (Ψ a₂).f.app ⟨b, hb.trans ha₁₂⟩,
    { intros a₁ a₂ ha₁₂ b hb,
      exact eval_injective τ ⟨a₀, ha₀ _⟩ (by simpa only [is_bot.of_le_iff] using ha₀)
        I₁ I₂ ⟨a₁.1, a₁.2.le⟩ ⟨a₂.1, a₂.2.le⟩ (Ψ a₁) (Ψ a₂) (by erw [hΨ a₁, hΨ a₂])
        ⟨b, hb.trans a₁.2.le⟩ hb (hb.trans ha₁₂), },
    let m' : { x // x ≤ m} := ⟨m, le_refl m⟩,
    have hm' : is_top m' := λ a, a.2,
    let φ' : order.lt_inclusion_functor m' ⋙ I₁.F ⟶ order.lt_inclusion_functor m' ⋙ I₂.F :=
    { app := by { rintro ⟨⟨a, ha⟩, ha'⟩, exact (Ψ ⟨a, ha'⟩).f.app ⟨a, le_refl _⟩, },
      naturality' := begin
        rintro ⟨⟨a₁, ha₁⟩, ha₁'⟩ ⟨⟨a₂, ha₂⟩, ha₂'⟩ g,
        dsimp,
        rw hΨ' ⟨a₁, ha₁'⟩ ⟨a₂, ha₂'⟩ (le_of_hom g),
        let a₁' : {x // x ≤ a₂} := ⟨a₁, le_of_hom g⟩,
        let a₂' : {x // x ≤ a₂} := ⟨a₂, le_refl _⟩,
        let g' : a₁' ⟶ a₂' := hom_of_le (le_of_hom g),
        exact (Ψ ⟨a₂, ha₂'⟩).f.naturality g',
      end },
    cases is_well_order.two_cases _ hm with hm'' hm'',
    { obtain ⟨m₁, hm₁⟩ := hm'',
      have hm₁' := (order.are_succ.of_le_iff ⟨m₁, hm₁.le⟩ m').2 hm₁,
      let m₁' : { x // x < m'} := ⟨⟨m₁, hm₁.le⟩, hm₁.lt⟩,
      let φm : I₁.F.obj m' ⟶ I₂.F.obj m' := (under.forget _).map (I₁.iso _ _ hm₁').hom ≫
        Φ.map (φ'.app m₁') ≫ (under.forget _).map (I₂.iso _ _ hm₁').inv,
      refine ⟨{ f := hm₁'.mk_nat_trans hm' _ _ φ' φm _, commτ := _, }, _⟩,
      { have eq := τ.naturality (φ'.app m₁'),
        have eq₁ := under.w (I₁.iso _ _ hm₁').hom,
        have eq₂ := under.w (I₂.iso _ _ hm₁').hom,
        have eq₃ := ((under.forget _).map_iso (I₂.iso _ _ hm₁')).hom_inv_id,
        dsimp [φm] at ⊢ eq eq₁ eq₂ eq₃,
        rw [← eq₁, ← eq₂, assoc] at eq,
        slice_lhs 1 3 { rw ← eq, },
        simp only [assoc, eq₃, comp_id], },
      { rintro ⟨a, ha⟩ ⟨b, hb⟩ hab,
        by_cases hb' : b < m,
        { have ha' : a < m := lt_of_le_of_lt hab.le hb',
          rw [hm₁'.mk_nat_trans_eq hm' _ _ _ _ _ ⟨b, hb⟩ hb',
            hm₁'.mk_nat_trans_eq hm' _ _ _ _ _ ⟨a, ha⟩ ha'],
          dsimp [φ'],
          rw [hΨ' ⟨a, ha'⟩ ⟨b, hb'⟩ hab.le a (le_refl _)],
          exact (Ψ ⟨b, hb'⟩).commτ ⟨a, hab.le⟩ ⟨b, le_refl _⟩
            (by simpa only [order.are_succ.of_le_iff] using hab), },
        { have hb'' : m = b := le_antisymm (not_lt.1 hb') hb,
          subst hb'',
          have ha' : m₁ = a := order.are_succ.pred_uniq hm₁ ((order.are_succ.of_le_iff _ _).1 hab),
          subst ha',
          rw [hm₁'.mk_nat_trans_eq' hm', hm₁'.mk_nat_trans_eq hm' _ _ _ _ _ ⟨m₁, ha⟩ hm₁.lt],
          dsimp [φm],
          have eq := ((under.forget _).map_iso (I₂.iso ⟨m₁, ha⟩ ⟨m, hb⟩ hab)).inv_hom_id,
          dsimp at eq,
          simp only [assoc, eq, comp_id], }, },
      { dsimp,
        let a₀' : { x // x ≤ m} := ⟨a₀, ha₀ _⟩,
        have ha₀' : a₀' < m',
        { rw hm₁'.lt_iff_le,
          apply ha₀, },
        rw hm₁'.mk_nat_trans_eq hm' _ _ _ _ _ a₀' ha₀',
        dsimp [φ'],
        rw hΨ, }, },
    { let φm : I₁.F.obj m' ⟶ I₂.F.obj m' := (I₁.hF m'
        ((order.is_limit.of_le_iff m').2 hm'')).desc (cocone.mk (I₂.F.obj m')
          { app := begin
              rintro ⟨⟨a, ha⟩, ha'⟩,
              exact (Ψ ⟨a, ha'⟩).f.app ⟨a, le_refl _⟩ ≫ I₂.F.map (hom_of_le ha),
            end,
            naturality' := begin
              rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩ hab,
              dsimp,
              rw [comp_id, hΨ' ⟨a, ha'⟩ ⟨b, hb'⟩ (le_of_hom hab) a (le_refl _)],
              let a' : { x // x ≤ b} := ⟨a, le_of_hom hab⟩,
              let b' : { x // x ≤ b} := ⟨b, le_refl _⟩,
              let hab' : a' ⟶ b' := hom_of_le a'.2,
              let a'' : {x // x ≤ m} := ⟨a, ha⟩,
              let b'' : {x // x ≤ m} := ⟨b, hb⟩,
              let g : b'' ⟶ m' := hom_of_le hb,
              let hab'' : a'' ⟶ b'' := hab,
              have eq' := subsingleton.elim (hom_of_le ha : a'' ⟶ m') (hab'' ≫ hom_of_le hb),
              rw [eq', I₂.F.map_comp],
              have eq := (Ψ ⟨b, hb'⟩).f.naturality hab' =≫ I₂.F.map g,
              simp only [assoc] at eq,
              convert eq,
            end }),
      refine ⟨{ f := hm'.mk_nat_trans _ _ φ' φm _, commτ := _, }, _⟩,
      { rintro ⟨⟨a, ha⟩, ha'⟩,
        apply (I₁.hF m' ((order.is_limit.of_le_iff m').2 hm'')).fac, },
      { rintro ⟨a, ha⟩ ⟨b, hb⟩ hab,
        have hb' : b < m,
        { by_contra',
          have hb'' := le_antisymm this hb,
          subst hb'',
          simp only [order.are_succ.of_le_iff] at hab,
          exact hm''.2 ⟨_, hab⟩, },
        have ha' : a < m := lt_of_lt_of_le hab.lt hb,
        rw [hm'.mk_nat_trans_eq _ _ _ _ _ ⟨a, ha⟩ ha',
          hm'.mk_nat_trans_eq _ _ _ _ _ ⟨b, hb⟩ hb'],
        dsimp [φ'],
        rw hΨ' ⟨a, ha'⟩ ⟨b, hb'⟩ hab.le a (le_refl _),
        exact (Ψ ⟨b, hb'⟩).commτ ⟨a, _⟩ ⟨b, _⟩
          (by simpa only [order.are_succ.of_le_iff] using hab), },
      { dsimp,
        let a₀' : { x // x ≤ m} := ⟨a₀, ha₀ _⟩,
        have ha₀' : a₀' < m',
        { by_contra',
          apply hm''.1,
          rw ← le_antisymm a₀'.2 this,
          exact ha₀, },
        rw hm'.mk_nat_trans_eq _ _ _ _ _ a₀' ha₀',
        apply hΨ, }, }, },
end

end transfinite_iteration

section

def to_sections_lt_inclusion_functor [partial_order α] (F : αᵒᵖ ⥤ Type v) (a : α) (x : F.obj (opposite.op a)) :
  ((order.lt_inclusion_functor a).op ⋙ F).sections :=
⟨λ b, F.map (hom_of_le b.unop.2.le).op x, begin
  rintro b c f,
  dsimp,
  simpa only [← functor_to_types.map_comp_apply F],
end⟩

variables [linear_order α] [is_well_order α (<)]
  (F : αᵒᵖ ⥤ Type v)
  (hF₁ : ∀ (a b : α) (hab : order.are_succ a b), function.surjective (F.map (hom_of_le hab.le).op))
  (hF₂ : ∀ (a : α) (ha : order.is_limit a), function.surjective (F.to_sections_lt_inclusion_functor a))

namespace surjective_of_is_well_order_of_surjective

structure X :=
(β : set α)
(hβ : ∀ (x y : α) (hxy : x ≤ y) (hy : y ∈ β), x ∈ β)
(s : Π (b : β), F.obj (opposite.op b.1))
(hs : ∀ (b c : β) (h : b ≤ c), s b = F.map (hom_of_le h : b.1 ⟶ c.1).op (s c))

instance : partial_order (X F) :=
{ le := λ σ₁ σ₂, (σ₁.β ⊆ σ₂.β) ∧
    ∀ (b : α) (hb₁ : b ∈ σ₁.β) (hb₂ : b ∈ σ₂.β), σ₁.s ⟨b, hb₁⟩ = σ₂.s ⟨b, hb₂⟩,
  le_refl := by tauto,
  le_trans := λ σ₁ σ₂ σ₃ h₁₂ h₂₃,
    ⟨h₁₂.1.trans h₂₃.1, λ b hb₁ hb₃, (h₁₂.2 b hb₁ (h₁₂.1 hb₁)).trans (h₂₃.2 b (h₁₂.1 hb₁) hb₃)⟩,
  le_antisymm := λ σ₁ σ₂ h₁₂ h₂₁, begin
    rcases σ₁ with ⟨β, hβ, s, hs⟩,
    rcases σ₂ with ⟨β', hβ', s', hs'⟩,
    have eqβ : β = β',
    { ext,
      exact ⟨λ h, h₁₂.1 h, λ h, h₂₁.1 h⟩, },
    subst eqβ,
    simp only [eq_self_iff_true, heq_iff_eq, true_and],
    ext ⟨b, hb⟩,
    exact h₁₂.2 b hb hb,
  end, }

@[simps]
def X.of_is_bot (a₀ : α) (ha₀ : is_bot a₀) (x : F.obj (opposite.op a₀)) :
  X F :=
{ β := { a₀ },
  hβ := λ x y hxy hy, begin
    simp only [set.mem_singleton_iff] at hy ⊢,
    exact le_antisymm (hxy.trans (by rw hy)) (ha₀ _),
  end,
  s := begin
    rintro ⟨b, hb⟩,
    simp only [set.mem_singleton_iff] at hb,
    subst hb,
    exact x,
  end,
  hs := begin
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc,
    simp only [set.mem_singleton_iff] at hb hc,
    substs hb hc,
    dsimp,
    erw [subsingleton.elim (hom_of_le hbc) (𝟙 _), op_id, F.map_id, types_id_apply],
  end, }

@[simp]
lemma X.of_is_bot_s₀ (a₀ : α) (ha₀ : is_bot a₀) (x : F.obj (opposite.op a₀)) :
  (X.of_is_bot F a₀ ha₀ x).s ⟨a₀, rfl⟩ = x := rfl

def X_set (a₀ : α) (ha₀ : is_bot a₀) (x₀ : F.obj (opposite.op a₀)) :=
  { σ : X F | X.of_is_bot F a₀ ha₀ x₀ ≤ σ }

variable {F}

lemma X_set_chain_condition {a₀ : α} {ha₀ : is_bot a₀} {x₀ : F.obj (opposite.op a₀)}
  (C : set (X F)) (hC₁ : C ⊆ X_set F a₀ ha₀ x₀) (hC₂ : is_chain (≤) C) :
  ∃ (m : X F) (hm : m ∈ X_set F a₀ ha₀ x₀), ∀ (z : X F) (hz : z ∈ C), z ≤ m :=
begin
  by_cases hC₀ : nonempty C,
  { let β : set α := λ b, ∃ (c : C), b ∈ c.1.β,
    let γ : β → C := λ b, b.2.some,
    have hγ : ∀ (b : β), b.1 ∈ (γ b).1.β := λ b, b.2.some_spec,
    let s : Π (b : β), F.obj (opposite.op b.val) := λ b, (γ b).1.s ⟨b.1, hγ b⟩,
    have hC₂' : ∀ (z₁ z₂ : C) (b : α) (hb₁ : b ∈ z₁.1.β) (hb₂ : b ∈ z₂.1.β),
      z₁.1.s ⟨b, hb₁⟩ = z₂.1.s ⟨b, hb₂⟩,
    { intros z₁ z₂ b hb₁ hb₂,
      by_cases hz₁₂ : z₁.1 = z₂.1,
      { have hz₁₂' : z₁ = z₂ := by { ext, exact hz₁₂, },
        subst hz₁₂', },
      { cases hC₂ z₁.2 z₂.2 hz₁₂,
        { apply h.2, },
        { symmetry, apply h.2, }, }, },
    have hs : ∀ (z : C) (b : α) (hb : b ∈ z.1.β), s ⟨b, ⟨z, hb⟩⟩ = z.1.s ⟨b, hb⟩,
    { intros s b hb,
      apply hC₂', },
    refine
    ⟨{ β := β,
      hβ := λ b₁ b₂ h₁₂ h₂, begin
        obtain ⟨c, hc⟩ := h₂,
        exact ⟨c, c.1.hβ b₁ _ h₁₂ hc⟩,
      end,
      s := s,
      hs := begin
        rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc,
        let g := γ ⟨c, hc⟩,
        erw [hs g c (hγ _), hs g b (g.1.hβ _ _ hbc (hγ _))],
        exact g.1.hs ⟨b, _⟩ ⟨c, _⟩ hbc,
      end, }, _, _⟩,
    { split,
      { dsimp,
        simp only [set.singleton_subset_iff],
        exact ⟨_, (hC₁ hC₀.some.2).1 rfl⟩, },
      { intros b hb₁ hb₂,
        apply (hC₁ (γ ⟨b, hb₂⟩).2).2, }, },
    { intros z hz,
      split,
      { intros a ha,
        exact ⟨⟨z, hz⟩, ha⟩, },
      { intros b hb₁ hb₂,
        exact (hs ⟨z, hz⟩ b hb₁).symm, }, }, },
  { refine ⟨X.of_is_bot F a₀ ha₀ x₀, le_refl _, _⟩,
    intros z hz,
    exfalso,
    exact hC₀ ⟨⟨z, hz⟩⟩, },
end

section

variables (x : X F) {m : α} (hx : x.β = {a | a < m}) (t : F.obj (opposite.op m))
  (ht : ∀ (b : α) (hb : b < m),
    x.s ⟨b, by simpa only [hx] using hb⟩ = (F.map (hom_of_le hb.le).op) t)

include ht

@[simps]
def X.extension : X F :=
{ β := {a | a ≤ m},
  hβ := λ x y hxy hy, hxy.trans hy,
  s := begin
    rintro ⟨b, hb⟩,
    by_cases b < m,
    { exact x.s ⟨b, by simpa only [hx] using h⟩, },
    { have hb' := le_antisymm (not_lt.1 h) hb,
      subst hb',
      exact t, },
  end,
  hs := begin
    rintro ⟨b, hb⟩ ⟨c, hc⟩ (hbc : b ≤ c),
    dsimp,
    by_cases hc' : c < m,
    { have hb' : b < m := lt_of_le_of_lt hbc hc',
      rw [dif_pos hb', dif_pos hc'],
      exact x.hs ⟨b, by simpa only [hx] using hb'⟩ ⟨c, by simpa only [hx] using hc'⟩ hbc, },
    { replace hc' : m = c := le_antisymm (not_lt.1 hc') hc,
      subst hc',
      by_cases hb' : b < m,
      { dsimp,
        simp only [dif_pos hb', lt_self_iff_false, not_false_iff, dif_neg],
        apply ht, },
      { replace hb' : m = b := le_antisymm (not_lt.1 hb') hb,
        subst hb',
        dsimp,
        simp only [lt_self_iff_false, not_false_iff, dif_neg,
          subsingleton.elim (hom_of_le hbc) (𝟙 _), op_id, F.map_id, types_id_apply], }, },
  end, }

lemma X.le_extension : x < X.extension x hx t ht :=
begin
  have hx' : x ≠ X.extension x hx t ht,
  { intro h,
    rw ← lt_self_iff_false m,
    change m ∈ { x | x < m},
    rw [← hx, h],
    apply le_refl, },
  suffices : x ≤ X.extension x hx t ht,
  { cases this.lt_or_eq,
    { exact h, },
    { exfalso,
      refine hx' h, }, },
  split,
  { dsimp,
    simp only [hx, set.set_of_subset_set_of],
    intros a ha,
    exact ha.le, },
  { intros b hb₁ hb₂,
    have hb₁' : b < m := by simpa only [hx] using hb₁,
    dsimp,
    rw dif_pos hb₁', },
end

end

end surjective_of_is_well_order_of_surjective

include hF₁ hF₂

open surjective_of_is_well_order_of_surjective

lemma surjective_of_is_well_order_of_surjective' (a₀ : α) (ha₀ : is_bot a₀):
  function.surjective (λ (s : F.sections), s.1 (opposite.op a₀)) :=
λ x₀, begin
  obtain ⟨m, hm₀ : X.of_is_bot F a₀ ha₀ x₀ ≤ m, hm⟩ :=
    zorn_partial_order₀ (X_set F a₀ ha₀ x₀) (by apply X_set_chain_condition),
  suffices : m.β = ⊤,
  { have hm' : ∀ (b : α), b ∈ m.β := λ b, by simp only [this, set.top_eq_univ],
    refine ⟨⟨λ b, m.s ⟨b.unop, hm' _⟩, _⟩, _⟩,
    { intros b c f,
      have eq := m.hs ⟨c.unop, hm' _⟩ ⟨b.unop, hm' _⟩ (le_of_hom f.unop),
      convert eq.symm, },
    { dsimp,
      simp only [← hm₀.2 a₀ (by simp) (hm' _), X.of_is_bot_s], }, },
  replace hm : ∀ (z : X F) (hz : m ≤ z), z = m := λ z hz, hm z (hm₀.trans hz) hz,
  by_contra' hm',
  replace hm' : (m.βᶜ : set α).nonempty,
  { simp only [set.nonempty_iff_ne_empty],
    intro h,
    apply hm',
    rw [← compl_compl m.β, h, set.compl_empty, set.top_eq_univ], },
  let b := @well_founded.min α (<) is_well_founded.wf _ hm',
  have hb : m.β = { x | x < b},
  { have hb' : b ∈ m.βᶜ := well_founded.min_mem _ _ _,
    ext a,
    split,
    { intro ha,
      dsimp,
      by_contra',
      exact hb' (m.hβ _ _ this ha), },
    { intro ha,
      dsimp at ha,
      by_contra ha',
      have ha'' : ¬ (a < b):= well_founded.not_lt_min _ _ _ ha',
      exact ha'' ha, }, },
  rcases is_well_order.three_cases b with h₁ | (h₂ | h₃),
  { rw is_bot.unique h₁ ha₀ at hb,
    have ha₀' : a₀ ∉ m.β,
    { simp only [hb, set.mem_set_of_eq, lt_self_iff_false, not_false_iff], },
    apply ha₀',
    apply hm₀.1,
    simp only [X.of_is_bot_β, set.mem_singleton], },
  { obtain ⟨a, hab⟩ := h₂,
    have ha' : a ∈ m.β := by simpa only [hb] using hab.lt,
    obtain ⟨t, ht⟩ := hF₁ _ _ hab (m.s ⟨a, ha'⟩),
    let M := X.extension m hb t (λ c hc, begin
      rw hab.lt_iff_le at hc,
      rw m.hs ⟨c, m.hβ _ _ hc ha'⟩ ⟨a, ha'⟩ hc,
      have eq := congr_arg (F.map (hom_of_le hc).op) ht,
      simp only [← functor_to_types.map_comp_apply] at eq,
      convert eq.symm,
    end),
    have hM : m < M := X.le_extension _ _ _ _,
    simpa only [hm M hM.le, lt_self_iff_false] using hM, },
  { obtain ⟨t, ht⟩ := hF₂ _ h₃ ⟨λ c, m.s ⟨c.unop.1, by simpa only [hb] using c.unop.2⟩,
      (λ c d hcd, (m.hs ⟨d.unop.1, _⟩ ⟨c.unop.1, _⟩ _).symm)⟩,
    let M := X.extension m hb t (λ c hc,
      congr_fun (congr_arg subtype.val ht.symm) (opposite.op ⟨c, hc⟩)),
    have hM : m < M := X.le_extension _ _ _ _,
    simpa only [hm M hM.le, lt_self_iff_false] using hM, },
end

lemma surjective_of_is_well_order_of_surjective [order_bot α] :
  function.surjective (λ (s : F.sections), s.1 (opposite.op ⊥)) :=
surjective_of_is_well_order_of_surjective' F hF₁ hF₂ ⊥ (order_bot.bot_le)

end

section

variables {m : α} [linear_order α] (F : { x // x < m } ⥤ C) (X : C)
  (φ : F ⟶ (functor.const _).obj X)

namespace order_extension_from_lt_to_le

include F X

def obj (a : { x // x ≤ m}) : C :=
begin
  by_cases a.1 < m,
  { exact F.obj ⟨a.1, h⟩, },
  { exact X, },
end

def obj_iso_of_lt (a : { x // x ≤ m}) (ha : a.1 < m) :
  obj F X a ≅ F.obj ⟨a.1, ha⟩ :=
eq_to_iso begin
  dsimp [obj],
  classical,
  erw [dif_pos ha],
end

def obj_iso_of_not_lt (a : { x // x ≤ m}) (ha : ¬ a.1 < m) :
  obj F X a ≅ X :=
eq_to_iso begin
  dsimp [obj],
  erw [dif_neg ha],
end

end order_extension_from_lt_to_le

open order_extension_from_lt_to_le

include φ

def order_extension_from_lt_to_le : { x // x ≤ m } ⥤ C :=
{ obj := order_extension_from_lt_to_le.obj F X,
  map := λ a b f, begin
    classical,
    by_cases ha : a.1 < m,
    { by_cases hb : b.1 < m,
      { exact (obj_iso_of_lt F X a ha).hom ≫ F.map (hom_of_le (by exact le_of_hom f)) ≫
          (obj_iso_of_lt F X b hb).inv, },
      { exact (obj_iso_of_lt F X a ha).hom ≫ φ.app ⟨a, ha⟩ ≫ (obj_iso_of_not_lt F X b hb).inv, }, },
    { exact (obj_iso_of_not_lt F X a ha).hom ≫ (obj_iso_of_not_lt F X b
        (by { simp only [not_lt] at ⊢ ha, exact ha.trans (le_of_hom f), })).inv, },
  end,
  map_id' := λ a, begin
    by_cases ha : a.1 < m,
    { simp only [dif_pos ha],
      have h := le_refl (⟨a.1, ha⟩ : { x // x < m}),
      rw [subsingleton.elim (hom_of_le h) (𝟙 _), functor.map_id, id_comp, iso.hom_inv_id], },
    { simp only [dif_neg ha, iso.hom_inv_id], },
  end,
  map_comp' := λ a b c f g, begin
    by_cases ha : a.1 < m,
    { by_cases hb : b.1 < m,
      { by_cases hc : c.1 < m,
        { simp only [dif_pos ha, dif_pos hb, dif_pos hc, assoc, iso.inv_hom_id_assoc,
            iso.cancel_iso_hom_left, ← F.map_comp_assoc],
          congr, },
        { simp only [dif_pos ha, dif_pos hb, dif_neg hc, assoc, iso.inv_hom_id_assoc,
            iso.cancel_iso_hom_left],
          let f' : (⟨a, ha⟩ : { x // x < m}) ⟶ ⟨b, hb⟩ := f,
          have eq := φ.naturality f',
          dsimp at eq,
          rw comp_id at eq,
          simp only [← eq, assoc],
          congr, }, },
      { have hc : ¬c.1 < m := λ h, hb (lt_of_le_of_lt (le_of_hom g) h),
        simp only [dif_pos ha, dif_neg hb, dif_neg hc, assoc, iso.inv_hom_id_assoc], } },
    { have hb : ¬b.1 < m := λ h, ha (lt_of_le_of_lt (le_of_hom f) h),
      have hc : ¬c.1 < m := λ h, hb (lt_of_le_of_lt (le_of_hom g) h),
      simp only [dif_neg ha, dif_neg hb, dif_neg hc, assoc, iso.inv_hom_id_assoc], },
  end, }

end

@[simps]
def nat_trans_to_functor_const [preorder α] (F : α ⥤ C) (m : α) (hm : is_top m) :
  F ⟶ (functor.const _).obj (F.obj m) :=
{ app := λ a, F.map (hom_of_le (hm a)),
  naturality' := λ a b hab, begin
    dsimp,
    simpa only [comp_id, ← F.map_comp],
  end, }

namespace transfinite_iteration

variables (τ) [linear_order α] [is_well_order α (<)] {m : α} (a₀ : { b : α // b ≤ m})
  (ha₀ : is_bot a₀)

def mk_of_is_bot (hm : is_bot m) (X : C) : transfinite_iteration τ m :=
{ F := (functor.const _).obj X,
  hF := λ b hb, begin
    exfalso,
    exact hb.1 (by simpa only [is_bot.of_le_iff] using (hm.of_le _ b.2)),
  end,
  iso := begin
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab,
    exfalso,
    rw order.are_succ.of_le_iff at hab,
    dsimp at hab,
    have ha' := is_bot.unique (hm.of_le _ ha) hm,
    have hb' := is_bot.unique (hm.of_le _ hb) hm,
    substs ha' hb',
    simpa only [lt_self_iff_false] using hab.lt,
  end, }

def mk_of_are_succ {a b : α} (hab : order.are_succ a b) (I : transfinite_iteration τ a) :
  transfinite_iteration τ b :=
begin
  let a' : { x // x < b} := ⟨a, hab.lt⟩,
  have ha' : is_top a' := λ c, (hab.lt_iff_le c.1).1 c.2,
  let i : { x // x < b } → { x // x ≤ a } := λ x, ⟨x.1, ha' _⟩,
  have hi : _root_.monotone i := λ x y hxy, hxy,
  exact
  { F := order_extension_from_lt_to_le (monotone.functor hi ⋙ I.F)
      (Φ.obj (I.F.obj ⟨a, le_refl a⟩))
      (functor.nat_trans_to_functor_const _ a' ha' ≫ (functor.const _).map (τ.app _)),
    hF := sorry,
    iso := sorry, }
end

variable (m)

include ha₀

lemma ess_surj_eval_zero : ess_surj (eval τ m a₀) :=
begin
  rcases a₀ with ⟨a₀, ha₁⟩,
  rw is_bot.of_le_iff at ha₀,
  apply @well_founded.induction α (<) is_well_founded.wf
    (λ b, ess_surj (eval τ b ⟨a₀, ha₀ _⟩)) m,
  intros b H,
  rcases is_well_order.three_cases b with h₁ | (h₂ | h₃),
  { have hb := is_bot.unique h₁ ha₀,
    subst hb,
    exact ⟨λ X₀, ⟨mk_of_is_bot τ ha₀ X₀, ⟨iso.refl _⟩⟩⟩, },
  { obtain ⟨a, hab⟩ := h₂,
    haveI := H a hab.lt,
    exact ⟨λ X₀, ⟨mk_of_are_succ τ hab ((eval τ a ⟨a₀, ha₀ _⟩).obj_preimage X₀),
      ⟨order_extension_from_lt_to_le.obj_iso_of_lt _ _ _ (lt_of_le_of_lt (ha₀ _) hab.lt) ≪≫
      ((eval τ a ⟨a₀, ha₀ _⟩).obj_obj_preimage_iso _)⟩⟩⟩, },
  { sorry, },
end

end transfinite_iteration

end functor

end category_theory
