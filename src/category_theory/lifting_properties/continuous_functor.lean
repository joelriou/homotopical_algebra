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

@[simps]
def functor.well_order_cocone : limits.cocone (functor.well_order_inclusion_functor h ⋙ F) :=
{ X := F.obj h.top,
  ι :=
  { app := λ b, F.map (hom_of_le (le_of_lt (by { dsimp, rw h.down, use b, }))),
    naturality' := λ b₁ b₂ hb, by { dsimp, simpa only [← F.map_comp, category.comp_id], }, }, }

omit h

/-- add the assumption that β has no maximum and is not empty... -/
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

noncomputable
instance : inhabited (⊤_ (Type v)) :=
by { let φ := terminal.from (ulift.{v} (fin 1)), exact ⟨φ (ulift.up 0)⟩ }

instance : subsingleton (⊤_ (Type v)) :=
⟨λ x₁ x₂, begin
  let φ₁ : ulift (fin 1) ⟶ ⊤_ (Type v) := λ z, x₁,
  let φ₂ : ulift (fin 1) ⟶ ⊤_ (Type v) := λ z, x₂,
  have eq := subsingleton.elim φ₁ φ₂,
  exact congr_fun eq (ulift.up 0),
end⟩

lemma induction_principle (x₀ : X.obj (opposite.op ⊥))
  (hX : ∀ (b : α) (hb : b ≠ ⊥), function.surjective (restriction X b)) :
  ∃ (S : solutions X), S.app (opposite.op ⊥) = λ n, x₀ :=
begin
  let A := { o : set α // ⊥ ∈ o ∧ ∀ (x y : α) (hxy : x ≤ y) (hy : y ∈ o), x ∈ o },
  let incl : Π (o : A), o.1 → α := λ o x, x.1,
  have hincl : ∀ (o : A), monotone (incl o) := λ o a b h, h,
  let ι : Π (o : A), o.1 ⥤ α := λ o, monotone.functor (hincl o),
  let n : ⊤_ (Type v) := arbitrary _,
  let B := sigma (λ (o : A), (functor.const o.1ᵒᵖ).obj (terminal (Type v)) ⟶ (ι o).op ⋙ X),
  have extB : ∀ (b₁ b₂ : B) (h₁ : b₁.1.1 = b₂.1.1) (h₂ : ∀ (a : α) (ha₁ : a ∈ b₁.1.1)
    (ha₂ : a ∈ b₂.1.1), b₁.2.app (opposite.op ⟨a, ha₁⟩) n = b₂.2.app (opposite.op ⟨a, ha₂⟩) n),
    b₁ = b₂,
  { intros b₁ b₂ h₁ h₂,
    rcases b₁ with ⟨o₁, t₁⟩,
    rcases b₂ with ⟨o₂, t₂⟩,
    dsimp at h₁ h₂,
    rw ← subtype.ext_iff at h₁,
    subst h₁,
    simp only [eq_self_iff_true, heq_iff_eq, true_and],
    ext a m,
    induction a using opposite.rec,
    rcases a with ⟨a₁, a₂⟩,
    have hm := subsingleton.elim n m,
    subst hm,
    exact h₂ a₁ a₂ a₂, },
  let ρ : B → B → Prop := λ t₁ t₂, t₁.1.1 ⊆ t₂.1.1 ∧ Π (h₁ : t₁.1.1 ⊆ t₂.1.1),
    ∀ (a : t₁.1.1), t₁.2.app (opposite.op a) n = t₂.2.app (opposite.op ⟨a.1, h₁ a.2⟩) n,
  let b : B,
  { refine ⟨⟨{⊥}, ⟨set.mem_singleton _, λ x y hxy hy,
      by { dsimp at hy, simpa only [hy, ← eq_bot_iff] using hxy, }⟩⟩, _⟩,
    exact
    { app := λ a z, begin
        refine X.map _ x₀,
        suffices : (opposite.unop a).1 ≤ ⊥,
        { exact (hom_of_le this).op, },
        rw set.eq_of_mem_singleton (a.unop.2),
      end,
      naturality' := λ a₁ a₂ φ, begin
        induction a₁ using opposite.rec,
        induction a₂ using opposite.rec,
        have eq₁ : a₁ = a₂,
        { ext,
          have h₁ := set.eq_of_mem_singleton (a₁.2),
          have h₂ := set.eq_of_mem_singleton (a₂.2),
          simp only [subtype.val_eq_coe] at h₁ h₂,
          rw [h₁, h₂], },
        subst eq₁,
        have eq₂ := subsingleton.elim φ (𝟙 _),
        subst eq₂,
        dsimp,
        erw [category.id_comp, X.map_id, category.comp_id],
      end, }, },
  have hb : is_chain ρ {b} := set.subsingleton.is_chain set.subsingleton_singleton,
  rcases hb.exists_max_chain with ⟨M, ⟨hM₁, hM₂⟩⟩,
  have h : ∀ (x : α), ∃ (m : M), x ∈ m.1.1.1,
  { by_contra',
    let Z := { x : α | ∀ (m : M), ¬ x ∈ m.1.1.1 },
    have hZ : Z.nonempty := ⟨this.some, this.some_spec⟩,
    have hZ₀ : ¬ ⊥ ∈ Z,
    { dsimp [Z],
      simp only [set_coe.forall, subtype.coe_mk, sigma.forall, subtype.forall,
        not_forall, set.not_not_mem, exists_prop, exists_and_distrib_right],
      exact ⟨{⊥}, ⟨⟨⟨set.mem_singleton _, λ x y hxy hy,
        by { dsimp at hy, simpa only [hy, ← eq_bot_iff] using hxy, }⟩,
        ⟨b.2, hM₂ (set.mem_singleton _)⟩⟩, set.mem_singleton _⟩⟩, },
    let wf : well_founded ((<) : α → α → Prop) := is_well_founded.wf,
    let μ := wf.min Z hZ,
    have hμ : μ ≠ ⊥,
    { intro hμ',
      rw ← hμ' at hZ₀,
      exact hZ₀ (wf.min_mem Z hZ), },
    have hβ : ∀ (a : α) (ha : a < μ), ∃ (m : M), a ∈ m.1.1.1,
    { intros a ha,
      by_contra' ha',
      change a ∈ Z at ha',
      have ha'' : μ ≤ a := wf.min_le ha',
      exact (lt_self_iff_false μ).mp (lt_of_le_of_lt ha'' ha), },
    let Y := { a : α // a < μ },
    have H : ∃ (φ : Y → M), ∀ (a : Y), a.1 ∈ (φ a).1.1.1 :=
      ⟨λ a, (hβ a.1 a.2).some, λ a, (hβ a.1 a.2).some_spec⟩,
    rcases H with ⟨φ, hφ⟩,
    let app' := λ (a : Y), (φ a).1.2.app (opposite.op ⟨a.1, hφ a⟩) n,
    have compat : ∀ (a : Y) (m : M) (hm : a.1 ∈ m.1.1.1),
      m.1.2.app (opposite.op ⟨a.1, hm⟩) n = app' a,
    { intro a,
      suffices : ∀ (m₁ m₂ : M) (hm₁ : a.1 ∈ m₁.1.1.1) (hm₂ : a.1 ∈ m₂.1.1.1),
        m₁.1.2.app (opposite.op ⟨a.1, hm₁⟩) n = m₂.1.2.app (opposite.op ⟨a.1, hm₂⟩) n,
      { intros m hm,
        exact this m (φ a) hm (hφ a), },
      suffices : ∀ (m₁ m₂ : M) (hm₁ : a.1 ∈ m₁.1.1.1) (hm₂ : a.1 ∈ m₂.1.1.1) (h₁₂ : ρ m₁ m₂),
        m₁.1.2.app (opposite.op ⟨a.1, hm₁⟩) n = m₂.1.2.app (opposite.op ⟨a.1, hm₂⟩) n,
      { intros m₁ m₂ hm₁ hm₂,
        by_cases m₁ = m₂,
        { subst h, },
        { rw subtype.ext_iff at h,
          rcases hM₁.is_chain m₁.2 m₂.2 h with (h'|h'),
          { exact this m₁ m₂ hm₁ hm₂ h', },
          { exact (this m₂ m₁ hm₂ hm₁ h').symm, }, }, },
      intros m₁ m₂ hm₁ hm₂ h₁₂,
      exact h₁₂.2 h₁₂.1 ⟨a.1, hm₁⟩, },
    let s : compatible_system X μ :=
    { app := λ a z, app' a.unop,
      naturality' := λ a₂ a₁ ψ, begin
        ext m,
        have hm := subsingleton.elim n m,
        subst hm,
        induction a₁ using opposite.rec,
        induction a₂ using opposite.rec,
        dsimp,
        have ha : ∃ (m : M), a₁.1 ∈ m.1.1.1 ∧ a₂.1 ∈ m.1.1.1,
        { by_cases φ a₁ = φ a₂,
          { exact ⟨φ a₁, ⟨hφ a₁, by { rw h, exact hφ a₂, }⟩⟩, },
          { have h' : (φ a₁).1 ≠ (φ a₂).1 := λ h'', h (subtype.ext_iff.mpr h''),
            cases hM₁.is_chain (φ a₁).2 (φ a₂).2 h' with h'' h'',
            { exact ⟨φ a₂, ⟨h''.1 (hφ a₁), hφ a₂⟩⟩, },
            { exact ⟨φ a₁, ⟨hφ a₁, h''.1 (hφ a₂)⟩⟩, }, }, },
        rcases ha with ⟨m, hm₁, hm₂⟩,
        rw [← compat a₁ m hm₁, ← compat a₂ m hm₂],
        let a₁' : m.1.1.1 := ⟨a₁.1, hm₁⟩,
        let a₂' : m.1.1.1 := ⟨a₂.1, hm₂⟩,
        let α : a₁' ⟶ a₂' := ψ.unop,
        exact congr_fun (m.1.2.naturality α.op) n,
      end, },
    cases hX μ hμ s with x hx,
    let o : A := ⟨{ y : α | y ≤ μ }, ⟨bot_le, λ x y hxy hy, hxy.trans hy⟩⟩,
    let b : B := ⟨o,
      { app := λ a z, X.map (hom_of_le a.unop.2).op x,
        naturality' := λ a₁ a₂ ψ, by { ext m, dsimp, rw X_map_comp, }, }⟩,
    have hμ' : μ ∈ Z := wf.min_mem Z hZ,
    have hZ' : ∀ (a₁ a₂ : α) (h : a₁ ≤ a₂), a₂ ∉ Z → a₁ ∉ Z,
    { intros a₁ a₂ h h₂,
      dsimp at h₂,
      simp only [not_forall, set.not_not_mem] at h₂,
      cases h₂ with m hm,
      intro ha₁,
      exact ha₁ m (m.1.1.2.2 _ _ h hm), },
    have hb : is_chain ρ (insert b M) := hM₁.is_chain.insert (λ b' hb'₁ hb'₂, or.inr begin
      split,
      { intros a,
        by_contra',
        exact hZ' μ a (le_of_lt (not_le.mp this.2)) (λ ha, ha ⟨b', hb'₁⟩ this.1) hμ', },
      { intro h₁,
        have compat' : ∀ (a : b'.1.1) (ha : a.1 < μ), b'.2.app (opposite.op a) n =
          b.2.app (opposite.op ⟨a.1, h₁ a.2⟩) n,
        { rintro ⟨a, ha⟩ ha',
          have eq := congr_fun (nat_trans.congr_app hx (opposite.op ⟨a, ha'⟩)) n,
          have eq' := compat ⟨a, ha'⟩ ⟨b', hb'₁⟩ ha,
          exact eq'.trans eq.symm, },
        intro a,
        dsimp,
        cases eq_or_lt_of_le (h₁ a.2),
        { exfalso,
          apply hb'₂,
          apply extB,
          { ext c,
            split,
            { intro hc,
              exact b'.1.2.2 _ _ hc (by { rw ← h, exact a.2, }), },
            { intro hc,
              exact h₁ hc, }, },
          { intros c hc₁ hc₂,
            suffices : c < μ,
            { exact (compat' ⟨c, hc₂⟩ this).symm, },
            by_contra',
            exact hZ' _ _ this (λ hc, hc ⟨b', hb'₁⟩ hc₂) hμ', }, },
        { exact compat' a h, }, },
    end),
    have hb' : super_chain ρ M (insert b M) := begin
      refine ⟨hb, ⟨set.subset_insert _ _, _⟩⟩,
      intro hb'',
      have hμ'' := hμ' ⟨b, hb'' (set.mem_insert _ _)⟩,
      dsimp at hμ'',
      apply hμ'',
      refl,
    end,
    exact hM₁.not_super_chain hb', },
  have H : ∃ (φ : α → M), ∀ (a : α), a ∈ (φ a).1.1.1,
  { refine ⟨λ a, (h a).some, λ a, (h a).some_spec⟩, },
  rcases H with ⟨φ, hφ⟩,
  let app' := λ (a : α), (φ a).1.2.app (opposite.op ⟨a, hφ a⟩) n,
  have compat'' : ∀ (a : α) (m : M) (hm : a ∈ m.1.1.1), m.1.2.app (opposite.op ⟨a, hm⟩) n = app' a,
  { intro a,
    suffices : ∀ (m₁ m₂ : M) (hm₁ : a ∈ m₁.1.1.1) (hm₂ : a ∈ m₂.1.1.1),
      m₁.1.2.app (opposite.op ⟨a, hm₁⟩) = m₂.1.2.app (opposite.op ⟨a, hm₂⟩),
    { intros m hm,
      exact congr_fun (this m (φ a) hm (hφ a)) n, },
      /- duplicates ? -/
    suffices : ∀ (m₁ m₂ : M) (hm₁ : a ∈ m₁.1.1.1) (hm₂ : a ∈ m₂.1.1.1) (h₁₂ : ρ m₁ m₂),
      m₁.1.2.app (opposite.op ⟨a, hm₁⟩) = m₂.1.2.app (opposite.op ⟨a, hm₂⟩),
    { intros m₁ m₂ hm₁ hm₂,
      by_cases m₁ = m₂,
      { subst h, },
      { rw subtype.ext_iff at h,
        rcases hM₁.is_chain m₁.2 m₂.2 h with (h'|h'),
        { exact this m₁ m₂ hm₁ hm₂ h', },
        { exact (this m₂ m₁ hm₂ hm₁ h').symm, }, }, },
    intros m₁ m₂ hm₁ hm₂ h₁₂,
    ext m,
    have hm := subsingleton.elim n m,
    subst hm,
    exact h₁₂.2 h₁₂.1 ⟨a, hm₁⟩, },
  refine ⟨{ app := λ a z, app' a.unop,
    naturality' := λ a₂ a₁ ψ, begin
      ext m,
      have hm := subsingleton.elim n m,
      subst hm,
      induction a₁ using opposite.rec,
      induction a₂ using opposite.rec,
      have hψ : a₁ ≤ a₂ := le_of_hom ψ.unop,
      dsimp,
      rw [← compat'' a₂ (φ a₂) (hφ a₂), ← compat'' a₁ (φ a₂) ((φ a₂).1.1.2.2 _ _ hψ (hφ a₂))],
      let X : (φ a₂).1.1.1 := ⟨a₁, (φ a₂).1.1.2.2 _ _ hψ (hφ a₂)⟩,
      let Y : (φ a₂).1.1.1 := ⟨a₂, hφ a₂⟩,
      let γ : X ⟶ Y := hom_of_le hψ,
      convert congr_fun ((φ a₂).val.snd.naturality γ.op) n,
    end }, _⟩,
  { ext m,
    have hm := subsingleton.elim n m,
    subst hm,
    dsimp,
    rw ← compat'' ⊥ ⟨b, hM₂ (set.mem_singleton b)⟩ rfl,
    dsimp,
    have eq : 𝟙 (⊥ : α) = hom_of_le rfl.le := subsingleton.elim _ _,
    simpa only [← eq, op_id, X.map_id], },
end

end

@[simp]
lemma hom_of_le_self_eq_id (a : α) : hom_of_le (show a ≤ a, by refl) = 𝟙 a := subsingleton.elim _ _

@[simp]
lemma hom_of_le_le_of_hom {a b : α} (f : a ⟶ b) : hom_of_le (le_of_hom f) = f := subsingleton.elim _ _


lemma min_eq {α : Type*} [linear_order α] [H : is_well_order α (<)]
  (s : set α) (hs : s.nonempty) (m : α) (hm₁ : m ∈ s) (hm₂ : ∀ (b : α), b ∈ s → m ≤ b) :
  H.wf.min s hs = m :=
le_antisymm (H.wf.min_le hm₁) (hm₂ _ (H.wf.min_mem s hs))

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
  let U : αᵒᵖ ⥤ Type v :=
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
  let x₀ : U.obj (opposite.op ⊥) :=
  { l := f,
    fac_left' := by { dsimp, rw [hom_of_le_self_eq_id, F.map_id, category.id_comp], },
    fac_right' := sq.w, },
  let n : ⊤_ (Type v) := arbitrary _,
  cases induction_principle U x₀ _ with L hL,
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
  { intros b hb s,
    by_cases ∃ (b₀ : α) (h₀ : b₀ < b), ∀ (a : α), a < b → a ≤ b₀,
    { rcases h with ⟨b₀, h₀, h₁⟩,
      let L := (s.app (opposite.op ⟨b₀, h₀⟩) n),
      have H := hF₂ b₀ p hp,
      let e : arrow.mk (F.map (hom_of_le (le_succ b₀))) ≅ arrow.mk (F.map (hom_of_le (le_of_lt h₀))) :=
        arrow.iso_mk' (F.map (hom_of_le (le_succ b₀))) (F.map (hom_of_le (le_of_lt h₀))) (iso.refl _)
          (F.map_iso (eq_to_iso begin
            dsimp [well_founded.succ],
            rw dif_pos,
            { refine min_eq _ ⟨b, h₀⟩ _ h₀ _,
              intros b₁ hb₁,
              by_contra',
              exact not_lt.mpr (h₁ _ this) hb₁, },
          end)) begin
            simp only [iso.refl_hom, category.id_comp, functor.map_iso_hom, eq_to_iso.hom, ← F.map_comp],
            congr,
          end,
      rw has_lifting_property.iff_of_arrow_iso_left e at H,
      haveI := H,
      have S : comm_sq L.l (F.map (hom_of_le (le_of_lt h₀))) p (c.ι.app b ≫ g),
      { apply comm_sq.mk,
        simp only [L.fac_right, cocone.w_assoc], },
      let t : U.obj (opposite.op b) :=
      { l := S.lift,
        fac_left' := begin
          conv_rhs { rw [← L.fac_left, ← S.fac_left, ← F.map_comp_assoc], },
          congr,
        end,
        fac_right' := S.fac_right, },
      refine ⟨t, _⟩,
      ext d m,
      dsimp at m,
      have hm := subsingleton.elim n m,
      subst hm,
      dsimp [restriction],
      have pif := S.fac_left,
      dsimp [L] at pif,
      have foo := (s.app d n).fac_left,
      let φ : d.unop ⟶ ⟨b₀, h₀⟩ := hom_of_le (h₁ d.unop.1 d.unop.2),
      have eq := congr_fun (s.naturality φ.op) n,
      rw comm_sq.lift_struct.ext_iff at eq,
      dsimp at eq,
      conv_rhs { rw [eq, ← S.fac_left, ← F.map_comp_assoc], },
      congr, },
    { let β := {a : α // a < b},
      let B := @principal_seg.mk _ _ ((<) : β → β → Prop) ((<) : α → α → Prop)
        (subtype.rel_embedding _ _) b begin
        intro c,
        split,
        { intro hc,
          exact ⟨⟨c, hc⟩, rfl⟩, },
        { intro hc,
          cases hc with d hd,
          rw ← hd,
          exact d.2, },
      end,
      let d₀ : β := ⟨⊥, begin
        rcases (bot_le : ⊥ ≤ b).eq_or_lt with (h₁|h₂),
        { exfalso,
          exact hb h₁.symm, },
        { exact h₂, },
      end⟩,
      let Co : cocone (functor.well_order_inclusion_functor B ⋙ F) := cocone.mk X
        { app := λ d, (s.app (opposite.op d) n).l,
          naturality' := λ b₁ b₂ φ, begin
            dsimp [functor.well_order_inclusion_functor],
            have hφ := congr_fun (s.naturality φ.op) n,
            dsimp at hφ,
            simpa only [category.comp_id, hφ],
          end, },
      let t : U.obj (opposite.op b) :=
      { l := (hF₁ β B).desc Co,
        fac_left' := begin
          dsimp,
          conv_rhs { rw ← (s.app (opposite.op d₀) n).fac_left, },
          have h₀ := (hF₁ β B).fac Co d₀,
          dsimp [functor.well_order_cocone] at h₀,
          rw [← h₀, ← F.map_comp_assoc],
          congr,
        end,
        fac_right' := begin
          apply (hF₁ β B).hom_ext,
          intro d,
          rw [is_colimit.fac_assoc, (s.app (opposite.op d) n).fac_right,
            functor.well_order_cocone_ι_app],
          dsimp,
          simpa only [cocone.w_assoc],
        end, },
      use t,
      ext a m,
      rw ← subsingleton.elim n m,
      exact (hF₁ β B).fac Co a.unop, }, },
end⟩

end morphism_property

end category_theory
