/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a
import for_mathlib.algebra.homology.double
import for_mathlib.algebra.homology.k_projective
import category_theory.filtered
import for_mathlib.algebra.homology.homology_sequence

noncomputable theory

open category_theory category_theory.category algebraic_topology
  category_theory.limits

variables {C : Type*} [category C]

namespace category_theory

namespace functor

section

variables {J : Type*} [category J] (F : J ⥤ C) [is_filtered J]

open is_filtered

def is_eventually_constant_from (i : J) : Prop :=
∀ (j : J) (f : i ⟶ j), is_iso (F.map f)

lemma is_eventually_constant_from.of_map {i i' : J} (g : i ⟶ i')
  (hi : F.is_eventually_constant_from i) :
  F.is_eventually_constant_from i' :=
λ j f, begin
  haveI : is_iso (F.map (g ≫ f)) := hi _ _,
  haveI : is_iso (F.map g) := hi _ _,
  exact is_iso.of_is_iso_fac_left (F.map_comp g f).symm,
end

class is_eventually_constant : Prop :=
(condition [] : ∃ (i : J), F.is_eventually_constant_from i)

namespace is_eventually_constant

variable [is_eventually_constant F]

def index : J :=
  (is_eventually_constant.condition F).some

instance {j : J} (f : index F ⟶ j) :
  is_iso (F.map f) := (is_eventually_constant.condition F).some_spec j f

lemma map_from_index_eq {j : J} (f₁ f₂ : index F ⟶ j) :
  F.map f₁ = F.map f₂ :=
begin
  haveI : is_iso (F.map (coeq_hom f₁ f₂)) := begin
    have eq := F.map_comp f₁ (coeq_hom f₁ f₂),
    exact is_iso.of_is_iso_fac_left eq.symm,
  end,
  simp only [← cancel_mono (F.map (coeq_hom f₁ f₂)), ← F.map_comp],
  exact F.congr_map (coeq_condition f₁ f₂),
end

lemma map_is_iso {j₁ j₂ : J} (g : j₁ ⟶ j₂) (f₁ : index F ⟶ j₁) :
  is_iso (F.map g) :=
is_iso.of_is_iso_fac_left (F.map_comp f₁ g).symm


lemma map_eq {j j' : J} (f₁ f₂ : j ⟶ j') (g : index F ⟶ j') :
  F.map f₁ = F.map f₂ :=
begin
  haveI : is_iso (F.map (coeq_hom f₁ f₂)) := map_is_iso F _ g,
  simp only [← cancel_mono (F.map (coeq_hom f₁ f₂)), ← F.map_comp, coeq_condition],
end

@[simps]
def cocone : cocone F :=
{ X := F.obj (index F),
  ι :=
  { app := λ j, F.map (left_to_max j (index F)) ≫
        category_theory.inv (F.map (right_to_max j (index F))),
    naturality' := λ j j' g, begin
      let k := (is_filtered.max j (index F)),
      let k' := (is_filtered.max j' (index F)),
      let m := is_filtered.max k k',
      have eq := map_from_index_eq F (right_to_max _ _ ≫ (left_to_max _ _ : _ ⟶ m))
        (right_to_max _ _ ≫ (right_to_max _ _ : _ ⟶ m)),
      simp only [F.map_comp] at eq,
      haveI : is_iso (F.map (right_to_max k k')) := map_is_iso F _ (right_to_max _ _),
      erw [const_obj_map, comp_id, ← cancel_mono (F.map (right_to_max _ _ : _ ⟶ k')),
        assoc, assoc, is_iso.inv_hom_id, comp_id, ← cancel_mono (F.map (right_to_max k k')),
        assoc, assoc, assoc, ← eq, is_iso.inv_hom_id_assoc, ← F.map_comp, ← F.map_comp,
        ← F.map_comp],
      exact map_eq F _ _ (right_to_max _ _ ≫ right_to_max _ _),
    end }, }

lemma cocone_ι_app_eq {j : J} (g : index F ⟶ j) :
  (cocone F).ι.app j = category_theory.inv (F.map g) :=
begin
  dsimp,
  let h := coeq_hom (g ≫ left_to_max _ (index F)) (right_to_max _ _),
  haveI : is_iso (F.map h) := map_is_iso F _ (right_to_max _ _),
  simpa only [← cancel_epi (F.map g), is_iso.hom_inv_id, assoc, is_iso.hom_inv_id_assoc,
    ← cancel_mono (F.map (right_to_max j (index F))), is_iso.inv_hom_id, comp_id,
    ← cancel_mono (F.map h), F.map_comp]
    using F.congr_map (coeq_condition (g ≫ left_to_max _ (index F)) (right_to_max _ _)),
end

@[simp]
lemma cocone_ι_app_index :
  (cocone F).ι.app (index F) = 𝟙 _ :=
begin
  simp only [cocone_ι_app_eq F (𝟙 (index F)), F.map_id],
  dsimp,
  simp only [is_iso.inv_id],
end

def cocone_is_colimit : is_colimit (cocone F) :=
{ desc := λ s, s.ι.app (index F),
  fac' := λ s j, begin
    dsimp,
    have eq := s.ι.naturality (right_to_max j (index F)),
    dsimp at eq,
    rw comp_id at eq,
    rw [← eq, assoc, is_iso.inv_hom_id_assoc, cocone.w],
  end,
  uniq' := λ s m hm, by simpa only [cocone_ι_app_index, id_comp] using hm (index F), }

@[priority 100]
instance : has_colimit F :=
⟨⟨⟨_, cocone_is_colimit F⟩⟩⟩

lemma is_iso_cocone_ι_app' (j : J) (g : index F ⟶ j) : is_iso (colimit.ι F j) :=
begin
  haveI : is_iso ((cocone F).ι.app j),
  { rw cocone_ι_app_eq F g,
    apply_instance, },
  exact is_iso.of_is_iso_fac_right
    (limits.colimit.comp_cocone_point_unique_up_to_iso_inv (cocone_is_colimit F) j),
end

lemma is_iso_colimit_ι_app (i : J) (hi : F.is_eventually_constant_from i) :
  is_iso (colimit.ι F i) :=
begin
  haveI : is_iso (F.map (left_to_max i (index F))) := hi _ _,
  haveI : is_iso (colimit.ι F (is_filtered.max i (index F))) :=
    is_iso_cocone_ι_app' _ _ (right_to_max _ _),
  rw ← colimit.w F (left_to_max i (index F)),
  apply_instance,
end

end is_eventually_constant

end

variables {X : ℕ → C} (φ : Π n, X n ⟶ X (n+1))

namespace mk_of_sequence

lemma congr_φ (n n' : ℕ) (h : n = n') :
  φ n = eq_to_hom (by rw h) ≫ φ n' ≫ eq_to_hom (by rw h) :=
by { subst h, simp only [eq_to_hom_refl, comp_id, id_comp], }

def f_aux (n : ℕ) : Π (k : ℕ), X n ⟶ X (n+k)
|0 := eq_to_hom (by rw add_zero)
|(k+1) := f_aux k ≫ φ (n+k) ≫ eq_to_hom (by rw add_assoc)

lemma congr_f_aux (n k k' : ℕ) (h : k = k') :
  f_aux φ n k = f_aux φ n k' ≫ eq_to_hom (by rw h) :=
by { subst h, simp only [eq_to_hom_refl, comp_id], }

lemma congr_f_aux' (n n' k k' : ℕ) (hn : n = n') (hk : k = k') :
  f_aux φ n k = eq_to_hom (by rw hn) ≫ f_aux φ n' k' ≫ eq_to_hom (by rw [hn, hk]) :=
by { substs hn hk, simp only [eq_to_hom_refl, comp_id, id_comp], }

def f (n n' : ℕ) (h : n ≤ n') : X n ⟶ X n' :=
f_aux φ n (n'-n) ≫ eq_to_hom (by { congr', linarith, })

lemma congr_f (n₁ n₂ n₂' : ℕ) (h : n₁ ≤ n₂) (h₂ : n₂ = n₂') :
  f φ n₁ n₂ h = f φ n₁ n₂' (h.trans (by rw h₂)) ≫ eq_to_hom (by rw h₂) :=
by { subst h₂, rw [eq_to_hom_refl, comp_id], }

lemma f_eq_f_aux_comp_eq_to_hom (n n' r : ℕ) (h : n' = n+r) :
  f φ n n' (nat.le.intro h.symm)= f_aux φ n r ≫ eq_to_hom (by rw h) :=
begin
  have hr : r = n'-n := by simp only [h, add_tsub_cancel_left],
  subst hr,
  refl,
end

@[simp]
lemma f_eq_id (n : ℕ) : f φ n n (by refl) = 𝟙 _ :=
begin
  rw f_eq_f_aux_comp_eq_to_hom φ n n 0 (add_zero n).symm,
  dsimp [f_aux],
  rw comp_id,
end

lemma f_comp_next (n₁ n₂ n₃ : ℕ) (h : n₁ ≤ n₂) (hn₃ : n₃ = n₂+1) :
  f φ n₁ n₃ (h.trans (by simpa only [hn₃] using nat.le_succ n₂)) =
    f φ n₁ n₂ h ≫ φ n₂ ≫ eq_to_hom (by rw hn₃) :=
begin
  rw le_iff_exists_add at h,
  obtain ⟨r, rfl⟩ := h,
  rw [f_eq_f_aux_comp_eq_to_hom φ n₁ (n₁+r) r rfl,
    f_eq_f_aux_comp_eq_to_hom φ n₁ n₃ (r+1) (by linarith)],
  unfold f_aux,
  simpa only [eq_to_hom_refl, comp_id, assoc],
end

lemma f_next (n₁ n₂ : ℕ) (h : n₂ = n₁+1) :
  f φ n₁ n₂ (by simpa only [h] using nat.le_succ n₁) = φ n₁ ≫ eq_to_hom (by rw h) :=
by simp only [f_comp_next φ n₁ n₁ n₂ (by refl) h, f_eq_id, id_comp]

lemma f_comp (n₁ n₂ n₃ : ℕ) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃) :
  f φ n₁ n₂ h₁₂ ≫ f φ n₂ n₃ h₂₃ = f φ n₁ n₃ (h₁₂.trans h₂₃) :=
begin
  rw le_iff_exists_add at h₂₃,
  obtain ⟨r, rfl⟩ := h₂₃,
  induction r with r hr,
  { simp only [congr_f φ n₂ (n₂ + 0) n₂ (by linarith) (add_zero n₂),
      congr_f φ n₁ (n₂ + 0) n₂ (by linarith) (add_zero n₂),
      f_eq_id, eq_to_hom_refl, comp_id], },
  { simp only [f_comp_next φ n₂ (n₂+r) (n₂+r.succ) (by linarith) rfl,
      f_comp_next φ n₁ (n₂+r) (n₂+r.succ) (by linarith) rfl,
      reassoc_of (hr (by linarith))], },
end

lemma is_iso_f (n₁ n₂ : ℕ) (h₁₂ : n₁ ≤ n₂)
  (H : ∀ (p : ℕ) (hp : n₁ ≤ p) (hp' : p < n₂), is_iso (φ p)) :
  is_iso (f φ n₁ n₂ h₁₂) :=
begin
  rw le_iff_exists_add at h₁₂,
  unfreezingI { obtain ⟨r, rfl⟩ := h₁₂, },
  unfreezingI { induction r with r hr, },
  { simp only [congr_f φ n₁ (n₁+0) n₁ (by linarith) (by linarith),
      f_eq_id, eq_to_hom_refl, comp_id],
    apply_instance, },
  { rw congr_f φ n₁ (n₁+r.succ) (n₁+r+1) (by linarith)
      (by { rw nat.succ_eq_add_one, linarith, }),
    rw ← f_comp φ n₁ (n₁+r) (n₁+r+1) (by linarith) (by linarith),
    haveI := H (n₁+r) (by linarith) (by { rw nat.succ_eq_add_one, linarith, }),
    haveI : is_iso (f φ (n₁+r) (n₁+r+1) (by linarith)),
    { rw f_next φ _ _ rfl, apply_instance, },
    haveI := hr (by linarith) (λ p hp hp', H p hp (by { rw nat.succ_eq_add_one, linarith, })),
    apply_instance, },
end

variable (ψ : Π (n₀ n₁ : ℕ) (h : n₁ = n₀+1), X n₀ ⟶ X n₁)

@[simp]
def restriction (n : ℕ) : X n ⟶ X (n+1) := ψ n (n+1) rfl

lemma f_of_restriction (n₀ n₁ : ℕ) (h : n₁ = n₀ + 1) :
  f (restriction ψ) n₀ n₁ (by simpa only [h] using nat.le_succ n₀) = ψ n₀ n₁ h :=
begin
  subst h,
  simp only [restriction, f_next _ n₀ (n₀+1) rfl, eq_to_hom_refl, comp_id],
end

end mk_of_sequence

@[simps]
def mk_of_sequence : ℕ ⥤ C :=
{ obj := X,
  map := λ n₁ n₂ g, mk_of_sequence.f φ n₁ n₂ (le_of_hom g),
  map_id' := mk_of_sequence.f_eq_id _,
  map_comp' := λ n₁ n₂ n₃ g g', (mk_of_sequence.f_comp φ n₁ n₂ n₃ _ _).symm, }

end functor

variables {X Z : C} (f : X ⟶ Z)

structure hom_factorisation :=
(Y : C)
(i : X ⟶ Y)
(p : Y ⟶ Z)
(fac' : i ≫ p = f . obviously)

namespace hom_factorisation

restate_axiom fac'
attribute [simp, reassoc] fac

variables {f} (F₁ F₂ F₃ : hom_factorisation f)

@[ext]
structure hom :=
(τ : F₁.Y ⟶ F₂.Y)
(commi' : F₁.i ≫ τ = F₂.i . obviously)
(commp' : τ ≫ F₂.p = F₁.p . obviously)

namespace hom

restate_axiom commi'
restate_axiom commp'
attribute [simp, reassoc] commi commp

end hom

instance : category (hom_factorisation f) :=
{ hom := hom,
  id := λ F, { τ := 𝟙 _, },
  comp := λ F₁ F₂ F₃ φ φ', { τ := φ.τ ≫ φ'.τ, }, }

variable (f)

def eval : hom_factorisation f ⥤ C :=
{ obj := λ F, F.Y,
  map := λ F₁ F₂ φ, φ.τ, }

variable {f}

@[simp] lemma id_τ (F : hom_factorisation f) : hom.τ (𝟙 F) = 𝟙 _ := rfl
@[simp, reassoc] lemma comp_τ {F₁ F₂ F₃ : hom_factorisation f} (φ : F₁ ⟶ F₂) (φ' : F₂ ⟶ F₃) :
  (φ ≫ φ').τ = φ.τ ≫ φ'.τ := rfl

lemma eq_to_hom_τ {F₁ F₂ : hom_factorisation f} (eq : F₁ = F₂) :
  hom.τ (eq_to_hom eq) = eq_to_hom (by rw eq) := by { subst eq, refl, }

lemma is_iso_τ {F₁ F₂ : hom_factorisation f} (φ : F₁ ⟶ F₂) [is_iso φ] :
  is_iso φ.τ :=
begin
  change is_iso ((eval f).map φ),
  apply_instance,
end

end hom_factorisation

end category_theory

open category_theory

variables [abelian C] [enough_projectives C]

namespace bounded_above_cochain_complex

namespace projective_model_structure

namespace CM5b

variables {X Z : bounded_above_cochain_complex C} {f : X ⟶ Z}

instance (n : ℤ) [is_iso f] : is_iso (f.f n) :=
begin
  change is_iso ((homological_complex.eval _ _ n).map ((induced_functor _).map f)),
  apply_instance,
end

structure is_cof_fib_factorisation (F : hom_factorisation f) : Prop :=
(hi : arrow_classes.cof F.i)
(hp : arrow_classes.fib F.p)

variable (f)

@[derive category]
def cof_fib_factorisation := full_subcategory (@is_cof_fib_factorisation _ _ _ _ _ _ f)

@[simps]
def cof_fib_factorisation.forget : cof_fib_factorisation f ⥤ hom_factorisation f :=
full_subcategory_inclusion _

@[simps]
def cof_fib_factorisation.eval (n : ℤ) : cof_fib_factorisation f ⥤ C :=
cof_fib_factorisation.forget f ⋙ hom_factorisation.eval f ⋙
  bounded_above_cochain_complex.ι ⋙ (homological_complex.eval C (complex_shape.up ℤ) n)

variable {f}

def cof_fib_factorisation.quasi_iso_ge (F : cof_fib_factorisation f) (n : ℤ) : Prop :=
  ∀ (i : ℤ) (hi : n ≤ i), is_iso (homology_map F.1.p i)

variable (f)

@[derive category]
def cof_fib_factorisation_quasi_iso_ge (n : ℤ) :=
  full_subcategory (λ (F : cof_fib_factorisation f), F.quasi_iso_ge n)

variable {f}

def cof_fib_factorisation.is_iso_ge (F : cof_fib_factorisation f) (n : ℤ) : Prop :=
  ∀ (i : ℤ) (hi : n ≤ i), is_iso (F.1.i.f i)

namespace induction

variables (f) (hf : arrow_classes.fib f)

include hf

lemma step₁ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf' : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₁) (hF₂ : F.quasi_iso_ge n₁),
    epi (homology_map (F.1.p) n₀) :=
begin
  let Y : bounded_above_cochain_complex C :=
    ⟨homological_complex.biprod X.1
      ((homological_complex.single C (complex_shape.up ℤ) n₀).obj
        (projective.over (Z.1.cycles n₀))),
    sorry⟩,
  let i : X ⟶ Y := homological_complex.biprod.inl,
  let p : Y ⟶ Z := homological_complex.biprod.desc f
    (cochain_complex.desc_single _ _ ((homological_complex.single_obj_X_self _ _ _ _).hom ≫
    projective.π _ ≫ Z.1.cycles_i n₀) (n₀+1) rfl
      (by simp only [assoc, homological_complex.cycles_i_d, comp_zero])),
  refine
  ⟨⟨{ Y := Y,
    i := i,
    p := p,
    fac' := homological_complex.biprod.inl_desc _ _, },
    { hi := _, hp := _ }⟩, _, _, _⟩,
  sorry { intro n,
    refine ⟨_, _, biprod.snd, ⟨⟨biprod.fst, biprod.inr,
      ⟨biprod.inl_fst, biprod.inr_snd, biprod.inl_snd, biprod.inr_fst, biprod.total⟩⟩⟩⟩,
    by_cases n = n₀,
    { subst h,
      exact projective.of_iso (homological_complex.single_obj_X_self C _ _ _).symm
        infer_instance, },
    { dsimp [homological_complex.single],
      rw if_neg h,
      apply_instance, }, },
  sorry { intro n,
    change epi (p.f n),
    haveI : epi (biprod.inl ≫ p.f n),
    { dsimp [p],
      rw biprod.inl_desc,
      exact hf n, },
    exact epi_of_epi biprod.inl (p.f n), },
  sorry { intros n hn,
    refine ⟨⟨biprod.fst, biprod.inl_fst, eq.symm _⟩⟩,
    dsimp,
    rw [← biprod.total, add_right_eq_self],
    convert comp_zero,
    apply is_zero.eq_of_src,
    rw if_neg,
    { apply is_zero_zero, },
    { linarith, }, },
  { sorry, },
  { sorry, },
end

lemma step₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf' : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q))
  (hf'' : epi (homology_map f n₀)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₀),
    F.quasi_iso_ge n₀ := sorry

lemma step₁₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf' : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q)) :
  ∃ (F : cof_fib_factorisation f) (hF : F.is_iso_ge n₁),
    F.quasi_iso_ge n₀ :=
begin
  obtain ⟨F₁, hF₁, hF₂, hp⟩ := step₁ f hf n₀ n₁ hn₁ hf',
  obtain ⟨F₂, hF₂, hF₂'⟩ := step₂ F₁.1.p F₁.2.hp n₀ n₁ hn₁ hF₂ hp,
  let F : cof_fib_factorisation f :=
  ⟨{ Y := F₂.1.Y,
    i := F₁.1.i ≫ F₂.1.i,
    p := F₂.1.p, },
  { hi := cof_stable_under_composition _ _ F₁.2.hi F₂.2.hi,
    hp := F₂.2.hp, }⟩,
  refine ⟨F, _, hF₂'⟩,
  { intros i hi,
    dsimp [F],
    haveI := hF₁ i hi,
    haveI : is_iso (F₂.obj.i.f i) := hF₂ i (by linarith),
    erw homological_complex.comp_f,
    apply_instance, },
end

lemma step' (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (F : cof_fib_factorisation_quasi_iso_ge f n₁) :
  ∃ (F' : cof_fib_factorisation_quasi_iso_ge f n₀) (φ : F.obj.obj ⟶ F'.obj.obj),
    ∀ (i : ℤ) (hi : n₁ ≤ i), is_iso ((hom_factorisation.hom.τ φ).f i) :=
begin
  obtain ⟨G, hG, hG'⟩ := step₁₂ F.1.1.p F.1.2.hp n₀ n₁ hn₁ F.2,
  let F' : cof_fib_factorisation f :=
  ⟨{ Y := G.1.Y,
    i :=  F.1.1.i ≫ G.1.i,
    p := G.1.p, },
  { hi := cof_stable_under_composition _ _ F.1.2.hi G.2.hi,
    hp := G.2.hp, }⟩,
  exact ⟨⟨F', hG'⟩, { τ := G.1.i, }, hG⟩,
end

variables {n₀ : ℤ} (F₀ : cof_fib_factorisation_quasi_iso_ge f n₀)

def step (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (F₁ : cof_fib_factorisation_quasi_iso_ge f n₁) :
  cof_fib_factorisation_quasi_iso_ge f n₀ :=
(step' f hf n₀ n₁ hn₁ F₁).some

def step_map (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (F₁ : cof_fib_factorisation_quasi_iso_ge f n₁) :
  F₁.obj.obj ⟶ (step f hf n₀ n₁ hn₁ F₁).obj.obj :=
(step' f hf n₀ n₁ hn₁ F₁).some_spec.some

lemma is_iso_step_map_τ_f (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (F₁ : cof_fib_factorisation_quasi_iso_ge f n₁) (i : ℤ) (hi : n₁ ≤ i) :
  is_iso ((hom_factorisation.hom.τ (step_map f hf n₀ n₁ hn₁ F₁)).f i) :=
(step' f hf n₀ n₁ hn₁ F₁).some_spec.some_spec i hi

noncomputable def sequence : Π (k : ℕ), cof_fib_factorisation_quasi_iso_ge f (n₀-k)
| 0 := ⟨F₀.1, λ i hi, F₀.2 i (by simpa using hi)⟩
| (k+1) := step f hf _ _ (by { simp only [nat.cast_add, algebra_map.coe_one],linarith, })
    (sequence k)

def sequence_next_step_iso (k₀ k₁ : ℕ) (h : k₁ = k₀ + 1) :
  (step f hf (n₀ - ↑k₁) (n₀ - ↑k₀) (by { subst h, simp only [nat.cast_add,
    algebra_map.coe_one, sub_add_eq_sub_sub, sub_add_cancel], })
    (sequence f hf F₀ k₀)).obj ≅
  (sequence f hf F₀ k₁).obj :=
eq_to_iso (by { subst h, unfold sequence, })

instance (k₀ k₁ : ℕ) (h : k₁ = k₀ + 1) :
  is_iso ((sequence_next_step_iso f hf F₀ k₀ k₁ h).hom.τ) :=
is_iso.of_iso ((cof_fib_factorisation.forget f ⋙
  hom_factorisation.eval f).map_iso (sequence_next_step_iso f hf F₀ k₀ k₁ h))

lemma congr_sequence_obj (k k' : ℕ) (h : k = k') :
  (sequence f hf F₀ k).obj = (sequence f hf F₀ k').obj :=
by subst h

def sequence_map_next (k₀ k₁ : ℕ) (h : k₁ = k₀ + 1) :
  (sequence f hf F₀ k₀).obj ⟶ (sequence f hf F₀ k₁).obj :=
step_map f hf (n₀-k₁) (n₀-k₀) (by linarith) _ ≫
  (sequence_next_step_iso f hf F₀ k₀ k₁ h).hom

lemma is_iso_sequence_map_next_τ_f (k₀ k₁ : ℕ )(h : k₁ = k₀ + 1) (n : ℤ) (hn : n₀ - k₀ ≤ n) :
  is_iso ((sequence_map_next f hf F₀ k₀ k₁ h).τ.f n) :=
begin
  unfold sequence_map_next,
  haveI := is_iso_step_map_τ_f f hf (n₀-k₁) _ (by linarith) (sequence f hf F₀ k₀) n hn,
  erw [homological_complex.comp_f],
  apply_instance,
end

def inductive_system : ℕ ⥤ cof_fib_factorisation f :=
functor.mk_of_sequence (functor.mk_of_sequence.restriction (sequence_map_next f hf F₀))

def inductive_system' : ℕ ⥤ cochain_complex C ℤ :=
inductive_system f hf F₀ ⋙ cof_fib_factorisation.forget f ⋙ hom_factorisation.eval f ⋙
  bounded_above_cochain_complex.ι

lemma is_iso_inductive_system'_comp_eval_map_next (k₀ k₁ : ℕ ) (h : k₁ = k₀ + 1) (n : ℤ)
  (hn : n₀ - k₀ ≤ n) :
  is_iso ((inductive_system' f hf F₀ ⋙ homological_complex.eval C (complex_shape.up ℤ) n).map
    (hom_of_le (nat.le.intro h.symm))) :=
begin
  dsimp [inductive_system', inductive_system, hom_factorisation.eval, ι],
  rw [functor.mk_of_sequence.f_next _ k₀ k₁ h],
  simp only [functor.mk_of_sequence.restriction, functor.map_comp, eq_to_hom_map,
    hom_factorisation.comp_τ, hom_factorisation.eq_to_hom_τ],
  erw [homological_complex.comp_f, hom_factorisation.eq_to_hom_τ,
    homological_complex.eq_to_hom_f],
  { haveI := is_iso_sequence_map_next_τ_f f hf F₀ k₀ _ rfl n hn,
    apply_instance, },
  all_goals { rw congr_sequence_obj, linarith, },
end

lemma is_iso_inductive_system'_comp_eval_map (k₀ k₁ : ℕ) (h : k₀ ≤ k₁) (n : ℤ)
  (hn : n₀ - k₀ ≤ n) :
  is_iso ((inductive_system' f hf F₀ ⋙ homological_complex.eval C (complex_shape.up ℤ) n).map
    (hom_of_le h)) :=
begin
  rw le_iff_exists_add at h,
  obtain ⟨r, rfl⟩ := h,
  induction r with r hr,
  { haveI : is_iso (hom_of_le h) :=
      ⟨⟨hom_of_le (by refl), subsingleton.elim _ _ , subsingleton.elim _ _⟩⟩,
    apply_instance, },
  { have h₁ : k₀ ≤ k₀ + r := by linarith,
    have h₂ : k₀ + r ≤ k₀ + r.succ := by { rw nat.succ_eq_add_one, linarith, },
    have eq : _ = hom_of_le h := hom_of_le_comp h₁ h₂,
    simp only [← eq, functor.map_comp],
    exact @is_iso.comp_is_iso _ _ _ _ _ _ _ (hr h₁)
      (is_iso_inductive_system'_comp_eval_map_next f hf F₀ (k₀+r) (k₀+r.succ)
          (by { rw nat.succ_eq_add_one, linarith, }) _
          (by { simp only [nat.cast_add, tsub_le_iff_right], linarith, })), },
end

lemma inductive_system'_comp_eval_is_eventually_constant_from (n : ℤ) :
  ((inductive_system' f hf F₀) ⋙
    homological_complex.eval _ _ n).is_eventually_constant_from (n₀-n).truncate :=
λ p hp, is_iso_inductive_system'_comp_eval_map _ _ _ _ _ (le_of_hom hp) _
  (by linarith [int.self_le_coe_truncate (n₀-n)])

instance inductive_system'_comp_eval_is_eventually_constant (n : ℤ) :
  ((inductive_system' f hf F₀) ⋙
    homological_complex.eval _ _ n).is_eventually_constant :=
⟨⟨_, inductive_system'_comp_eval_is_eventually_constant_from f hf F₀ n⟩⟩

lemma is_iso_colimit_ι_inductive_system'_f (k : ℕ) (n : ℤ) (hn : n₀-k ≤ n) :
  is_iso ((colimit.ι (inductive_system' f hf F₀) k).f n) :=
begin
  have ineq : (n₀-n).truncate ≤ k,
  { by_cases n ≤ n₀,
    { simp only [← int.coe_nat_le_coe_nat_iff, int.coe_truncate (n₀-n) (by linarith)],
      linarith, },
    { simpa only [int.truncate_eq_zero (n₀-n) (by linarith)] using zero_le', }, },
  haveI := functor.is_eventually_constant.is_iso_colimit_ι_app
    ((inductive_system' f hf F₀) ⋙ homological_complex.eval _ _ n) k
    (functor.is_eventually_constant_from.of_map _
      (hom_of_le ineq) (inductive_system'_comp_eval_is_eventually_constant_from f hf F₀ n)),
  exact is_iso.of_is_iso_fac_right ((ι_preserves_colimits_iso_hom (homological_complex.eval _ _ n)
      (inductive_system' f hf F₀) k)),
end

@[simps]
def factorisation_Y : bounded_above_cochain_complex C :=
⟨colimit (inductive_system' f hf F₀),
begin
  obtain ⟨ny, hny⟩ := F₀.obj.obj.Y.2,
  have h₂ := le_max_right ny n₀,
  refine ⟨max ny n₀, λ i hi, _⟩,
  haveI := is_iso_colimit_ι_inductive_system'_f f hf F₀ 0 i
    (by simpa only [algebra_map.coe_zero, tsub_zero]
      using (lt_of_le_of_lt (le_max_right _ _) hi).le),
  exact limits.is_zero.of_iso (hny _ (lt_of_le_of_lt (le_max_left _ _) hi))
    (as_iso ((limits.colimit.ι (inductive_system' f hf F₀) 0).f i)).symm,
end⟩

@[simps]
def factorisation_i : X ⟶ factorisation_Y f hf F₀ :=
F₀.obj.obj.i ≫ colimit.ι (inductive_system' f hf F₀) 0

@[simp]
def factorisation_p : factorisation_Y f hf F₀ ⟶ Z :=
colimit.desc (inductive_system' f hf F₀) (cocone.mk Z.obj
{ app := λ n, ((inductive_system f hf F₀).obj n).obj.p,
  naturality' := λ n n' φ, begin
    dsimp,
    rw comp_id,
    exact ((inductive_system f hf F₀).map φ).commp,
  end, })

@[simps]
def factorisation : cof_fib_factorisation f :=
⟨{ Y := factorisation_Y f hf F₀,
  i := factorisation_i f hf F₀,
  p := factorisation_p f hf F₀,
  fac' := begin
    dsimp only [factorisation_i, factorisation_p],
    simp only [assoc],
    erw colimit.ι_desc,
    dsimp only,
    exact ((inductive_system f hf F₀).obj 0).1.fac,
  end, },
  { hi := λ n, begin
      let k := (n₀-n).truncate,
      dsimp [ι],
      haveI := is_iso_colimit_ι_inductive_system'_f f hf F₀ k n
        (by linarith [int.self_le_coe_truncate (n₀-n)]),
      have eq : F₀.obj.obj.i.f n ≫ (limits.colimit.ι (inductive_system' f hf F₀) 0).f n =
        ((inductive_system f hf F₀).obj k).obj.i.f n ≫
        (limits.colimit.ι (inductive_system' f hf F₀) k).f n,
      { simpa only [← homological_complex.comp_f,
          ← colimit.w (inductive_system' f hf F₀) (hom_of_le (zero_le' : 0 ≤ k)), ← assoc,
          ← ((inductive_system f hf F₀).map (hom_of_le (zero_le' : 0 ≤ k))).commi],},
      rw eq,
      exact preadditive.mono_with_projective_coker.is_stable_by_composition
        _ _ _ (((inductive_system f hf F₀).obj k).2.hi n)
          (preadditive.mono_with_projective_coker.of_is_iso _),
    end,
    hp := λ n, begin
      dsimp [ι],
      let k := (n₀-n).truncate,
      haveI := is_iso_colimit_ι_inductive_system'_f f hf F₀ k n
        (by linarith [int.self_le_coe_truncate (n₀-n)]),
      rw [← epi_comp_left_iff_epi ((limits.colimit.ι (inductive_system' f hf F₀) k).f n),
        ← homological_complex.comp_f, colimit.ι_desc],
      exact ((inductive_system f hf F₀).obj k).2.hp n,
    end, }⟩

lemma quasi_iso_factorisation_p (n : ℤ) :
  quasi_iso (ι.map (factorisation f hf F₀).1.p) :=
⟨λ n, begin
  let k := (n₀+1-n).truncate,
  have hk := int.self_le_coe_truncate (n₀+1-n),
  have eq : homology_map (colimit.ι (inductive_system' f hf F₀) k) n ≫
    homology_map (factorisation f hf F₀).obj.p n =
      homology_map ((inductive_system f hf F₀).obj k).obj.p n,
  { rw ← homology_map_comp,
    congr' 1,
    apply colimit.ι_desc _ _, },
  haveI : is_iso (homology_map ((inductive_system f hf F₀).obj k).obj.p n) :=
    (sequence f hf F₀ k).2 n (by linarith),
  haveI : is_iso (homology_map (limits.colimit.ι (inductive_system' f hf F₀) k) n),
  { let φ := (homological_complex.short_complex_functor C _ n).map
      ((limits.colimit.ι (inductive_system' f hf F₀) k)),
    change is_iso ((short_complex.homology_functor C).map φ),
    haveI : is_iso φ.τ₁,
    { apply is_iso_colimit_ι_inductive_system'_f,
      rw cochain_complex.prev,
      linarith, },
    haveI : is_iso φ.τ₂,
    { apply is_iso_colimit_ι_inductive_system'_f,
      linarith, },
    haveI : is_iso φ.τ₃,
    { apply is_iso_colimit_ι_inductive_system'_f,
      rw cochain_complex.next,
      linarith, },
    haveI := short_complex.is_iso_of_isos φ,
    apply_instance, },
  exact is_iso.of_is_iso_fac_left eq,
end⟩

end induction

lemma for_fibration {X Z : bounded_above_cochain_complex C} (f : X ⟶ Z)
  (hf : arrow_classes.fib f) :
  ∃ (Y : bounded_above_cochain_complex C) (i : X ⟶ Y)
    (hi : arrow_classes.cof i) (p : Y ⟶ Z)
    (hp : arrow_classes.triv_fib p), f = i ≫ p :=
begin
  obtain ⟨nx, hnx⟩ := X.2,
  obtain ⟨ny, hny⟩ := Z.2,
  haveI : X.obj.is_strictly_le nx := ⟨hnx⟩,
  haveI : Z.obj.is_strictly_le ny := ⟨hny⟩,
  let n₀ := max (nx+1) (ny+1),
  have hnx' : nx + 1 ≤ n₀ := le_max_left _ _,
  have hny' : ny + 1 ≤ n₀ := le_max_right _ _,
  let F₀ : cof_fib_factorisation_quasi_iso_ge f n₀ :=
  ⟨⟨{ Y := X,
    i := 𝟙 _,
    p := f, },
  { hi := λ n, preadditive.mono_with_projective_coker.id_mem _,
    hp := hf, }⟩,
    λ i hi, ⟨⟨0,
      limits.is_zero.eq_of_src (cochain_complex.is_le.is_zero _ nx _ (by linarith)) _ _,
      limits.is_zero.eq_of_src (cochain_complex.is_le.is_zero _ ny _ (by linarith)) _ _⟩⟩⟩,
  let F := induction.factorisation f hf F₀,
  exact ⟨_, _, F.2.hi, _,
    ⟨F.2.hp,
      ⟨λ n, by { haveI := induction.quasi_iso_factorisation_p f hf F₀ n, apply_instance, }⟩⟩,
    F.1.fac.symm⟩,
end

end CM5b

lemma CM5b : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5b :=
λ X Z f, begin
  obtain ⟨X', j, hj, q, hq, rfl⟩ := projective_model_structure.CM5a f,
  obtain ⟨Y, i, hi, p, hp, rfl⟩ := CM5b.for_fibration q hq,
  exact ⟨Y, j ≫ i, cof_stable_under_composition j i hj.1 hi, p, hp, by rw assoc⟩,
end

lemma CM5 : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5 :=
  ⟨CM5a, CM5b⟩

end projective_model_structure

end bounded_above_cochain_complex
