/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a
import for_mathlib.algebra.homology.trunc
import for_mathlib.algebra.homology.k_projective

noncomputable theory

open category_theory category_theory.category algebraic_topology

universes v u

variables {C : Type u} [category.{v} C]

namespace category_theory

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
  (hf : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₁) (hF₂ : F.quasi_iso_ge n₁),
    epi (homology_map (F.1.p) n₀) := sorry

lemma step₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q))
  (hf' : epi (homology_map f n₀)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₀),
    F.quasi_iso_ge n₀ := sorry

lemma step₁₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf : ∀ (q : ℤ) (hq : n₁ ≤ q), is_iso (homology_map f q)) :
  ∃ (F : cof_fib_factorisation f) (hF : F.is_iso_ge n₁),
    F.quasi_iso_ge n₀ :=
begin
  obtain ⟨F₁, hF₁, hF₂, hp⟩ := step₁ f n₀ n₁ hn₁ hf,
  obtain ⟨F₂, hF₂, hF₂'⟩ := step₂ F₁.1.p n₀ n₁ hn₁ hF₂ hp,
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
  obtain ⟨G, hG, hG'⟩ := step₁₂ F.1.1.p n₀ n₁ hn₁ F.2,
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
    (sequence f hf F₀ k₀)).obj.obj ≅
  (sequence f hf F₀ k₁).obj.obj :=
eq_to_iso (by { subst h, unfold sequence, })

instance (k₀ k₁ : ℕ) (h : k₁ = k₀ + 1)  :
  is_iso ((sequence_next_step_iso f hf F₀ k₀ k₁ h).hom.τ) :=
hom_factorisation.is_iso_τ _

def sequence_map (k₀ k₁ : ℕ) (h : k₁ = k₀ + 1) :
  (sequence f hf F₀ k₀).obj.obj ⟶ (sequence f hf F₀ k₁).obj.obj :=
step_map f hf (n₀-k₁) (n₀-k₀) (by linarith) _ ≫
  (sequence_next_step_iso f hf F₀ k₀ k₁ h).hom

lemma is_iso_sequence_map_τ_f (k₀ k₁ : ℕ )(h : k₁ = k₀ + 1) (n : ℤ) (hn : n₀ - k₀ ≤ n) :
  is_iso ((sequence_map f hf F₀ k₀ k₁ h).τ.f n) :=
begin
  unfold sequence_map,
  haveI := is_iso_step_map_τ_f f hf (n₀-k₁) _ (by linarith) (sequence f hf F₀ k₀) n hn,
  erw [homological_complex.comp_f],
  apply_instance,
end

include F₀

def factorisation : cof_fib_factorisation f :=
begin
  sorry,
end

lemma quasi_iso_factorisation_p (n : ℤ) :
  quasi_iso (ι.map (factorisation f hf F₀).1.p) := sorry

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
