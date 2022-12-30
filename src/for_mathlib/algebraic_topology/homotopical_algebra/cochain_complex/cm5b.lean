/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.algebraic_topology.homotopical_algebra.cochain_complex.cm5a

open category_theory category_theory.category algebraic_topology

variables {C : Type*} [category C]

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

@[simp] lemma id_τ (F : hom_factorisation f) : hom.τ (𝟙 F) = 𝟙 _ := rfl
@[simp, reassoc] lemma comp_τ {F₁ F₂ F₃ : hom_factorisation f} (φ : F₁ ⟶ F₂) (φ' : F₂ ⟶ F₃) :
  (φ ≫ φ').τ = φ.τ ≫ φ'.τ := rfl

end hom_factorisation

end category_theory

open category_theory

variables [abelian C] [enough_projectives C]

namespace bounded_above_cochain_complex

namespace projective_model_structure

namespace CM5b

variables {X Z : bounded_above_cochain_complex C} {f : X ⟶ Z}

structure is_cof_fib_factorisation (F : hom_factorisation f) : Prop :=
(hi : arrow_classes.cof F.i)
(hp : arrow_classes.fib F.p)

variable (f)

@[derive category]
def cof_fib_factorisation := full_subcategory (@is_cof_fib_factorisation _ _ _ _ _ _ f)

variable {f}

def cof_fib_factorisation.quasi_iso_ge (F : cof_fib_factorisation f) (n : ℤ) : Prop :=
  ∀ (i : ℤ) (hi : i ≥ n), is_iso (homology_map F.1.p i)

def cof_fib_factorisation.is_iso_ge (F : cof_fib_factorisation f) (n : ℤ) : Prop :=
  ∀ (i : ℤ) (hi : i ≥ n), is_iso (F.1.i.f i)

namespace induction

variables (f) (hf : arrow_classes.fib f)

include hf

lemma step₁ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf : ∀ (q : ℤ) (hq : q ≥ n₁), is_iso (homology_map f q)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₁) (hF₂ : F.quasi_iso_ge n₁),
    epi (homology_map (F.1.p) n₀) := sorry

lemma step₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf : ∀ (q : ℤ) (hq : q ≥ n₁), is_iso (homology_map f q))
  (hf' : epi (homology_map f n₀)) :
  ∃ (F : cof_fib_factorisation f) (hF₁ : F.is_iso_ge n₀),
    F.quasi_iso_ge n₀ := sorry

lemma step₁₂ (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hf : ∀ (q : ℤ) (hq : q ≥ n₁), is_iso (homology_map f q)) :
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

lemma step (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (F : cof_fib_factorisation f) (hF : F.quasi_iso_ge n₁):
  ∃ (F' : cof_fib_factorisation f) (hF': F'.quasi_iso_ge n₀) (φ : F ⟶ F'),
    ∀ (i : ℤ) (hi : i ≥ n₁), is_iso ((hom_factorisation.hom.τ φ).f i) :=
begin
  obtain ⟨G, hG, hG'⟩ := step₁₂ F.1.p n₀ n₁ hn₁ hF,
  let F' : cof_fib_factorisation f :=
  ⟨{ Y := G.1.Y,
    i :=  F.1.i ≫ G.1.i,
    p := G.1.p, },
  { hi := cof_stable_under_composition _ _ F.2.hi G.2.hi,
    hp := G.2.hp, }⟩,
  exact ⟨F', hG', { τ := G.1.i, }, hG⟩,
end

end induction

lemma for_fibration {X Z : bounded_above_cochain_complex C} (f : X ⟶ Z)
  (hf : arrow_classes.fib f) :
  ∃ (Y : bounded_above_cochain_complex C) (i : X ⟶ Y)
    (hi : arrow_classes.cof i) (p : Y ⟶ Z)
    (hp : arrow_classes.triv_fib p), f = i ≫ p :=
begin
  sorry
end

end CM5b

lemma CM5b : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5b :=
λ X Z f, begin
  obtain ⟨X', j, hj, q, hq, rfl⟩ := projective_model_structure.CM5a f,
  obtain ⟨Y, i, hi, p, hp, rfl⟩ := CM5b_for_fibration q hq,
  exact ⟨Y, j ≫ i, cof_stable_under_composition j i hj.1 hi, p, hp, by rw assoc⟩,
end

lemma CM5 : (arrow_classes : category_with_fib_cof_weq (bounded_above_cochain_complex C)).CM5 :=
  ⟨CM5a, CM5b⟩

end projective_model_structure

end bounded_above_cochain_complex
