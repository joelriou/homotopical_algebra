import for_mathlib.algebra.homology.derived_category

noncomputable theory

open category_theory category_theory.category category_theory.pretriangulated
  category_theory.limits


namespace homological_complex

/- to be moved to algebra.homology.homology -/

variables {C ι : Type*} {c : complex_shape ι} [category C] [has_zero_morphisms C]

abbreviation cycles (K : homological_complex C c) (i : ι) [K.has_homology i] : C :=
((short_complex_functor C c i).obj K).cycles

abbreviation homology_π (K : homological_complex C c) (i : ι) [K.has_homology i] :
  K.cycles i ⟶ K.homology i :=
((short_complex_functor C c i).obj K).homology_π

def lift_cycles (K : homological_complex C c) {A : C} {n₀ : ι} [K.has_homology n₀]
  (z : A ⟶ K.X n₀) (n₁ : ι) (hn₁ : c.rel n₀ n₁) (hz : z ≫ K.d n₀ n₁ = 0) :
    A ⟶ K.cycles n₀ :=
short_complex.lift_cycles _ z begin
  have hn₁ := c.next_eq' hn₁,
  subst hn₁,
  exact hz,
end

end homological_complex

variables {C : Type*} [category C] [abelian C]

namespace derived_category

@[reassoc]
lemma homology_functor_factors_hom_naturality {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  (homology_functor C n).map (Q.map φ) ≫ (homology_functor_factors C n).hom.app L =
    (homology_functor_factors C n).hom.app K ≫ homology_map φ n :=
(homology_functor_factors C n).hom.naturality φ

@[reassoc]
lemma homology_functor_factors_inv_naturality {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  homology_map φ n ≫ (homology_functor_factors C n).inv.app L =
    (homology_functor_factors C n).inv.app K ≫ (homology_functor C n).map (Q.map φ) :=
(homology_functor_factors C n).inv.naturality φ

end derived_category

namespace cochain_complex

namespace homology_sequence

variables {C} {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

include ex

lemma ex₂ (n : ℤ) :
  (short_complex.mk (homology_map S.f n) (homology_map S.g n)
    (by rw [← homology_map_comp, S.zero, _root_.homology_map_zero])).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (derived_category.homology_sequence.ex₂ (derived_category.triangle_of_ses_dist ex) n),
  exact short_complex.mk_iso
    ((derived_category.homology_functor_factors C n).app _)
    ((derived_category.homology_functor_factors C n).app _)
    ((derived_category.homology_functor_factors C n).app _)
    (derived_category.homology_functor_factors_hom_naturality S.f n).symm
    (derived_category.homology_functor_factors_hom_naturality S.g n).symm,
end

def δ (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  S.X₃.homology n₀ ⟶ S.X₁.homology n₁ :=
(derived_category.homology_functor_factors C n₀).inv.app S.X₃ ≫
  derived_category.homology_sequence.δ (derived_category.triangle_of_ses_dist ex) n₀ n₁ h ≫
  (derived_category.homology_functor_factors C n₁).hom.app S.X₁

@[simp, reassoc]
lemma δ_comp (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  δ ex _ _ h ≫ homology_map S.f n₁  = 0 :=
begin
  dsimp only [δ],
  simp only [assoc, ← derived_category.homology_functor_factors_hom_naturality],
  erw [derived_category.homology_sequence.δ_comp_assoc, zero_comp, comp_zero],
end

@[simp, reassoc]
lemma comp_δ (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  homology_map S.g n₀ ≫ δ ex _ _ h = 0 :=
begin
  dsimp only [δ],
  rw derived_category.homology_functor_factors_inv_naturality_assoc,
  erw derived_category.homology_sequence.comp_δ_assoc (derived_category.triangle_of_ses_dist ex),
  rw [zero_comp, comp_zero],
end

lemma ex₃ (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (short_complex.mk (homology_map S.g n₀) (δ ex _ _ h) (by simp)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (derived_category.homology_sequence.ex₃ (derived_category.triangle_of_ses_dist ex) n₀ n₁ h),
  exact short_complex.mk_iso
    ((derived_category.homology_functor_factors C n₀).app _)
    ((derived_category.homology_functor_factors C n₀).app _)
    ((derived_category.homology_functor_factors C n₁).app _)
    (derived_category.homology_functor_factors_hom_naturality S.g n₀).symm
    (by { dsimp [δ], simp only [iso.hom_inv_id_app_assoc]}),
end

lemma ex₁ (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (short_complex.mk (δ ex _ _ h) (homology_map S.f n₁)  (by simp)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1
    (derived_category.homology_sequence.ex₁ (derived_category.triangle_of_ses_dist ex) n₀ n₁ h),
  exact short_complex.mk_iso
    ((derived_category.homology_functor_factors C n₀).app _)
    ((derived_category.homology_functor_factors C n₁).app _)
    ((derived_category.homology_functor_factors C n₁).app _)
    (by { dsimp [δ], simp only [iso.hom_inv_id_app_assoc], })
    (derived_category.homology_functor_factors_hom_naturality S.f n₁).symm,
end

lemma comp_δ_eq {n₀ n₁ : ℤ} {A : C} (x₃ : A ⟶ S.X₃.X n₀)
  (x₂ : A ⟶ S.X₂.X n₀) (x₁ : A ⟶ S.X₁.X n₁) (h : n₁ = n₀+1)
    (hx₃ : x₃ ≫ S.X₃.d n₀ n₁ = 0) (hx₂ : x₂ ≫ S.g.f n₀ = x₃)
    (hx₁ : x₁ ≫ S.f.f n₁ = x₂ ≫ S.X₂.d n₀ n₁) :
  S.X₃.lift_cycles x₃ n₁ h.symm hx₃ ≫ S.X₃.homology_π n₀ ≫ (δ ex n₀ n₁ h) =
    S.X₁.lift_cycles x₁ (n₁+1) rfl begin
      haveI : mono (S.f.f (n₁+1)) :=
        (short_complex.short_exact.map_of_exact ex (homological_complex.eval _ _ (n₁+1))).mono_f,
      simp only [← cancel_mono (S.f.f (n₁+1)), assoc, ← S.f.comm, reassoc_of hx₁,
        homological_complex.d_comp_d, comp_zero, zero_comp],
    end ≫ S.X₁.homology_π n₁ :=
begin
/- lift x₃ as a cocycle of the cone of S.f, etc. -/
  sorry,
end

/- Actually, we probably need a more general homology sequence for any complex_shape, which
could be done using the snake lemma, and then `comp_δ_eq` would give the comparison of
the maps... -/
end homology_sequence

end cochain_complex
