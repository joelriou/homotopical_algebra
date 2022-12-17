import for_mathlib.algebra.homology.triangulated
import for_mathlib.category_theory.triangulated.homological_functor

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.triangulated category_theory.pretriangulated

variables (C : Type*) [category C] [abelian C]

namespace homotopy_category

/- should be generalised -/
instance homology_functor_additive (n : ℤ) :
  (homology_functor C (complex_shape.up ℤ) n).additive := sorry

instance homology_functor_is_homological (n : ℤ):
  (homology_functor C (complex_shape.up ℤ) n).is_homological := sorry

def acyclic : triangulated.subcategory (homotopy_category C (complex_shape.up ℤ)) :=
(homology_functor C (complex_shape.up ℤ) 0).kernel_of_is_homological

instance acyclic_saturated : (acyclic C).saturated :=
by { dsimp only [acyclic], apply_instance, }

/-- should be obtained first for homological complexes -/
def shift_homology_functor_iso (n k m : ℤ) (h : n + k = m):
  shift_functor _ n ⋙ homology_functor C (complex_shape.up ℤ) k ≅
    homology_functor C _ m := sorry

lemma mem_acyclic_W_iff {K L : homotopy_category C (complex_shape.up ℤ)} (φ : K ⟶ L) :
  (acyclic C).W φ ↔ ∀ (n : ℤ), is_iso ((homology_functor _ _ n).map φ) :=
begin
  dsimp only [acyclic],
  rw functor.kernel_of_is_homological_W,
  simpa only [← λ n, nat_iso.is_iso_map_iff (shift_homology_functor_iso C _ _ _ (add_zero n)) φ],
end

lemma map_quotient_W_iff {K L : cochain_complex C ℤ} (φ : K ⟶ L) :
  (acyclic C).W ((quotient _ _).map φ) ↔ quasi_iso φ :=
begin
  simp only [mem_acyclic_W_iff, ← homology_functor_map_factors],
  split,
  { intro h,
    exact ⟨h⟩, },
  { intro h,
    exact h.is_iso, }
end

end homotopy_category

@[derive category, derive preadditive, derive has_zero_object, derive has_finite_products,
  derive has_finite_coproducts]
def derived_category := (homotopy_category.acyclic C).W.localization

namespace derived_category

variable {C}

instance : has_shift (derived_category C) ℤ :=
by { dsimp [derived_category], apply_instance, }

instance shift_functor_additive (n : ℤ) :
  (shift_functor (derived_category C) n).additive :=
by { dsimp [derived_category], apply_instance, }

instance : pretriangulated (derived_category C) :=
by { dsimp [derived_category], apply_instance, }

instance : is_triangulated (derived_category C) :=
by { dsimp [derived_category], apply_instance, }

def Qh : triangulated_functor (homotopy_category C (complex_shape.up ℤ)) (derived_category C) :=
pretriangulated.localization_functor _ _ _

instance Qh_additive : (Qh : triangulated_functor _ (derived_category C)).to_functor.additive :=
by { dsimp [Qh, localization_functor], apply_instance, }

instance Qh_is_localization_W :
  Qh.to_functor.is_localization (homotopy_category.acyclic C).W :=
begin
  change (morphism_property.Q _).is_localization _,
  apply_instance,
end

def Q : cochain_complex C ℤ ⥤ derived_category C :=
homotopy_category.quotient _ _ ⋙ Qh.to_functor

instance Q_additive : (Q : _ ⥤ derived_category C).additive :=
by { dsimp [Q], apply_instance, }

lemma is_iso_Q_map_iff {K L : cochain_complex C ℤ} (φ : K ⟶ L) :
  is_iso (Q.map φ) ↔ quasi_iso φ :=
(subcategory.is_iso_map_iff _ _).trans (homotopy_category.map_quotient_W_iff C φ)

variable (C)

def single_functor (n : ℤ) : C ⥤ derived_category C :=
homological_complex.single _ _ n ⋙ Q

instance single_additive (n : ℤ) :
  (homological_complex.single C (complex_shape.up ℤ) n).additive := sorry

instance single_functor_additive (n : ℤ) : (single_functor C n).additive :=
by { dsimp [single_functor], apply_instance, }

end derived_category
