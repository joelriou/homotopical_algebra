import for_mathlib.algebra.homology.triangulated
import for_mathlib.category_theory.triangulated.homological_functor

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.triangulated category_theory.pretriangulated
open_locale zero_object

section

variables {C ι : Type*} [category C]
  (c : complex_shape ι)

instance homological_complex.single_additive [decidable_eq ι] [preadditive C] [has_zero_object C] (n : ι) :
  (homological_complex.single C c n).additive :=
⟨λ X Y f g, by { ext i, dsimp, split_ifs; simp, }⟩

instance homotopy_category.homology_functor_additive [abelian C] (n : ι) :
  (homotopy_category.homology_functor C c n).additive :=
@quotient.lift_additive _ _ _ _ _ _ _ _ _
    (infer_instance : (homotopy_category.quotient C _).additive) _ _ _

variable (C)

def homotopy_category.comm_shift_quotient [preadditive C] (n : ℤ) :
  shift_functor (cochain_complex C ℤ) n ⋙
    homotopy_category.quotient _ _ ≅
  homotopy_category.quotient _ _ ⋙ shift_functor _ n :=
quotient.comm_shift _ _

namespace cochain_complex

section

variables [preadditive C] (K : cochain_complex C ℤ) (n k m : ℤ) (h : k + n = m)

include h

variable (C)

def shift_eval_prev : (shift_functor _ n) ⋙ homological_complex.eval C _ ((complex_shape.up ℤ).prev k) ≅
  homological_complex.eval C _ ((complex_shape.up ℤ).prev m) :=
preadditive.mul_iso ((-1 : units ℤ)^n) (eq_to_iso (congr_arg (homological_complex.eval _ _)
  (show (complex_shape.up ℤ).prev k + n = (complex_shape.up ℤ).prev m, by { simp, linarith, })))
def shift_eval : (shift_functor _ n) ⋙ homological_complex.eval C (complex_shape.up ℤ) k ≅
  homological_complex.eval C (complex_shape.up ℤ) m :=
eq_to_iso (congr_arg (homological_complex.eval _ _)  h)
def shift_eval_next : (shift_functor _ n) ⋙ homological_complex.eval C _ ((complex_shape.up ℤ).next k) ≅
  homological_complex.eval C _ ((complex_shape.up ℤ).next m) :=
preadditive.mul_iso ((-1 : units ℤ)^n) (eq_to_iso (congr_arg (homological_complex.eval _ _)
  (show (complex_shape.up ℤ).next k + n = (complex_shape.up ℤ).next m, by { simp, linarith, })))

variable {C}

lemma shift_eval_prev_hom_app_comp_d_to :
  (shift_eval_prev C n k m h).hom.app K ≫ K.d_to m =
    K⟦n⟧.d_to k ≫ (shift_eval C n k m h).hom.app K :=
begin
  subst h,
  simp only [K⟦n⟧.d_to_eq (show (k-1)+1 = k, by linarith),
    K.d_to_eq (show (k-1+n)+1 = k+n, by linarith), shift_functor_obj_d'],
  dsimp [homological_complex.X_prev_iso, shift_eval_prev, shift_eval],
  simp only [add_zero, zero_add, neg_zero, nat_trans.app_zsmul, eq_to_hom_app,
    linear.smul_comp_assoc, eq_to_hom_trans, linear.smul_comp, linear.comp_smul, assoc,
    eq_to_hom_trans_assoc],
  erw comp_id,
  refl,
end

lemma shift_eval_hom_app_comp_d_from :
(shift_eval C n k m h).hom.app K ≫ K.d_from m =
  K⟦n⟧.d_from k ≫ (shift_eval_next C n k m h).hom.app K :=
begin
  subst h,
  simp only [K⟦n⟧.d_from_eq rfl, shift_functor_obj_d',
    K.d_from_eq (show k+n+1=k+1+n, by linarith)],
  dsimp [homological_complex.X_next_iso, shift_eval_next, shift_eval, hom_complex.ε],
  simpa only [id_comp, linear.smul_comp, nat_trans.app_zsmul, eq_to_hom_app,
    linear.comp_smul, assoc, eq_to_hom_trans, smul_smul,
    ← units.coe_mul, ← mul_zpow, neg_mul, mul_neg, neg_neg,
    int.units_mul_self, one_zpow, units.coe_one, one_zsmul],
end

variable (C)

def shift_short_complex_functor_iso :
  shift_functor _ n ⋙ homological_complex.short_complex_functor C (complex_shape.up ℤ) k ≅
    homological_complex.short_complex_functor C (complex_shape.up ℤ) m :=
nat_iso.of_components
  (λ K, short_complex.mk_iso ((shift_eval_prev C _ _ _ h).app K) ((shift_eval C _ _ _ h).app K)
    (((shift_eval_next C _ _ _ h).app K)) (shift_eval_prev_hom_app_comp_d_to _ _ _ _ _)
    (shift_eval_hom_app_comp_d_from _ _ _ _ _))
  (λ K L φ, begin
    ext1,
    { exact (shift_eval_prev C _ _ _ h).hom.naturality φ, },
    { exact (shift_eval C _ _ _ h).hom.naturality φ, },
    { exact (shift_eval_next C _ _ _ h).hom.naturality φ, },
  end)

end

def shift_homology_functor_iso [abelian C] (n k m : ℤ) (h : k + n = m) :
  shift_functor _ n ⋙ homology_functor C (complex_shape.up ℤ) k ≅
    homology_functor C _ m :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right (shift_short_complex_functor_iso C _ _ _ h) _

end cochain_complex

def homotopy_category.shift_homology_functor_iso [abelian C] (n k m : ℤ) (h : k + n = m):
  shift_functor _ n ⋙ homotopy_category.homology_functor C (complex_shape.up ℤ) k ≅
    homotopy_category.homology_functor C _ m :=
quotient.lift_nat_iso _ _ ((functor.associator _ _ _).symm ≪≫
  iso_whisker_right (quotient.comm_shift _ _).symm _ ≪≫
  functor.associator _ _ _ ≪≫
  iso_whisker_left _ (homotopy_category.homology_factors _ _ _).symm ≪≫
  cochain_complex.shift_homology_functor_iso C _ _ _ h ≪≫
  (homotopy_category.homology_factors _ _ _).symm)

end

variables (C : Type*) [category C] [abelian C]

namespace homotopy_category

instance homology_functor_is_homological (n : ℤ):
  (homology_functor C (complex_shape.up ℤ) n).is_homological := sorry

def acyclic : triangulated.subcategory (homotopy_category C (complex_shape.up ℤ)) :=
(homology_functor C (complex_shape.up ℤ) 0).kernel_of_is_homological

instance acyclic_saturated : (acyclic C).saturated :=
by { dsimp only [acyclic], apply_instance, }

lemma mem_acyclic_W_iff {K L : homotopy_category C (complex_shape.up ℤ)} (φ : K ⟶ L) :
  (acyclic C).W φ ↔ ∀ (n : ℤ), is_iso ((homology_functor _ _ n).map φ) :=
begin
  dsimp only [acyclic],
  rw functor.kernel_of_is_homological_W,
  simpa only [← λ n, nat_iso.is_iso_map_iff (shift_homology_functor_iso C _ _ _ (zero_add n)) φ],
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

instance : inhabited (derived_category C) := ⟨0⟩

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

variable (C)

def comm_shift_Q (n : ℤ) :
  shift_functor (cochain_complex C ℤ) n ⋙ Q ≅
  Q ⋙ shift_functor _ n :=
sorry

variable {C}

lemma is_iso_Q_map_iff {K L : cochain_complex C ℤ} (φ : K ⟶ L) :
  is_iso (Q.map φ) ↔ quasi_iso φ :=
(subcategory.is_iso_map_iff _ _).trans (homotopy_category.map_quotient_W_iff C φ)

instance {K L : cochain_complex C ℤ} (φ : K ⟶ L) [quasi_iso φ] :
  is_iso (Q.map φ) :=
by { rw is_iso_Q_map_iff, apply_instance, }

section

variables {K L : cochain_complex C ℤ}
  (φ : K ⟶ L)

def mapping_cone := Q.obj (cochain_complex.mapping_cone φ)

def ι_mapping_cone : Q.obj L ⟶ mapping_cone φ :=
Q.map (cochain_complex.ι_mapping_cone φ)

def mapping_cone_δ : mapping_cone φ ⟶ (Q.obj K)⟦(1 : ℤ)⟧ :=
  Q.map (cochain_complex.mapping_cone_δ φ) ≫ (comm_shift_Q C 1).hom.app K

def mapping_cone_triangle : triangle (derived_category C) :=
triangle.mk (Q.map φ) (ι_mapping_cone φ) (mapping_cone_δ φ)

lemma Qh_map_mapping_cone_triangle_iso :
  (Qh.map_triangle.obj (homotopy_category.mapping_cone_triangle' φ) ≅
    mapping_cone_triangle φ) :=
begin
  sorry,
end

end

def mem_dist_triang_iff' (T : triangle (derived_category C)) :
  (T ∈ dist_triang (derived_category C)) ↔
    ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L),
      nonempty (T ≅
        Qh.map_triangle.obj (homotopy_category.mapping_cone_triangle' φ)) :=
begin
  split,
  { rintro ⟨Th, e, ⟨K, L, φ, ⟨e'⟩⟩⟩,
    exact ⟨K, L, φ, ⟨e ≪≫ Qh.map_triangle.map_iso e'⟩⟩, },
  { rintro ⟨K, L, φ, ⟨e⟩⟩,
    exact ⟨_, e, ⟨K, L, φ, ⟨iso.refl _⟩⟩⟩, },
end


def mem_dist_triang_iff (T : triangle (derived_category C)) :
  (T ∈ dist_triang (derived_category C)) ↔
    ∃ (K L : cochain_complex C ℤ) (φ : K ⟶ L),
      nonempty (T ≅ mapping_cone_triangle φ) :=
begin
  rw mem_dist_triang_iff',
  split,
  { rintro ⟨K, L, φ, ⟨e⟩⟩,
    exact ⟨K, L, φ, ⟨e ≪≫ Qh_map_mapping_cone_triangle_iso _⟩⟩, },
  { rintro ⟨K, L, φ, ⟨e⟩⟩,
    exact ⟨K, L, φ, ⟨e ≪≫ (Qh_map_mapping_cone_triangle_iso _).symm⟩⟩, },
end

instance is_iso_Q_map_from_mapping_cone_of_ses
  {S : short_complex (cochain_complex C ℤ)}
  (ex : S.short_exact) :
  quasi_iso (cochain_complex.from_mapping_cone_of_ses ex) :=
cochain_complex.from_mapping_cone_of_ses_quasi_iso ex

def triangle_of_ses_δ {S : short_complex (cochain_complex C ℤ)}
  (ex : S.short_exact) : Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
inv (Q.map (cochain_complex.from_mapping_cone_of_ses ex)) ≫ (mapping_cone_triangle S.f).mor₃

@[simps]
def triangle_of_ses {S : short_complex (cochain_complex C ℤ)}
  (ex : S.short_exact) : triangle (derived_category C) :=
triangle.mk (Q.map S.f) (Q.map S.g) (triangle_of_ses_δ ex)

lemma triangle_of_ses_dist {S : short_complex (cochain_complex C ℤ)}
  (ex : S.short_exact) : triangle_of_ses ex ∈ dist_triang (derived_category C) :=
begin
  rw mem_dist_triang_iff,
  refine ⟨_, _, S.f, ⟨_⟩⟩,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
    (as_iso (Q.map (cochain_complex.from_mapping_cone_of_ses ex))).symm (by tidy) _ _,
  { dsimp [triangle_of_ses, mapping_cone_triangle, ι_mapping_cone],
    simp only [← cancel_mono (Q.map (cochain_complex.from_mapping_cone_of_ses ex)),
      id_comp, assoc, is_iso.inv_hom_id, comp_id, ← Q.map_comp,
      cochain_complex.ι_mapping_cone_comp_from_mapping_cone_of_ses], },
  { dsimp [triangle_of_ses, triangle_of_ses_δ],
    simp only [category_theory.functor.map_id, comp_id], },
end

variable (C)

def single_functor (n : ℤ) : C ⥤ derived_category C :=
homological_complex.single _ _ n ⋙ Q

instance single_functor_additive (n : ℤ) : (single_functor C n).additive :=
by { dsimp [single_functor], apply_instance, }


end derived_category
