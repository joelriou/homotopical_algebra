import for_mathlib.algebra.homology.triangulated
import for_mathlib.category_theory.triangulated.homological_functor_localization
import for_mathlib.category_theory.shift_misc
import for_mathlib.category_theory.localization.composition
import for_mathlib.algebra.homology.cylinder

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

instance [preadditive C]: full (homotopy_category.quotient C c) :=
by { dsimp [homotopy_category.quotient], apply_instance, }

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

section

open cochain_complex

lemma homology_functor_comp_ι_mapping_cone {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  (homology_functor C (complex_shape.up ℤ) n).map (φ ≫ ι_mapping_cone φ) = 0 :=
begin
  rw homotopy_category.homology_functor_map_factors,
  have hφ : homotopy_category.induced_triangle (mapping_cone_triangle φ) ∈ dist_triang _,
  { rw homotopy_category.triangle_distinguished_iff,
    exact ⟨_, _, _, ⟨iso.refl _⟩⟩, },
  simpa only [functor.map_comp, functor.map_zero]
    using (homotopy_category.homology_functor _ _ n).congr_map
      ((triangle.comp_eq_zero.of_distinguished _ hφ).zero₁₂),
end

variable {C}

lemma homology_functor_is_homological_aux {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  (short_complex.mk ((homology_functor C (complex_shape.up ℤ) n).map φ)
    ((homology_functor C (complex_shape.up ℤ) n).map (ι_mapping_cone φ))
    (by rw [← functor.map_comp, homology_functor_comp_ι_mapping_cone])).exact :=
begin
  rw short_complex.exact_iff_pseudo_exact',
  intros A₀ γ₂ hγ₂,
  dsimp at γ₂ hγ₂,
  /- the next three operations could be a specialised lemma -/
  obtain ⟨A₁, π₁, hπ₁, z₂, hz₂⟩ := abelian.pseudo_surjective_of_epi'
    (short_complex.homology_π _) γ₂,
  have hz₂' : ∃ z₂' hz₂', z₂ = short_complex.lift_cycles _ z₂' hz₂' :=
    ⟨z₂ ≫ short_complex.cycles_i _,
      by simp only [assoc, short_complex.cycles_i_g, comp_zero],
      by simp only [← cancel_mono ((homological_complex.short_complex_functor C
        (complex_shape.up ℤ) n).obj L).cycles_i, short_complex.lift_cycles_i]⟩,
  obtain ⟨z₂, hz₂', rfl⟩ := hz₂',
  replace hγ₂ := π₁ ≫= hγ₂,
  rw [reassoc_of hz₂, comp_zero, short_complex.homology_π_naturality, ← assoc,
    short_complex.comp_homology_π_eq_zero_iff] at hγ₂,
  obtain ⟨A₂, π₂, hπ₂, c₁, hc₁⟩ := hγ₂,
  dsimp at c₁ hc₁,
  replace hc₁ := hc₁ =≫ (short_complex.cycles_i _),
  simp only [assoc, homological_complex.short_complex_functor_map_τ₂,
    short_complex.lift_cycles_comp_cycles_map, short_complex.lift_cycles_i,
    short_complex.to_cycles_i, homological_complex.short_complex_functor_obj_f,
    @to_mapping_cone_ext_iff _ _ _ _ _ _ φ _ _ _ _ ((complex_shape.up _).next n) (by simp),
    mapping_cone_d_fst ((complex_shape.up _).prev n) n ((complex_shape.up _).next n) (by simp) (by simp),
    mapping_cone_d_snd ((complex_shape.up _).prev n) n (by simp),
    ι_mapping_cone, mapping_cone_inr_fst, comp_zero, preadditive.comp_neg,
    zero_eq_neg, mapping_cone_inr_snd, preadditive.comp_add] at hc₁,
  dsimp at hc₁,
  rw comp_id at hc₁,
  obtain ⟨hc₁, hc₁'⟩ := hc₁,
  rw ← assoc at hc₁,
  haveI := hπ₁,
  haveI := hπ₂,
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _,
    ((homological_complex.short_complex_functor C
      (complex_shape.up ℤ) n).obj K).lift_cycles _ hc₁ ≫ short_complex.homology_π _, _⟩,
  dsimp,
  simp only [assoc, hz₂, short_complex.comp_lift_cycles_assoc,
    homological_complex.short_complex_functor_map_τ₂, short_complex.homology_π_naturality,
    short_complex.lift_cycles_comp_cycles_map_assoc,
    short_complex.lift_cycles_comp_homology_π_eq_iff],
  exact ⟨A₂, 𝟙 A₂, infer_instance,
    c₁ ≫ (mapping_cone_snd φ).v ((complex_shape.up ℤ).prev n)
      ((complex_shape.up ℤ).prev n) (add_zero _).symm, by simpa only [id_comp, hc₁', assoc]⟩,
end

end

variable (C)

namespace homotopy_category

instance homology_functor_is_homological (n : ℤ):
  (homology_functor C (complex_shape.up ℤ) n).is_homological :=
functor.is_homological.mk' _ (λ T hT, begin
  rw triangle_distinguished_iff at hT,
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT,
  refine ⟨_, ⟨_, _, _, ⟨mapping_cone_induced_triangle_iso φ⟩⟩, e,
    homology_functor_is_homological_aux φ n⟩,
end)

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

lemma homology_functor_is_inverted_by (n : ℤ) :
  (acyclic C).W.is_inverted_by (homology_functor C (complex_shape.up ℤ) n) :=
begin
  intros K L φ hφ,
  rw mem_acyclic_W_iff at hφ,
  exact hφ n,
end

variable {C}

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

section

variables (D : Type*) [category D] [has_zero_morphisms D] [category_with_homology D]
  {ι : Type*} (c : complex_shape ι)

def quasi_isomorphisms :
  morphism_property (homological_complex D c) :=
λ K L φ, ∀ (i : ι), is_iso (homology_map φ i)

variables {D c}

lemma mem_quasi_isomorphisms_iff {K L : homological_complex D c} (φ : K ⟶ L) :
  quasi_isomorphisms D c φ ↔ quasi_iso φ :=
⟨λ h, ⟨h⟩, λ h, h.1⟩

end

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

instance : ess_surj (Qh.to_functor : _ ⥤ derived_category C) :=
localization.ess_surj _ (homotopy_category.acyclic C).W

def Q : cochain_complex C ℤ ⥤ derived_category C :=
homotopy_category.quotient _ _ ⋙ Qh.to_functor

instance Q_additive : (Q : _ ⥤ derived_category C).additive :=
by { dsimp [Q], apply_instance, }

variable (C)

def comm_shift_Q_one :
  shift_functor (cochain_complex C ℤ) (1 : ℤ) ⋙
    (Q : cochain_complex _ _ ⥤ derived_category C) ≅
    Q ⋙ shift_functor (derived_category C) (1 : ℤ) :=
functor.comm_shift_comp (homotopy_category.quotient_triangulated_functor_struct.comm_shift) Qh.comm_shift

variable {C}

lemma is_iso_Q_map_iff {K L : cochain_complex C ℤ} (φ : K ⟶ L) :
  is_iso (Q.map φ) ↔ quasi_iso φ :=
(subcategory.is_iso_map_iff _ _).trans (homotopy_category.map_quotient_W_iff φ)

instance {K L : cochain_complex C ℤ} (φ : K ⟶ L) [quasi_iso φ] :
  is_iso (Q.map φ) :=
by { rw is_iso_Q_map_iff, apply_instance, }

variable (C)

lemma Q_inverts_quasi_isomorphisms : (quasi_isomorphisms C _).is_inverted_by Q :=
λ K L φ hφ, begin
  rw mem_quasi_isomorphisms_iff at hφ,
  haveI := hφ,
  apply_instance,
end

lemma homotopy_equivalences_subset_quasi_isomorphisms :
  cochain_complex.homotopy_equivalences C ⊆ quasi_isomorphisms C (complex_shape.up ℤ) :=
begin
  rintros K L _ ⟨h, rfl⟩,
  simpa only [mem_quasi_isomorphisms_iff] using h.to_quasi_iso,
end

instance Q_is_localization : Q.is_localization (quasi_isomorphisms C _) :=
localization.comp (homotopy_category.quotient _ _) (Qh.to_functor)
    (cochain_complex.homotopy_equivalences C) (homotopy_category.acyclic C).W
    (quasi_isomorphisms C _) (Q_inverts_quasi_isomorphisms C)
    (homotopy_equivalences_subset_quasi_isomorphisms C)
(begin
  rintros ⟨K⟩ ⟨L⟩ φ hφ,
  have hf : ∃ (f : K ⟶ L), (homotopy_category.quotient _ _).map f = φ :=
    ⟨_, (homotopy_category.quotient C (complex_shape.up ℤ)).image_preimage φ⟩,
  obtain ⟨f, rfl⟩ := hf,
  refine ⟨_, _, f, _, ⟨iso.refl _⟩⟩,
  simpa only [mem_quasi_isomorphisms_iff, ← homotopy_category.map_quotient_W_iff] using hφ,
end)

instance : ess_surj (Q : _ ⥤ derived_category C) :=
localization.ess_surj _ (quasi_isomorphisms C _)

variable {C}

section

variables {K L : cochain_complex C ℤ}
  (φ : K ⟶ L)

def mapping_cone := Q.obj (cochain_complex.mapping_cone φ)

def ι_mapping_cone : Q.obj L ⟶ mapping_cone φ :=
Q.map (cochain_complex.ι_mapping_cone φ)

def mapping_cone_δ : mapping_cone φ ⟶ (Q.obj K)⟦(1 : ℤ)⟧ :=
  Q.map (cochain_complex.mapping_cone_δ φ) ≫ (comm_shift_Q_one C).hom.app K

def mapping_cone_triangle : triangle (derived_category C) :=
triangle.mk (Q.map φ) (ι_mapping_cone φ) (mapping_cone_δ φ)

lemma Qh_map_mapping_cone_triangle_iso :
  (Qh.map_triangle.obj (homotopy_category.mapping_cone_triangle' φ) ≅
    mapping_cone_triangle φ) :=
begin -- needs cleaning up...
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
  { tidy, },
  { tidy, },
  { dsimp [mapping_cone_triangle, mapping_cone_δ,
      homotopy_category.mapping_cone_triangle',
      cochain_complex.mapping_cone_δ',
      comm_shift_Q_one, functor.comm_shift_comp],
    simp only [category_theory.functor.map_id, comp_id, id_comp],
    congr' 1,
    erw id_comp,
    symmetry,
    convert id_comp _,
    convert category_theory.functor.map_id _ _, },
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

lemma left_factorisation {K L : cochain_complex C ℤ} (φ : Q.obj K ⟶ Q.obj L) :
  ∃ (L' : cochain_complex C ℤ) (f : K ⟶ L') (s : L ⟶ L') (hs : quasi_iso s),
    φ = Q.map f ≫ (by { haveI := hs, exact inv (Q.map s), }) :=
begin
  obtain ⟨⟨⟨L'⟩, f, s, hs⟩ , hz⟩ :=
    left_calculus_of_fractions.L_map_fac Qh.to_functor (homotopy_category.acyclic C).W φ,
  refine ⟨_, (homotopy_category.quotient _ _).preimage f,
    (homotopy_category.quotient _ _).preimage s, _, _⟩,
  { simpa only [← homotopy_category.map_quotient_W_iff, functor.image_preimage] using hs, },
  { dsimp [Q],
    simpa only [functor.image_preimage] using hz, },
end

lemma right_factorisation {K L : cochain_complex C ℤ} (φ : Q.obj K ⟶ Q.obj L) :
  ∃ (K' : cochain_complex C ℤ) (s : K' ⟶ K) (f : K' ⟶ L) (hs : quasi_iso s),
    φ = (by { haveI := hs, exact inv (Q.map s), }) ≫ Q.map f :=
begin
  obtain ⟨⟨⟨L'⟩, s, f, hs⟩ , hz⟩ :=
    right_calculus_of_fractions.L_map_fac Qh.to_functor (homotopy_category.acyclic C).W φ,
  refine ⟨_, (homotopy_category.quotient _ _).preimage s,
    (homotopy_category.quotient _ _).preimage f, _, _⟩,
  { simpa only [← homotopy_category.map_quotient_W_iff, functor.image_preimage] using hs, },
  { dsimp [Q],
    simpa only [functor.image_preimage] using hz, },
end

variable (C)

def homology_functor (n : ℤ) : derived_category C ⥤ C :=
localization.lift (homotopy_category.homology_functor C (complex_shape.up ℤ) n)
  (homotopy_category.homology_functor_is_inverted_by C n) Qh.to_functor

instance (n : ℤ) : localization.lifting Qh.to_functor (homotopy_category.acyclic C).W
  (homotopy_category.homology_functor C (complex_shape.up ℤ) n) (homology_functor C n) :=
localization.lifting_lift _ _ _

def homology_functor_factors_Qh (n : ℤ) :
  Qh.to_functor ⋙ homology_functor C n ≅
    homotopy_category.homology_functor C (complex_shape.up ℤ) n :=
localization.lifting.iso _ (homotopy_category.acyclic C).W _ _

def homology_functor_factors (n : ℤ) :
  Q ⋙ homology_functor C n ≅ _root_.homology_functor C (complex_shape.up ℤ) n :=
functor.associator _ _ _ ≪≫ iso_whisker_left _ ((homology_functor_factors_Qh C n)) ≪≫
  homotopy_category.homology_factors C _ n

instance homology_functor_preserves_zero_morphisms (n : ℤ) :
  (homology_functor C n).preserves_zero_morphisms :=
functor.is_homological.localization_lift_preserves_zero_morphisms _ _ _

instance homology_functor_is_homological (n : ℤ) :
  (homology_functor C n).is_homological :=
functor.is_homological.localization_lift_is_homological _ _ _

variable {C}

lemma is_iso_iff_is_iso_homology {K L : derived_category C} (φ : K ⟶ L) :
  is_iso φ ↔ ∀ (n : ℤ), is_iso ((homology_functor C n).map φ) :=
begin
  split,
  { introI,
    exact λ n, infer_instance, },
  { suffices : ∀ ⦃K' L' : cochain_complex C ℤ⦄ (φ' : Q.obj K' ⟶ Q.obj L')
      (hφ' : ∀ (n : ℤ), is_iso ((homology_functor C n).map φ')), is_iso φ',
    { introI,
      let ψ := (Q.obj_obj_preimage_iso K).hom ≫ φ ≫ (Q.obj_obj_preimage_iso L).inv,
      have eq : φ = (Q.obj_obj_preimage_iso K).inv ≫ ψ ≫ (Q.obj_obj_preimage_iso L).hom,
      { simp only [assoc, iso.inv_hom_id, comp_id, iso.inv_hom_id_assoc], },
      rw eq,
      haveI : is_iso ψ := this ψ (λ n, begin
        dsimp only [ψ],
        simp only [functor.map_comp],
        apply_instance,
      end),
      apply_instance, },
    intros K' L' φ' hφ',
    obtain ⟨L', f, s, hs, eq⟩ := left_factorisation φ',
    haveI : is_iso (Q.map f),
    { simp only [eq, functor.map_comp] at hφ',
      haveI := hφ',
      haveI : ∀ (n : ℤ), is_iso ((homology_functor C n).map (Q.map f)),
      { intro n,
        exact is_iso.of_is_iso_comp_right _ ((homology_functor C n).map (inv (Q.map s))), },
      haveI : quasi_iso f,
      { rw ← mem_quasi_isomorphisms_iff,
        intro n,
        refine (nat_iso.is_iso_map_iff (homology_functor_factors C n) f).1 _,
        dsimp,
        apply_instance, },
      apply_instance, },
    rw eq,
    apply_instance, },
end

abbreviation homology (K : derived_category C) (n : ℤ) := (homology_functor C n).obj K

end derived_category
