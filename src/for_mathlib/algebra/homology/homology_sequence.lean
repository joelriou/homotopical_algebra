import for_mathlib.algebra.homology.derived_category

noncomputable theory

open category_theory category_theory.category category_theory.pretriangulated
  category_theory.limits

namespace homological_complex

/- to be moved to algebra.homology.homology (and expanded) -/

variables {C ι : Type*} {c : complex_shape ι} [category C] [has_zero_morphisms C]

abbreviation cycles (K : homological_complex C c) (i : ι) [K.has_homology i] : C :=
((short_complex_functor C c i).obj K).cycles

abbreviation cycles_i (K : homological_complex C c) (i : ι) [K.has_homology i] :
  K.cycles i ⟶ K.X i :=
((short_complex_functor C c i).obj K).cycles_i

@[simp, reassoc]
lemma cycles_i_d (K : homological_complex C c) (i j : ι) [K.has_homology i] :
  K.cycles_i i ≫ K.d i j = 0 :=
begin
  by_cases c.rel i j,
  { have hj := c.next_eq' h,
    subst hj,
    apply short_complex.cycles_i_g, },
  { rw [K.shape _ _ h, comp_zero] },
end

def lift_cycles (K : homological_complex C c) {A : C} {n₀ : ι} [K.has_homology n₀]
  (z : A ⟶ K.X n₀) (n₁ : ι) (hn₁ : c.rel n₀ n₁) (hz : z ≫ K.d n₀ n₁ = 0) :
    A ⟶ K.cycles n₀ :=
short_complex.lift_cycles _ z begin
  have hn₁ := c.next_eq' hn₁,
  subst hn₁,
  exact hz,
end

@[simp, reassoc]
lemma lift_cycles_i (K : homological_complex C c) {A : C} {n₀ : ι} [K.has_homology n₀]
  (z : A ⟶ K.X n₀) (n₁ : ι) (hn₁ : c.rel n₀ n₁) (hz : z ≫ K.d n₀ n₁ = 0) :
  K.lift_cycles z n₁ hn₁ hz ≫ K.cycles_i n₀ = z :=
short_complex.lift_cycles_i _ _ _

lemma eq_lift_cycles_i (K : homological_complex C c) {A : C} {n₀ : ι} [K.has_homology n₀]
  (z : A ⟶ K.cycles n₀) (n₁ : ι) (hn₁ : c.rel n₀ n₁) :
  ∃ (z' : A ⟶ K.X n₀) (hz' : z' ≫ K.d n₀ n₁ = 0),
    z = K.lift_cycles z' n₁ hn₁ hz' :=
⟨z ≫ K.cycles_i n₀, by simp, by simp [← cancel_mono (K.cycles_i n₀)]⟩

abbreviation cycles_map {K L : homological_complex C c} (φ : K ⟶ L) (i : ι)
  [K.has_homology i] [L.has_homology i] :
  K.cycles i ⟶ L.cycles i :=
short_complex.cycles_map ((short_complex_functor C c i).map φ)

@[simp, reassoc]
lemma lift_cycles_comp_cycles_map {K L : homological_complex C c} {A : C} {n₀ : ι}
  [K.has_homology n₀] [L.has_homology n₀] (z : A ⟶ K.X n₀) (n₁ : ι)
  (hn₁ : c.rel n₀ n₁) (hz : z ≫ K.d n₀ n₁ = 0) (φ : K ⟶ L) :
  K.lift_cycles z n₁ hn₁ hz ≫ cycles_map φ n₀ =
    L.lift_cycles (z ≫ φ.f n₀) n₁ hn₁
    (by rw [assoc, φ.comm, reassoc_of hz, zero_comp]) :=
short_complex.lift_cycles_comp_cycles_map _ _ _ _

abbreviation homology_π (K : homological_complex C c) (i : ι) [K.has_homology i] :
  K.cycles i ⟶ K.homology i :=
((short_complex_functor C c i).obj K).homology_π

@[simp, reassoc]
lemma homology_π_naturality {K L : homological_complex C c} (φ : K ⟶ L) (i : ι)
  [K.has_homology i] [L.has_homology i] :
  K.homology_π i ≫ homology_map φ i = cycles_map φ i ≫ L.homology_π i :=
short_complex.homology_π_naturality _

variables (C c)

@[simps]
def _root_.cycles_functor (i : ι) [category_with_homology C] :
  homological_complex C c ⥤ C :=
  short_complex_functor C c i ⋙ short_complex.cycles_functor C

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

variable (C)
def shift_cycles_functor_iso [abelian C] (n k m : ℤ) (h : k + n = m) :
  category_theory.shift_functor _ n ⋙ cycles_functor C (complex_shape.up ℤ) k ≅
    cycles_functor C _ m :=
(functor.associator _ _ _).symm ≪≫
  iso_whisker_right (shift_short_complex_functor_iso C _ _ _ h) _

variable {C}

lemma shift_cycles_functor_iso_hom_app [abelian C] (n k m : ℤ) (h : k + n = m)
  (K : cochain_complex C ℤ) :
    (shift_cycles_functor_iso C n k m h).hom.app K =
    short_complex.cycles_map ((shift_short_complex_functor_iso C n k m h).hom.app K) :=
id_comp _

lemma shift_cycles_functor_iso_hom_app_comp_cycles_i [abelian C] (n k m : ℤ) (h : k + n = m)
  (K : cochain_complex C ℤ) :
  (shift_cycles_functor_iso C n k m h).hom.app K ≫ K.cycles_i m =
  K⟦n⟧.cycles_i k ≫ (K.shift_functor_obj_X_iso n k m h.symm).hom :=
begin
  have eq := (short_complex.cycles_i_nat_trans C).naturality
    ((shift_short_complex_functor_iso C _ _ _ h).hom.app K),
  dsimp at eq,
  rw [shift_cycles_functor_iso_hom_app, eq],
  dsimp [shift_short_complex_functor_iso],
  simpa only [shift_eval_hom_app_eq],
end

lemma unshift_cocycle (K : cochain_complex C ℤ) (r : ℤ) {A : C} {n₀ : ℤ}
  (z : A ⟶ K⟦r⟧.X n₀) (n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
  (hz : z ≫ K⟦r⟧.d n₀ n₁ = 0) (n₀' : ℤ) (hn₀' : n₀' = n₀ + r) (n₁' : ℤ) :
  (z ≫ (K.shift_functor_obj_X_iso r n₀ n₀' hn₀').hom) ≫ K.d n₀' n₁' = 0 :=
begin
  by_cases hn₁' : n₁' = n₁ + r,
  { substs hn₀' hn₁',
    dsimp [homological_complex.X_iso_of_eq, iso.refl] at ⊢ hz,
    rw [linear.comp_smul] at hz,
    erw [assoc, id_comp, ← cancel_epi (preadditive.mul_iso ((-1 : units ℤ)^r) (iso.refl A)).hom,
      comp_zero, preadditive.mul_iso_hom, iso.refl_hom, preadditive.zsmul_comp, id_comp, hz], },
  { rw [K.shape, comp_zero],
    change _ ≠ _,
    exact λ h, hn₁' (by linarith), },
end

@[reassoc]
lemma shift_lift_cycles (K : cochain_complex C ℤ) (r : ℤ) {A : C} {n₀ : ℤ}
  (z : A ⟶ K⟦r⟧.X n₀) (n₁ : ℤ) (hn₁ : (complex_shape.up ℤ).rel n₀ n₁)
    (hz : z ≫ K⟦r⟧.d n₀ n₁ = 0) (n₀' : ℤ) (hn₀' : n₀' = n₀ + r) :
    homological_complex.lift_cycles (K⟦r⟧) z n₁ hn₁ hz =
      K.lift_cycles (z ≫ (K.shift_functor_obj_X_iso r n₀ n₀' hn₀').hom) (n₀'+1) rfl
      (K.unshift_cocycle r z n₁ hn₁.symm hz n₀' hn₀' _) ≫
      (shift_cycles_functor_iso C r n₀ n₀' hn₀'.symm).inv.app K :=
begin
  simp only [← cancel_mono ((shift_cycles_functor_iso C r n₀ n₀' hn₀'.symm).hom.app K), assoc,
    iso.inv_hom_id_app, ← cancel_mono (homological_complex.cycles_i K n₀')],
  dsimp,
  simpa only [id_comp, homological_complex.lift_cycles_i,
    shift_cycles_functor_iso_hom_app_comp_cycles_i _ _ _  hn₀'.symm K,
    homological_complex.lift_cycles_i_assoc],
end

@[reassoc]
lemma shift_homology_π (K : cochain_complex C ℤ) (r n₀ n₀': ℤ) (hn₀' : n₀' = n₀ + r) :
  homological_complex.homology_π
    ((category_theory.shift_functor (cochain_complex C ℤ) r).obj K) n₀ =
    (shift_cycles_functor_iso C r n₀ n₀' hn₀'.symm).hom.app K ≫
      homological_complex.homology_π K n₀' ≫
      (shift_homology_functor_iso C r n₀ n₀' hn₀'.symm).inv.app K :=
begin
  simp only [← cancel_mono ((shift_homology_functor_iso C r n₀ n₀' hn₀'.symm).hom.app K),
    assoc, iso.inv_hom_id_app, shift_cycles_functor_iso_hom_app],
  erw comp_id,
  simpa only [shift_homology_functor_iso_hom_app]
    using short_complex.homology_π_naturality
      ((shift_short_complex_functor_iso C r n₀ n₀' hn₀'.symm).hom.app K),
end

@[reassoc]
lemma shift_lift_cycles_comp_homology_π (K : cochain_complex C ℤ) (r : ℤ) {A : C} {n₀ : ℤ}
  (z : A ⟶ K⟦r⟧.X n₀) (n₁ : ℤ) (hn₁ : (complex_shape.up ℤ).rel n₀ n₁)
    (hz : z ≫ K⟦r⟧.d n₀ n₁ = 0) (n₀' : ℤ) (hn₀' : n₀' = n₀ + r) :
  homological_complex.lift_cycles (K⟦r⟧) z n₁ hn₁ hz ≫ K⟦r⟧.homology_π n₀ =
  K.lift_cycles (z ≫ (K.shift_functor_obj_X_iso r n₀ n₀' hn₀').hom) (n₀'+1) rfl
    (K.unshift_cocycle r z n₁ hn₁.symm hz n₀' hn₀' _) ≫
    K.homology_π n₀' ≫ (shift_homology_functor_iso C r n₀ n₀' hn₀'.symm).inv.app K :=
by simp only [shift_lift_cycles K r z n₁ hn₁ hz n₀' hn₀', assoc,
  shift_homology_π K r n₀ n₀' hn₀', iso.inv_hom_id_app_assoc]

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

end homology_sequence


variables {C} {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

lemma from_mapping_cone_of_ses_comp_δ (n₀ n₁ : ℤ) (h : n₁ = n₀ + 1) :
  homology_map (cochain_complex.from_mapping_cone_of_ses ex) n₀ ≫
    homology_sequence.δ ex n₀ n₁ h =
  homology_map (mapping_cone.δ S.f) n₀ ≫
    (shift_homology_functor_iso C 1 n₀ n₁ h.symm).hom.app S.X₁ :=
begin
  dsimp only [homology_sequence.δ, derived_category.homology_sequence.δ,
    derived_category.triangle_of_ses, triangle.mk, derived_category.triangle_of_ses_δ,
    derived_category.mapping_cone_triangle, derived_category.mapping_cone_δ],
  simp only [assoc, derived_category.homology_functor_factors_inv_naturality_assoc,
    functor.map_comp, functor.map_inv, is_iso.hom_inv_id_assoc,
    derived_category.shift_homology_functor_iso_hom_app_Q_obj,
    iso.inv_hom_id_app, comp_id],
  simp only [← functor.map_comp_assoc, iso.hom_inv_id_app, functor.map_comp],
  erw [category_theory.functor.map_id, comp_id,
    ← derived_category.homology_functor_factors_inv_naturality_assoc,
    iso.inv_hom_id_app_assoc],
end

namespace mapping_cone

open hom_complex

@[simp, reassoc]
lemma cycles_i_fst_d {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n₀ n₁ n₂ : ℤ) (h : n₁ = n₀ + 1) :
  (mapping_cone φ).cycles_i n₀ ≫ (fst φ : cochain (mapping_cone φ) K 1).v n₀ n₁ h ≫
    K.d n₁ n₂ = 0 :=
begin
  by_cases hn₂ : n₁ + 1 = n₂,
  { have eq := (mapping_cone φ).cycles_i_d n₀ n₁,
    simpa only [assoc, d_fst _ _ _ _ h, zero_comp, preadditive.comp_neg, neg_eq_zero]
      using eq =≫ (fst φ : cochain (mapping_cone φ) K 1).v n₁ n₂ hn₂.symm, },
  { simp only [K.shape _ _ hn₂, comp_zero], },
end

lemma homology_map_δ_on_a_cocycle {K L : cochain_complex C ℤ} (φ : K ⟶ L) {A : C} {n₀ : ℤ}
  (z : A ⟶ (mapping_cone φ).cycles n₀) (n₁ : ℤ) (h : n₁ = n₀ + 1) :
  z ≫ (mapping_cone φ).homology_π n₀ ≫ homology_map (mapping_cone.δ φ) n₀ ≫
    (shift_homology_functor_iso C 1 n₀ n₁ h.symm).hom.app K =
    K.lift_cycles (-z ≫ (mapping_cone φ).cycles_i n₀ ≫
      (mapping_cone.fst φ : cochain (mapping_cone φ) K 1).v n₀ n₁ h) (n₁+1) rfl (by simp) ≫
      K.homology_π n₁ :=
begin
  obtain ⟨z, hz, rfl⟩ := (mapping_cone φ).eq_lift_cycles_i z n₁ h.symm,
  obtain ⟨x, y, eq⟩ := to_decomposition z n₁ h,
  simp only [homological_complex.homology_π_naturality_assoc,
    homological_complex.lift_cycles_i_assoc,
    homological_complex.lift_cycles_comp_cycles_map_assoc,
    shift_lift_cycles_comp_homology_π_assoc _ 1 _ n₁ h.symm _ n₁ h,
    iso.inv_hom_id_app, δ, assoc, cocycle.hom_of_f, cocycle.right_shift_coe, δ_as_cocycle_coe,
    cochain.right_shift_v _ _ _ (zero_add 1).symm n₀ n₀ (add_zero n₀).symm (n₁) h,
    preadditive.neg_comp, preadditive.comp_neg, shift_functor_obj_X_iso, cochain.neg_v,
    iso.inv_hom_id],
  dsimp,
  simp only [comp_id],
end

end mapping_cone

namespace homology_sequence

open hom_complex

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
  haveI : mono (S.f.f (n₁+1)) :=
    (short_complex.short_exact.map_of_exact ex (homological_complex.eval _ _ (n₁+1))).mono_f,
  have hx₁' : x₁ ≫ S.X₁.d n₁ (n₁ + 1) = 0,
  { simp only [← cancel_mono (S.f.f (n₁+1)), assoc, ← S.f.comm, reassoc_of hx₁,
      homological_complex.d_comp_d, comp_zero, zero_comp], },
  let z : A ⟶ (mapping_cone S.f).cycles n₀ :=
    (mapping_cone S.f).lift_cycles
      (-x₁ ≫ (mapping_cone.inl S.f).v n₁ n₀ (by linarith)
        + x₂ ≫ (mapping_cone.inr S.f).f n₀) n₁ h.symm
      (by simp only [mapping_cone.to_ext_iff _ _ _ rfl,
        assoc, preadditive.add_comp, zero_comp, preadditive.comp_neg,
        preadditive.neg_comp, neg_neg, mapping_cone.inl_fst_assoc, comp_id,
        mapping_cone.d_fst _ _ _ _ h, hx₁', zero_add, mapping_cone.inr_fst_assoc,
        comp_zero, neg_zero, mapping_cone.d_snd _ _ _ h, preadditive.comp_add,
        mapping_cone.inr_snd_assoc, mapping_cone.inl_snd_assoc, hx₁, add_zero, neg_add_self,
        eq_self_iff_true, and_self]),
  have hz₁ : x₁ = -z ≫ homological_complex.cycles_i (mapping_cone S.f) n₀ ≫
    (mapping_cone.fst S.f : cochain (mapping_cone S.f) S.X₁ 1).v n₀ n₁ h,
  { simp only [add_zero, neg_neg, preadditive.add_comp, preadditive.neg_comp, assoc,
      comp_zero, homological_complex.lift_cycles_i_assoc, mapping_cone.inl_fst,
      comp_id, mapping_cone.inr_fst], },
  have hz₂ : z ≫ homological_complex.cycles_map (from_mapping_cone_of_ses ex) n₀ =
    homological_complex.lift_cycles S.X₃ x₃ n₁ h.symm hx₃,
  { rw ← cancel_mono (S.X₃.cycles_i n₀),
    simp only [zero_add, neg_zero, assoc, preadditive.add_comp, preadditive.neg_comp,
      comp_zero, inl_from_mapping_cone_of_ses, inr_from_mapping_cone_of_ses,
      homological_complex.lift_cycles_comp_cycles_map, homological_complex.lift_cycles_i, hx₂], },
  simp only [hz₁, reassoc_of hz₂, ← mapping_cone.homology_map_δ_on_a_cocycle S.f z n₁ h,
    ← from_mapping_cone_of_ses_comp_δ ex n₀ n₁ h,
    homological_complex.homology_π_naturality_assoc],
end

/- Actually, we probably need a more general homology sequence for any complex_shape, which
could be done using the snake lemma, and then `comp_δ_eq` would be used to prove
a comparison lemma between the two connecting maps... -/

end homology_sequence

end cochain_complex
