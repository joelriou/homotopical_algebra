import for_mathlib.algebra.homology.trunc
import for_mathlib.category_theory.localization.shift

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace category_theory

instance ess_surj_comp {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃] (F : C₁ ⥤ C₂)
  [ess_surj F] (G : C₂ ⥤ C₃) [ess_surj G] : ess_surj (F ⋙ G) :=
⟨λ Z, ⟨_, ⟨G.map_iso (F.obj_obj_preimage_iso (G.obj_preimage Z)) ≪≫ G.obj_obj_preimage_iso Z⟩⟩⟩

instance ess_surj_Q {C : Type*} [category C] (W : morphism_property C) :
  ess_surj (W.Q) :=
localization.ess_surj W.Q W

lemma full_of_comp_ess_surj {C D E : Type*} [category C] [category D] [category E]
  (F : C ⥤ D) (G : D ⥤ E) [ess_surj F]
  (h : ∀ (X Y : C), function.surjective (λ (f : F.obj X ⟶ F.obj Y), G.map f)) : full G :=
G.full_of_surjective (λ K₁ K₂ f, begin
  let K'₁ := F.obj_preimage K₁,
  let K'₂ := F.obj_preimage K₂,
  let e₁ : F.obj K'₁ ≅ K₁ := F.obj_obj_preimage_iso K₁,
  let e₂ : F.obj K'₂ ≅ K₂ := F.obj_obj_preimage_iso K₂,
  obtain ⟨f', hf'⟩ := h K'₁ K'₂ (G.map e₁.hom ≫ f ≫ G.map e₂.inv),
  dsimp at hf',
  refine ⟨e₁.inv ≫ f' ≫ e₂.hom, _⟩,
  simp only [G.map_comp, hf', assoc],
  rw [← G.map_comp, e₂.inv_hom_id, G.map_id, comp_id, ← G.map_comp_assoc, e₁.inv_hom_id, G.map_id,
    id_comp],
end)

lemma faithful_of_comp_ess_surj {C D E : Type*} [category C] [category D] [category E]
  (F : C ⥤ D) (G : D ⥤ E) [ess_surj F]
  (h : ∀ (X Y : C), function.injective (λ (f : F.obj X ⟶ F.obj Y), G.map f)) : faithful G :=
⟨λ K₁ K₂ f₁ f₂ hf, begin
  let K'₁ := F.obj_preimage K₁,
  let K'₂ := F.obj_preimage K₂,
  let e₁ : F.obj K'₁ ≅ K₁ := F.obj_obj_preimage_iso K₁,
  let e₂ : F.obj K'₂ ≅ K₂ := F.obj_obj_preimage_iso K₂,
  rw [← cancel_mono e₂.inv, ← cancel_epi e₁.hom],
  apply h,
  dsimp,
  simp only [hf, functor.map_comp],
end⟩

end category_theory

variables {C : Type*} [category C] [abelian C]

namespace derived_category

instance zero_is_le (n : ℤ) : (0 : derived_category C).is_le n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

instance zero_is_ge (n : ℤ) : (0 : derived_category C).is_ge n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

def is_plus (K : derived_category C) : Prop := ∃ (n : ℤ), K.is_ge n

def is_minus (K : derived_category C) : Prop := ∃ (n : ℤ), K.is_le n

variable (C)
open category_theory.triangulated

instance plus_is_triangulated_subcategory :
  is_triangulated_subcategory (λ (K : derived_category C), K.is_plus) :=
{ zero := ⟨0, infer_instance⟩,
  shift := begin
    rintros K k ⟨n, hn⟩,
    haveI := hn,
    exact ⟨n-k, shift_is_ge K n k (n-k) (by linarith)⟩,
  end,
  ext₂ := begin
    rintros T hT ⟨n₁, hn₁⟩ ⟨n₃, hn₃⟩,
    exact ⟨min n₁ n₃,
      ⟨λ n hn, short_complex.exact.is_zero_of_both_zeros (homology_sequence.ex₂ hT n)
        (is_zero.eq_of_src (hn₁.is_zero' _ (lt_of_lt_of_le hn (min_le_left n₁ n₃))) _ _)
        (is_zero.eq_of_tgt (hn₃.is_zero' _ (lt_of_lt_of_le hn (min_le_right n₁ n₃))) _ _)⟩⟩,
  end, }

abbreviation plus := full_subcategory (λ (K : derived_category C), K.is_plus)
abbreviation minus := full_subcategory (λ (K : derived_category C), K.is_minus)

namespace plus

instance : pretriangulated (plus C) := infer_instance

variable {C}

def mk (K : derived_category C) (n : ℤ) [hn : K.is_ge n] :
  derived_category.plus C :=
⟨K, n, hn⟩

def mk' (K : derived_category C) (hK : K.is_plus) :
  derived_category.plus C :=
⟨K, hK⟩

abbreviation ι : plus C ⥤ derived_category C :=
full_subcategory_inclusion _

end plus

end derived_category

namespace cochain_complex

def is_plus (K : cochain_complex C ℤ) : Prop :=
  ∃ (n : ℤ), K.is_strictly_ge n

def is_minus (K : cochain_complex C ℤ) : Prop :=
  ∃ (n : ℤ), K.is_strictly_le n

lemma is_plus.Q {K : cochain_complex C ℤ} (h : K.is_plus) :
  (derived_category.Q.obj K).is_plus :=
begin
  obtain ⟨n, hn⟩ := h,
  haveI := hn,
  exact ⟨n, infer_instance⟩,
end

instance zero_is_strictly_ge (n : ℤ) : is_strictly_ge (0 : cochain_complex C ℤ) n :=
⟨λ k hk, is_zero.of_iso (is_zero_zero _)
  (homological_complex.eval C (complex_shape.up ℤ) k).map_zero_object⟩

instance zero_is_strictly_le (n : ℤ) : is_strictly_le (0 : cochain_complex C ℤ) n :=
⟨λ k hk, is_zero.of_iso (is_zero_zero _)
  (homological_complex.eval C (complex_shape.up ℤ) k).map_zero_object⟩

lemma mapping_cone_is_strictly_le {K L : cochain_complex C ℤ} (f : K ⟶ L) (n k l : ℤ)
  [K.is_strictly_le k] [L.is_strictly_le l] (hk : k ≤ n+1) (hl : l ≤ n) :
  (mapping_cone f).is_strictly_le n :=
⟨λ i hi, begin
  simp only [mapping_cone.X_is_zero_iff],
  split,
  { exact is_strictly_le.is_zero K k (i+1) (by linarith), },
  { exact is_strictly_le.is_zero L l i (by linarith), },
end⟩

lemma mapping_cone_is_strictly_ge {K L : cochain_complex C ℤ} (f : K ⟶ L) (n k l : ℤ)
  [K.is_strictly_ge k] [L.is_strictly_ge l] (hk : n+1 ≤ k) (hl : n ≤ l) :
  (mapping_cone f).is_strictly_ge n :=
⟨λ i hi, begin
  simp only [mapping_cone.X_is_zero_iff],
  split,
  { exact is_strictly_ge.is_zero K k (i+1) (by linarith), },
  { exact is_strictly_ge.is_zero L l i (by linarith), },
end⟩

lemma mapping_cone_is_plus {K L : cochain_complex C ℤ} (f : K ⟶ L)
  (hK : K.is_plus) (hL : L.is_plus) : (mapping_cone f).is_plus :=
begin
  obtain ⟨k, hK⟩ := hK,
  obtain ⟨l, hL⟩ := hL,
  haveI := hK,
  haveI := hL,
  exact ⟨min (k-1) l, mapping_cone_is_strictly_ge f _ k l
    (by linarith [min_le_left (k-1) l]) (min_le_right _ _)⟩,
end

variable (C)
abbreviation plus :=
full_subcategory (λ (K : cochain_complex C ℤ), cochain_complex.is_plus K)
abbreviation minus :=
full_subcategory (λ (K : cochain_complex C ℤ), cochain_complex.is_minus K)

namespace plus

variable {C}

abbreviation ι : plus C ⥤ cochain_complex C ℤ :=
full_subcategory_inclusion _

variable (C)

def shift_functor (k : ℤ) : plus C ⥤ plus C :=
full_subcategory.lift _ (ι ⋙ shift_functor _ k) (λ K, begin
  obtain ⟨n, hn⟩ := K.2,
  haveI := hn,
  refine ⟨n-k, _⟩,
  dsimp,
  exact shift_is_strict_ge K.1 n k (n-k) (by linarith),
end)

instance : has_shift (plus C) ℤ :=
has_shift_of_fully_faithful ι (shift_functor C)
  (λ n, full_subcategory.lift_comp_inclusion _ _ _)

end plus

namespace minus

variable {C}

abbreviation ι : minus C ⥤ cochain_complex C ℤ :=
full_subcategory_inclusion _

end minus

end cochain_complex

open category_theory.triangulated

namespace homotopy_category

variable (C)

def is_plus : set (homotopy_category C (complex_shape.up ℤ)) :=
λ K, cochain_complex.is_plus K.1

abbreviation plus :=
full_subcategory (homotopy_category.is_plus C)

instance plus_is_triangulated_subcategory' :
  category_theory.triangulated.is_triangulated_subcategory' (is_plus C) :=
{ zero := begin
    refine ⟨⟨0⟩, _, ⟨0, infer_instance⟩⟩,
    rw is_zero.iff_id_eq_zero,
    change (homotopy_category.quotient _ _).map (𝟙 0) = 0,
    simp only [id_zero, functor.map_zero],
  end,
  shift := begin
    rintro ⟨X⟩ n hX,
    exact ((cochain_complex.plus.shift_functor C n).obj ⟨X, hX⟩).2,
  end,
  distinguished_cocone_triangle' := begin
    rintro ⟨X⟩ ⟨Y⟩ hX hY ⟨f : X ⟶ Y⟩,
    refine ⟨_, _, _, _, ⟨_, _, f, ⟨iso.refl _⟩⟩⟩,
    exact cochain_complex.mapping_cone_is_plus f hX hY,
  end, }

namespace plus

variable {C}

abbreviation ι : plus C ⥤ homotopy_category C (complex_shape.up ℤ) :=
full_subcategory_inclusion _

variable (C)

abbreviation homology_functor (n : ℤ) : plus C ⥤ C :=
ι ⋙ homotopy_category.homology_functor C (complex_shape.up ℤ) n

def shift_homology_functor_iso (n k m : ℤ) (h : k + n = m):
  shift_functor _ n ⋙ homology_functor C k ≅ homology_functor C m :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right (ι.comm_shift_iso n) _ ≪≫
  functor.associator _ _ _ ≪≫
  iso_whisker_left ι (homotopy_category.shift_homology_functor_iso C n k m h)

abbreviation acyclic : set (plus C) :=
(homology_functor C 0).kernel_of_is_homological

variable {C}

lemma mem_acyclic_W_iff {K L : plus C} (φ : K ⟶ L) :
  (subcategory.W (acyclic C)) φ ↔ ∀ (n : ℤ), is_iso ((homology_functor C n).map φ) :=
by simpa only [functor.kernel_of_is_homological_W,
  ← λ n, nat_iso.is_iso_map_iff (shift_homology_functor_iso C _ _ _ (zero_add n)) φ]

variable (C)

lemma homology_functor_is_inverted_by (n : ℤ) :
  (subcategory.W (acyclic C)).is_inverted_by (homology_functor C n) :=
λ K L f hf, begin
  rw mem_acyclic_W_iff f at hf,
  exact hf n,
end

variable {C}

lemma mem_W_iff_ι_map_mem {K L : homotopy_category.plus C} (f : K ⟶ L) :
  subcategory.W (homotopy_category.acyclic C) (homotopy_category.plus.ι.map f) ↔
  subcategory.W (homotopy_category.plus.acyclic C) f :=
by simpa only [homotopy_category.mem_acyclic_W_iff, homotopy_category.plus.mem_acyclic_W_iff]

variable (C)

def single_functor (n : ℤ) : C ⥤ homotopy_category.plus C :=
full_subcategory.lift _ (homological_complex.single C (complex_shape.up ℤ) n ⋙
  homotopy_category.quotient _ _) (λ X, ⟨n, by { dsimp, apply_instance, }⟩)

def single_functor_factors (n : ℤ) :
  single_functor C n ⋙ homotopy_category.plus.ι ≅
  (homological_complex.single C (complex_shape.up ℤ) n ⋙ homotopy_category.quotient _ _) :=
full_subcategory.lift_comp_inclusion _ _ _

instance single_functor_additive (n : ℤ) : (single_functor C n).additive :=
⟨λ K L f₁ f₂, homotopy_category.plus.ι.map_injective begin
  dsimp only [single_functor],
  simp only [full_subcategory.lift_map, functor.map_add],
end⟩

end plus

end homotopy_category

namespace derived_category

namespace plus

abbreviation Qh : homotopy_category.plus C ⥤ derived_category.plus C :=
full_subcategory.lift _ (homotopy_category.plus.ι ⋙ derived_category.Qh)
begin
  rintro ⟨⟨K⟩, n, hn⟩,
  refine ⟨n, (_ : (Q.obj K).is_ge n)⟩,
  rw ← cochain_complex.is_ge_iff_Q_obj_is_ge,
  dsimp at hn,
  haveI := hn,
  exact cochain_complex.is_ge_of_is_strictly_ge K n,
end

variable (C)

def Qh_comp_ι_iso : (Qh : _ ⥤ derived_category.plus C) ⋙ derived_category.plus.ι ≅
  homotopy_category.plus.ι ⋙ derived_category.Qh :=
full_subcategory.lift_comp_inclusion _ _ _

namespace Qh_is_localization

lemma inverts :
  (subcategory.W (homotopy_category.plus.acyclic C)).is_inverted_by Qh :=
λ K L f hf, begin
  haveI : is_iso (derived_category.plus.ι.map (Qh.map f)),
  { erw [is_iso_map_iff_of_nat_iso (Qh_comp_ι_iso C) f],
    dsimp only [functor.comp_map],
    apply localization.inverts derived_category.Qh (subcategory.W (homotopy_category.acyclic C)),
    simpa only [homotopy_category.plus.mem_W_iff_ι_map_mem] using hf, },
  exact is_iso_of_reflects_iso (Qh.map f) ι,
end

abbreviation L := localization.lift _ (inverts C) (subcategory.W (homotopy_category.plus.acyclic C)).Q

def L_iso : (subcategory.W (homotopy_category.plus.acyclic C)).Q ⋙ L C ≅ Qh :=
localization.lifting.iso (subcategory.W (homotopy_category.plus.acyclic C)).Q
  (subcategory.W (homotopy_category.plus.acyclic C)) _ _

lemma full_L : full (L C) :=
begin
  let F := (subcategory.W (homotopy_category.plus.acyclic C)).Q,
  haveI := localization.ess_surj F
    (subcategory.W (homotopy_category.plus.acyclic C)), -- should be an instance
  have hF : (subcategory.W (homotopy_category.plus.acyclic C)).is_inverted_by F :=
    localization.inverts _ _,
  apply category_theory.full_of_comp_ess_surj F,
  rintros ⟨⟨K₁ : cochain_complex C ℤ⟩, hK₁⟩ ⟨⟨K₂ : cochain_complex C ℤ⟩, hK₂⟩ f,
  have hK₁' := hK₁,
  have hK₂' := hK₂,
  obtain ⟨n₁, hn₁⟩ := hK₁',
  obtain ⟨n₂, hn₂⟩ := hK₂',
  let n := min n₁ n₂,
  haveI : K₁.is_strictly_ge n,
  { haveI := hn₁, exact cochain_complex.is_strictly_ge_of_le _ _ _ (min_le_left n₁ n₂), },
  haveI : K₂.is_strictly_ge n,
  { haveI := hn₂, exact cochain_complex.is_strictly_ge_of_le _ _ _ (min_le_right n₁ n₂), },
  let f' : Qh.obj ⟨⟨K₁⟩, hK₁⟩ ⟶ Qh.obj ⟨⟨K₂⟩, hK₂⟩ :=
    (L_iso C).inv.app _ ≫ f ≫ (L_iso C).hom.app _,
  let f'' : derived_category.Q.obj K₁ ⟶ derived_category.Q.obj K₂ := f',
  obtain ⟨K₃, hK₃', s, g, hs, fac⟩ := right_factorisation_of_is_strictly_ge f'' n,
  replace fac := (Q.map s) ≫= fac,
  rw is_iso.hom_inv_id_assoc at fac,
  haveI := hK₃',
  haveI := hs,
  have hK₃ : homotopy_category.is_plus C ⟨K₃⟩ := ⟨n, hK₃'⟩,
  let s' : (⟨_, hK₃⟩ : homotopy_category.plus C) ⟶ ⟨_, hK₁⟩ := (homotopy_category.quotient _ _).map s,
  let g' : (⟨_, hK₃⟩ : homotopy_category.plus C) ⟶ ⟨_, hK₂⟩ := (homotopy_category.quotient _ _).map g,
  haveI : is_iso (F.map s') := hF _ begin
    rw ← homotopy_category.plus.mem_W_iff_ι_map_mem,
    erw homotopy_category.map_quotient_W_iff,
    exact hs,
  end,
  refine ⟨inv (F.map s') ≫ F.map g', _⟩,
  dsimp only,
  erw [functor.map_comp, ← cancel_epi ((L C).map (F.map s')), ← functor.map_comp_assoc,
    is_iso.hom_inv_id, (L C).map_id, id_comp, ← cancel_epi ((L_iso C).inv.app ⟨_, hK₃⟩),
    ← (L_iso C).inv.naturality g', ← fac],
  dsimp only [f'', f'],
  erw [assoc, ← (L_iso C).inv.naturality_assoc s'],
  dsimp,
  conv_lhs { congr, skip, erw assoc, congr, skip, erw assoc, },
  erw [(L_iso C).hom_inv_id_app, comp_id],
  refl,
end

instance faithful_L : faithful (L C) :=
begin
  let F := (subcategory.W (homotopy_category.plus.acyclic C)).Q,
  haveI := localization.ess_surj F
    (subcategory.W (homotopy_category.plus.acyclic C)), -- should be an instance
  have hF : (subcategory.W (homotopy_category.plus.acyclic C)).is_inverted_by F :=
    localization.inverts _ _,
  apply category_theory.faithful_of_comp_ess_surj F,
  rintros ⟨⟨K₁ : cochain_complex C ℤ⟩, hK₁⟩ ⟨⟨K₂ : cochain_complex C ℤ⟩, hK₂⟩,
  suffices : ∀ (f : F.obj {obj := {as := K₁}, property := hK₁} ⟶ F.obj {obj := {as := K₂}, property := hK₂})
    (hf : (L C).map f = 0), f = 0,
  { intros f₁ f₂ hf,
    rw [← sub_eq_zero],
    apply this,
    simpa only [functor.map_sub, sub_eq_zero] using hf, },
  intros f hf,
  obtain ⟨⟨⟨⟨K₁'⟩, hK₁'⟩, s, g, hs⟩, hz⟩ := right_calculus_of_fractions.L_map_fac F
    (subcategory.W (homotopy_category.plus.acyclic C)) f,
  dsimp [right_calculus_of_fractions.map_roof] at hz,
  simp only [hz, preadditive.is_iso.comp_left_eq_zero],
  obtain ⟨g, rfl⟩ := (homotopy_category.quotient _ _).map_surjective g,
  let g' : (⟨⟨K₁'⟩, hK₁'⟩ : homotopy_category.plus C) ⟶ ⟨⟨K₂⟩, hK₂⟩ :=
    (homotopy_category.quotient _ _).map g,
  have hg : derived_category.Qh.map g' = derived_category.Qh.map 0,
  { rw [hz, functor.map_comp, preadditive.is_iso.comp_left_eq_zero] at hf,
    simpa only [functor.comp_map, functor.map_zero, hf, zero_comp,
      preadditive.is_iso.comp_left_eq_zero] using ((L_iso C).hom.naturality g').symm, },
  rw left_calculus_of_fractions.L_map_eq_iff derived_category.Qh
    (subcategory.W (homotopy_category.acyclic C)) at hg,
  obtain ⟨⟨K₂' : cochain_complex C ℤ⟩, s, hs, fac⟩ := hg,
  obtain ⟨s, rfl⟩ := (homotopy_category.quotient _ _).map_surjective s,
  have hK₂' := hK₂,
  obtain ⟨n, hn : K₂.is_strictly_ge n⟩ := hK₂',
  rw zero_comp at fac,
  let t : (⟨⟨K₂⟩, hK₂⟩ : homotopy_category.plus C) ⟶ ⟨⟨K₂'.trunc_ge n⟩, ⟨n, infer_instance⟩⟩ :=
    (homotopy_category.quotient _ _).map (s ≫ cochain_complex.trunc_ge.π K₂' n),
  haveI : is_iso (F.map t),
  { apply hF,
    erw [← homotopy_category.plus.mem_W_iff_ι_map_mem, homotopy_category.map_quotient_W_iff],
    haveI : quasi_iso s,
    { simpa only [← homotopy_category.map_quotient_W_iff] using hs, },
    haveI : quasi_iso (cochain_complex.trunc_ge.π K₂' n),
    { rw [cochain_complex.quasi_iso_trunc_ge_π_iff, ← cochain_complex.is_ge_iff_of_quasi_iso s],
      apply_instance, },
    apply_instance, },
  simp only [← cancel_mono (F.map t), zero_comp, ← F.map_comp, ← F.map_zero],
  congr' 1,
  dsimp [t],
  erw [functor.map_comp, ← assoc, fac, zero_comp],
end

instance : ess_surj (L C) :=
⟨begin
  rintro ⟨K, hK⟩,
  let K' := Q.obj_preimage K,
  let e : Q.obj K' ≅ K := Q.obj_obj_preimage_iso K,
  obtain ⟨n, hn⟩ := hK,
  haveI := hn,
  haveI := (cochain_complex.is_ge_iff_Q_obj_is_ge K' n).2 (derived_category.is_ge.of_iso e.symm n),
  exact ⟨(morphism_property.Q _).obj ⟨⟨K'.trunc_ge n⟩, ⟨n, infer_instance⟩⟩,
    ⟨derived_category.plus.ι.preimage_iso (ι.map_iso ((L_iso C).app _) ≪≫
      (as_iso (Q.map (cochain_complex.trunc_ge.π K' n))).symm ≪≫ e)⟩⟩,
end⟩

lemma is_equivalence : is_equivalence (L C) :=
begin
  haveI := full_L C,
  exact equivalence.of_fully_faithfully_ess_surj _
end

instance : ess_surj (Qh : _ ⥤ derived_category.plus C) :=
ess_surj.of_iso (L_iso C)

end Qh_is_localization

instance Qh_is_localization :
  (Qh : _ ⥤ derived_category.plus C).is_localization
  (triangulated.subcategory.W (homotopy_category.plus.acyclic C)) :=
begin
  haveI := Qh_is_localization.is_equivalence C,
  refine functor.is_localization.of_equivalence
    (triangulated.subcategory.W (homotopy_category.plus.acyclic C)).Q
    (triangulated.subcategory.W (homotopy_category.plus.acyclic C)) Qh
    (Qh_is_localization.L C).as_equivalence _,
  dsimp only [functor.as_equivalence],
  exact localization.lifting.iso _ (subcategory.W (homotopy_category.plus.acyclic C)) _ _,
end

abbreviation single_functor (n : ℤ) : C ⥤ derived_category.plus C :=
homotopy_category.plus.single_functor C n ⋙ derived_category.plus.Qh

def homology_functor (n : ℤ) : derived_category.plus C ⥤ C :=
derived_category.plus.ι ⋙ derived_category.homology_functor C n

instance homology_functor_additive (n : ℤ) : (homology_functor C n).additive :=
by { dsimp only [homology_functor], apply_instance, }

instance homology_functor_is_homological (n : ℤ) : (homology_functor C n).is_homological :=
by { dsimp only [homology_functor], apply_instance, }

variable {C}

def triangle_of_ses {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)
  (h₁ : S.X₁.is_plus) (h₂ : S.X₂.is_plus) (h₃ : S.X₃.is_plus) :
    pretriangulated.triangle (derived_category.plus C) :=
pretriangulated.full_subcategory_lift_triangle _ (derived_category.triangle_of_ses ex)
  h₁.Q h₂.Q h₃.Q

lemma triangle_of_ses_dist {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)
  (h₁ : S.X₁.is_plus) (h₂ : S.X₂.is_plus) (h₃ : S.X₃.is_plus) :
  triangle_of_ses ex h₁ h₂ h₃ ∈ dist_triang (derived_category.plus C) :=
begin
  change (full_subcategory_inclusion _).map_triangle.obj (triangle_of_ses ex h₁ h₂ h₃)
    ∈ dist_triang (derived_category C),
  refine pretriangulated.isomorphic_distinguished _ (derived_category.triangle_of_ses_dist ex) _
    (pretriangulated.full_subcategory_lift_triangle_iso derived_category.is_plus
    (derived_category.triangle_of_ses ex) _ _ _),
end

end plus

end derived_category
