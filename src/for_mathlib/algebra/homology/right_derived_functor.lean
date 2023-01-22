import for_mathlib.algebra.homology.derivability_structure_injective
import for_mathlib.category_theory.abelian.extensions_derived_category

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C D : Type*} [category C] [category D] [abelian C] [abelian D]
  (F : C ⥤ D) [functor.additive F]

namespace functor

section

variables {ι : Type*} (c : complex_shape ι) (n : ι)

def single_comp_map_homological_complex_app [decidable_eq ι] (X : C) :
  (F.map_homological_complex c).obj ((homological_complex.single C c n).obj X) ≅
    (homological_complex.single D c n).obj (F.obj X) :=
homological_complex.hom.iso_of_components
(λ i, begin
  by_cases i = n,
  { exact eq_to_iso (by { dsimp, simp only [if_pos h], }), },
  { dsimp,
    simp only [if_neg h],
    exact F.map_zero_object, },
end)
(λ i j hij, begin
  dsimp,
  simp only [F.map_zero, zero_comp, comp_zero],
end)

def single_comp_map_homological_complex [decidable_eq ι] :
  homological_complex.single C c n ⋙ F.map_homological_complex c ≅
    F ⋙ homological_complex.single D c n :=
nat_iso.of_components (F.single_comp_map_homological_complex_app c n)
(λ X Y f, begin
  ext i,
  dsimp [single_comp_map_homological_complex_app],
  by_cases i = n,
  { simp only [dif_pos h, map_comp, eq_to_iso.hom, assoc, eq_to_hom_trans_assoc,
      eq_to_hom_map, eq_to_hom_trans], },
  { simp only [dif_neg h, F.map_zero, zero_comp, comp_zero], },
end)

variable {c}

lemma _root_.homotopy_category_quotient_map_functor_map_homological_complex
  {K L : homological_complex C c} (f : K ⟶ L) (F : C ⥤ D) [F.additive] :
  (homotopy_category.quotient D c).map ((F.map_homological_complex c).map f) =
    (map_homotopy_category c F).map ((homotopy_category.quotient C c).map f) :=
begin
  apply homotopy_category.eq_of_homotopy,
  apply F.map_homotopy,
  apply homotopy_category.homotopy_of_eq,
  simp only [homotopy_category.quotient_map_out],
end

end

instance map_is_strictly_ge (X : cochain_complex C ℤ) (n : ℤ) [X.is_strictly_ge n] :
  cochain_complex.is_strictly_ge ((F.map_homological_complex _ ).obj X) n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero D)
  (F.map_iso (cochain_complex.is_strictly_ge.is_zero X n i hi).iso_zero ≪≫ F.map_zero_object)⟩

lemma _root_.cochain_complex.is_plus.map {X : cochain_complex C ℤ} (h : X.is_plus)
  (F : C ⥤ D) [functor.additive F] :
  cochain_complex.is_plus ((map_homological_complex F (complex_shape.up ℤ)).obj X) :=
begin
  obtain ⟨n, hn⟩ := h,
  haveI := hn,
  exact ⟨n, infer_instance⟩,
end

def map_homotopy_category_factors :
  homotopy_category.quotient _ _ ⋙ map_homotopy_category (complex_shape.up ℤ) F ≅
    F.map_homological_complex _ ⋙ homotopy_category.quotient _ _ :=
nat_iso.of_components (λ K, iso.refl _)
(λ K L f, begin
  dsimp only [iso.refl, functor.comp_map],
  rw [id_comp, comp_id],
  apply homotopy_category.eq_of_homotopy,
  apply F.map_homotopy,
  apply homotopy_category.homotopy_of_eq,
  simp only [homotopy_category.quotient_map_out],
end)

instance map_homotopy_category_has_comm_shift :
  (functor.map_homotopy_category (complex_shape.up ℤ) F).has_comm_shift ℤ :=
@quotient.has_comm_shift _ _ _ _ _ _ _ F.map_homotopy_category_factors ℤ
  _ _ _ (infer_instance : has_shift (homotopy_category C (complex_shape.up ℤ)) ℤ)
  (infer_instance : (homotopy_category.quotient _ _).has_comm_shift ℤ) _

instance : nat_trans.respects_comm_shift F.map_homotopy_category_factors.hom ℤ :=
⟨λ n, begin
  ext K,
  dsimp only [map_homotopy_category_factors, nat_iso.of_components, whisker_right,
    nat_trans.comp_app, iso.refl, whisker_left],
  erw [functor.map_id, comp_id, id_comp],
  apply homotopy_category.eq_of_homotopy,
  erw [id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp,
    comp_id, comp_id, comp_id],
  apply homotopy_category.homotopy_of_eq,
  simp only [functor.map_comp, homotopy_category.quotient_map_out,
    homotopy_category_quotient_map_functor_map_homological_complex, iso.symm_hom,
    ← functor.map_comp_assoc],
  erw [← functor.map_comp, iso.hom_inv_id_app, functor.map_id, id_comp],
end⟩

def map_homotopy_category_plus : homotopy_category.plus C ⥤ homotopy_category.plus D :=
full_subcategory.lift _ (homotopy_category.plus.ι ⋙ functor.map_homotopy_category _ F)
  (λ K, cochain_complex.is_plus.map K.2 F)

def map_homotopy_category_plus_factors :
  F.map_homotopy_category_plus ⋙ homotopy_category.plus.ι ≅
    homotopy_category.plus.ι ⋙ functor.map_homotopy_category _ F :=
full_subcategory.lift_comp_inclusion _ _ _


instance map_homotopy_category_is_triangulated :
  (map_homotopy_category (complex_shape.up ℤ) F).is_triangulated :=
⟨λ T hT, begin
  rw homotopy_category.triangle_distinguished_iff at hT ⊢,
  obtain ⟨K, L, f, ⟨e⟩⟩ := hT,
  exact ⟨_, _, (F.map_homological_complex _).map f,
    ⟨(map_homotopy_category (complex_shape.up ℤ) F).map_triangle.map_iso e ≪≫
    (map_triangle_comp (homotopy_category.quotient C (complex_shape.up ℤ))
    (map_homotopy_category (complex_shape.up ℤ) F)).symm.app _ ≪≫
    (map_triangle_nat_iso F.map_homotopy_category_factors).app _ ≪≫
    (map_triangle_comp (F.map_homological_complex (complex_shape.up ℤ))
    (homotopy_category.quotient D (complex_shape.up ℤ))).app _ ≪≫
    (homotopy_category.quotient D (complex_shape.up ℤ)).map_triangle.map_iso
      (cochain_complex.mapping_cone.triangle_map_iso f F)⟩⟩,
end⟩

instance map_homotopy_category_plus_has_comm_shift :
  (functor.map_homotopy_category_plus F).has_comm_shift ℤ :=
by { dsimp only [map_homotopy_category_plus], apply_instance, }

instance map_homotopy_category_plus_is_triangulated :
  (functor.map_homotopy_category_plus F).is_triangulated :=
by { dsimp only [map_homotopy_category_plus], apply_instance, }

variable [hF : (functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh).has_right_derived_functor
    (triangulated.subcategory.W (homotopy_category.plus.acyclic C))]

include hF

abbreviation right_derived_functor_plus : derived_category.plus C ⥤ derived_category.plus D :=
  (functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh).right_derived_functor derived_category.plus.Qh
      (triangulated.subcategory.W (homotopy_category.plus.acyclic C))

def right_derived_functor_plus_αh :
  functor.map_homotopy_category_plus F ⋙
    derived_category.plus.Qh ⟶ derived_category.plus.Qh ⋙
      right_derived_functor_plus F :=
functor.right_derived_functor_α _ _ _

def abelian_right_derived_functor (n : ℕ) : C ⥤ D :=
derived_category.plus.single_functor C 0 ⋙ right_derived_functor_plus F ⋙
  derived_category.plus.homology_functor D (n : ℤ)

instance abelian_right_derived_functor_additive (n : ℕ)
  [F.right_derived_functor_plus.is_triangulated] :
  (F.abelian_right_derived_functor n).additive :=
by { dsimp only [abelian_right_derived_functor], apply_instance, }

omit hF
instance single_functor_is_termwise_injective (X : C) (n : ℤ) [injective X] :
  ((homotopy_category.plus.single_functor C n).obj X).obj.as.is_termwise_injective :=
begin
  change ((homological_complex.single C (complex_shape.up ℤ) n).obj X).is_termwise_injective,
  apply_instance,
end

instance (X : homotopy_category.plus C) [X.obj.as.is_termwise_injective]
  [enough_injectives C] :
  is_iso (F.right_derived_functor_plus_αh.app X) :=
by { dsimp only [right_derived_functor_plus_αh], apply_instance, }

def map_homotopy_plus_single_functor_homology_iso_zero :
  F ≅ homotopy_category.plus.single_functor C 0 ⋙ F.map_homotopy_category_plus ⋙
    derived_category.plus.Qh ⋙ derived_category.plus.homology_functor D 0 :=
begin
  change F ≅ homotopy_category.plus.single_functor C 0 ⋙ F.map_homotopy_category_plus ⋙
    derived_category.plus.Qh ⋙ derived_category.plus.ι ⋙ derived_category.homology_functor D 0,
  refine F.right_unitor.symm ≪≫
    iso_whisker_left F (homological_complex.single_homology_functor_iso D (complex_shape.up ℤ) 0).symm ≪≫
    (functor.associator _ _ _).symm ≪≫
    iso_whisker_right (F.single_comp_map_homological_complex (complex_shape.up ℤ) 0).symm
      (homology_functor D (complex_shape.up ℤ) 0) ≪≫
    functor.associator _ _ _ ≪≫ iso_whisker_left _ _ ≪≫ (functor.associator _ _ _).symm ≪≫
    iso_whisker_right (homotopy_category.plus.single_functor_factors C 0).symm _ ≪≫
    functor.associator _ _ _ ≪≫ iso_whisker_left _ (functor.associator _ _ _).symm ≪≫
    iso_whisker_left _ (iso_whisker_right (F.map_homotopy_category_plus_factors).symm _
      ≪≫ functor.associator _ _ _ ≪≫ iso_whisker_left _ (functor.associator _ _ _).symm) ≪≫
    iso_whisker_left _ (iso_whisker_left _
      (iso_whisker_right (derived_category.plus.Qh_comp_ι_iso D).symm
      (derived_category.homology_functor D 0) ≪≫ functor.associator _ _ _)),
  refine iso_whisker_left _ _ ≪≫ (functor.associator _ _ _).symm ≪≫
    iso_whisker_right F.map_homotopy_category_factors.symm _ ≪≫
    functor.associator _ _ _,
  refine (homotopy_category.homology_factors D (complex_shape.up ℤ) 0).symm ≪≫
    iso_whisker_left _ (derived_category.homology_functor_factors_Qh D 0).symm,
end

include hF

def abelian_right_derived_functor_α : F ⟶ F.abelian_right_derived_functor 0 :=
begin
  refine _ ≫ whisker_right (whisker_left (homotopy_category.plus.single_functor C 0)
    F.right_derived_functor_plus_αh) (derived_category.plus.homology_functor D 0) ≫ 𝟙 _,
  { exact F.map_homotopy_plus_single_functor_homology_iso_zero.hom, },
end

lemma abelian_right_derived_functor_α_app (X : C) :
  F.abelian_right_derived_functor_α.app X =
  F.map_homotopy_plus_single_functor_homology_iso_zero.hom.app X ≫
    (derived_category.plus.homology_functor D 0).map
      (F.right_derived_functor_plus_αh.app ((homotopy_category.plus.single_functor C 0).obj X)) :=
begin
  dsimp only [abelian_right_derived_functor_α, whisker_right, whisker_left,
    nat_trans.comp_app, nat_trans.id_app],
  rw comp_id,
end

instance is_iso_abelian_right_derived_functor_plus_α_app (X : C) [injective X] [enough_injectives C] :
  is_iso (F.abelian_right_derived_functor_α.app X) :=
begin
  rw abelian_right_derived_functor_α_app,
  apply_instance,
end

lemma abelian_right_derived_functor_obj_is_zero_of_injective'
  (X : C) [injective X] [enough_injectives C] (n : ℕ) (hn : 1 ≤ n) :
  limits.is_zero ((F.abelian_right_derived_functor n).obj X) :=
begin
  refine is_zero.of_iso _ (((derived_category.plus.homology_functor D n).map_iso
    (as_iso (F.right_derived_functor_plus_αh.app
      ((homotopy_category.plus.single_functor C 0).obj X)))).symm),
  have h : limits.is_zero ((derived_category.homology_functor D n).obj
    ((derived_category.single_functor D 0).obj (F.obj X))),
  { apply derived_category.is_le.is_zero _ 0,
    rw ← int.coe_nat_le_coe_nat_iff at hn,
    rw [algebra_map.coe_one] at hn,
    linarith, },
  refine is_zero.of_iso h ((derived_category.homology_functor D ↑n).map_iso _),
  sorry,
end

lemma abelian_right_derived_functor_obj_is_zero_of_injective (X : C)
  [injective X] [enough_injectives C] (n : ℕ) :
  limits.is_zero ((F.abelian_right_derived_functor (n+1)).obj X) :=
abelian_right_derived_functor_obj_is_zero_of_injective' _ _ _ (by linarith)

namespace abelian_right_derived_functor_homology_sequence

variables {S : short_complex C} (ex : S.short_exact) (n : ℕ )

def triangle : pretriangulated.triangle (derived_category.plus D) :=
F.right_derived_functor_plus.map_triangle.obj (derived_category.plus.triangle_of_ses
  (short_complex.short_exact.map_of_exact ex (homological_complex.single C (complex_shape.up ℤ) 0))
  (by { dsimp, exact ⟨0, infer_instance⟩, })
  (by { dsimp, exact ⟨0, infer_instance⟩, })
  (by { dsimp, exact ⟨0, infer_instance⟩, }))

def triangle' : pretriangulated.triangle (derived_category D) :=
derived_category.plus.ι.map_triangle.obj (triangle F ex)

variable [F.right_derived_functor_plus.is_triangulated]

lemma triangle_mem : (triangle F ex).distinguished :=
F.right_derived_functor_plus.map_distinguished _
  (derived_category.plus.triangle_of_ses_dist _ _ _ _)

lemma triangle'_mem : (triangle' F ex).distinguished :=
derived_category.plus.ι.map_distinguished _ (triangle_mem F ex)

lemma ex₂ (n : ℕ) :
  (short_complex.mk ((F.abelian_right_derived_functor n).map S.f)
    ((F.abelian_right_derived_functor n).map S.g)
    (by { rw [← functor.map_comp, S.zero, functor.map_zero], })).exact :=
derived_category.homology_sequence.ex₂ (triangle'_mem F ex) n

def δ (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (F.abelian_right_derived_functor n₀).obj S.X₃ ⟶ (F.abelian_right_derived_functor n₁).obj S.X₁ :=
derived_category.homology_sequence.δ (triangle'_mem F ex) n₀ n₁ (by simp [h])

@[simp, reassoc]
lemma δ_comp (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  δ F ex n₀ n₁ h ≫ (F.abelian_right_derived_functor n₁).map S.f = 0 :=
derived_category.homology_sequence.δ_comp (triangle'_mem F ex) n₀ n₁ (by simp [h])

@[simp, reassoc]
lemma comp_δ (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
   (F.abelian_right_derived_functor n₀).map S.g ≫ δ F ex n₀ n₁ h = 0 :=
derived_category.homology_sequence.comp_δ (triangle'_mem F ex) n₀ n₁ (by simp [h])

lemma ex₃ (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (short_complex.mk ((F.abelian_right_derived_functor n₀).map S.g) (δ F ex n₀ n₁ h)
    (by simp)).exact :=
derived_category.homology_sequence.ex₃ (triangle'_mem F ex) n₀ n₁ (by simp [h])

lemma ex₁ (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (short_complex.mk (δ F ex n₀ n₁ h) ((F.abelian_right_derived_functor n₁).map S.f)
    (by simp)).exact :=
derived_category.homology_sequence.ex₁ (triangle'_mem F ex) n₀ n₁ (by simp [h])

end abelian_right_derived_functor_homology_sequence

-- TODO:
-- * show that total_right_derived_functor is a triangulated functor
-- * deduce the long exact sequence attached to a short exact sequence in C
-- * define the natural transformation F ⟶ R^0 F, and show that when F is
--      left exact, it is an isomorphism using an injective resolution

end functor


end category_theory
