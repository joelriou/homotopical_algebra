import for_mathlib.algebra.homology.derived_category_plus
import for_mathlib.algebra.homology.k_injective
import category_theory.preadditive.injective

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace category_theory.morphism_property

instance isomorphism_contains_identities {C : Type*} [category C] :
  (isomorphisms C).contains_identities :=
{ id := λ X, by { rw isomorphisms.iff, apply_instance, }, }

instance isomorphism_multiplicative {C : Type*} [category C] :
  (isomorphisms C).multiplicative :=
{ contains_identities := infer_instance,
  comp := λ X Y Z f g hf hg, begin
    rw isomorphisms.iff at hf hg ⊢,
    haveI := hf,
    haveI := hg,
    apply_instance,
  end, }

end category_theory.morphism_property

variables {C ι : Type*} [category C] [abelian C] {c : complex_shape ι}

namespace homological_complex

class is_termwise_injective (K : homological_complex C c) : Prop :=
(X_injective [] : ∀ (n : ι), injective (K.X n))

instance (K : homological_complex C c) (n : ι) [K.is_termwise_injective] : injective (K.X n) :=
is_termwise_injective.X_injective K n

instance zero_is_termwise_injective :
  (0 : homological_complex C c).is_termwise_injective :=
⟨λ n, injective.of_iso (homological_complex.eval C c n).map_zero_object.symm
  infer_instance⟩

end homological_complex

namespace cochain_complex

@[simp]
lemma shift_is_termwise_injective_iff
  (K : cochain_complex C ℤ) (n : ℤ) :
  homological_complex.is_termwise_injective (K⟦n⟧) ↔
  homological_complex.is_termwise_injective K :=
begin
  split,
  { introI,
    refine ⟨λ i, _⟩,
    obtain ⟨m, rfl⟩ : ∃ (m : ℤ), i = m+n := ⟨i-n, by simp⟩,
    have h := homological_complex.is_termwise_injective.X_injective (K⟦n⟧) m,
    exact h, },
  { introI,
    refine ⟨λ i, _⟩,
    apply homological_complex.is_termwise_injective.X_injective K _, },
end

instance mapping_cone_is_termwise_injective {K L : cochain_complex C ℤ} (f : K ⟶ L)
  [K.is_termwise_injective] [L.is_termwise_injective] :
  (mapping_cone f).is_termwise_injective :=
⟨λ n, by { dsimp [mapping_cone], apply_instance, }⟩

end cochain_complex

namespace homotopy_category

namespace plus


variables (C)

abbreviation termwise_injective :=
  full_subcategory (λ (K : homotopy_category.plus C), K.obj.as.is_termwise_injective)

namespace termwise_injective

variable {C}

abbreviation ι : termwise_injective C ⥤ homotopy_category.plus C :=
full_subcategory_inclusion _

instance is_triangulated_subcategory' :
  triangulated.is_triangulated_subcategory'
    (λ (K : homotopy_category.plus C), K.obj.as.is_termwise_injective) :=
{ zero := begin
    refine ⟨⟨⟨0⟩, ⟨0, infer_instance⟩⟩, _, homological_complex.zero_is_termwise_injective⟩,
    rw limits.is_zero.iff_id_eq_zero,
    change (homotopy_category.quotient C (complex_shape.up ℤ)).map (𝟙 0) = 0,
    simp only [limits.id_zero, functor.map_zero],
  end,
  shift := begin
    rintro ⟨⟨K⟩, hK⟩ n h,
    change K⟦n⟧.is_termwise_injective,
    simpa only [cochain_complex.shift_is_termwise_injective_iff] using h,
  end,
  distinguished_cocone_triangle' := begin
    rintro ⟨⟨K : cochain_complex C ℤ⟩, hK⟩ ⟨⟨L : cochain_complex C ℤ⟩, hL⟩ hK' hL',
    haveI : K.is_termwise_injective := hK',
    haveI : L.is_termwise_injective := hL',
    rintro (f : (homotopy_category.quotient _ _).obj K ⟶ (homotopy_category.quotient _ _).obj L),
    obtain ⟨f, rfl⟩ := (homotopy_category.quotient _ _).map_surjective f,
    exact ⟨⟨(homotopy_category.quotient _ _).obj (cochain_complex.mapping_cone f),
      cochain_complex.mapping_cone_is_plus f hK hL⟩,
      (infer_instance : (cochain_complex.mapping_cone f).is_termwise_injective),
      (homotopy_category.quotient _ _).map (cochain_complex.mapping_cone.inr f),
      (homotopy_category.quotient _ _).map (cochain_complex.mapping_cone.δ f),
      by { erw triangle_distinguished_iff, exact ⟨_, _, f, ⟨iso.refl _⟩⟩, }⟩,
  end, }

def Φ : localizor_morphism (morphism_property.isomorphisms (termwise_injective C))
  (triangulated.subcategory.W (homotopy_category.plus.acyclic C)) :=
{ functor := termwise_injective.ι,
  mapW := λ X Y f hf, begin
    rw morphism_property.isomorphisms.iff at hf,
    haveI := hf,
    rw ← triangulated.subcategory.is_iso_map_iff (acyclic C) derived_category.plus.Qh,
    apply_instance,
  end, }

instance Φ_functor_has_comm_shift :
  (Φ : localizor_morphism (morphism_property.isomorphisms
    (termwise_injective C)) _).functor.has_comm_shift ℤ :=
by { dsimp only [Φ], apply_instance, }

instance Φ_functor_is_triangulated :
  (Φ : localizor_morphism (morphism_property.isomorphisms
    (termwise_injective C)) _).functor.is_triangulated :=
by { dsimp only [Φ], apply_instance, }

def Qh : termwise_injective C ⥤ derived_category.plus C :=
termwise_injective.ι ⋙ derived_category.plus.Qh

instance Qh_has_comm_shift : (Qh : _ ⥤ derived_category.plus C).has_comm_shift ℤ :=
by { dsimp only [Qh], apply_instance, }

instance Qh_is_triangulated : (Qh : _ ⥤ derived_category.plus C).is_triangulated :=
by { dsimp only [Qh], apply_instance, }

instance is_K_injective_of_termwise_injective_of_is_plus (K : termwise_injective C) :
  K.obj.obj.is_K_injective :=
begin
  rw is_K_injective_iff',
  haveI := K.property,
  obtain ⟨n, hn⟩ := K.obj.property,
  haveI := hn,
  exact cochain_complex.is_K_injective_of_bounded_below_of_injective K.obj.obj.as n,
end

instance : faithful (Qh : _ ⥤ derived_category.plus C) :=
⟨λ K L, (derived_category.Qh_map_bijective_of_is_K_injective K.obj.obj L.obj.obj).1⟩

instance : full (Qh : _ ⥤ derived_category.plus C) :=
functor.full_of_surjective _
  (λ K L, (derived_category.Qh_map_bijective_of_is_K_injective K.obj.obj L.obj.obj).2)

variable [enough_injectives C]

instance (Y : homotopy_category.plus C) :
  nonempty (Φ.right_resolution Y) :=
sorry

instance : ess_surj (Qh : _ ⥤ derived_category.plus C) :=
⟨λ Z, begin
  have R : Φ.right_resolution (derived_category.plus.Qh.obj_preimage Z) :=
    nonempty.some infer_instance,
  refine ⟨R.right.obj, ⟨_ ≪≫ derived_category.plus.Qh.obj_obj_preimage_iso Z⟩⟩,
  haveI := localization.inverts derived_category.plus.Qh _ _ R.hom.hf,
  exact (as_iso (derived_category.plus.Qh.map (R.hom.f))).symm,
end⟩

instance : is_equivalence (Qh : _ ⥤ derived_category.plus C) :=
equivalence.of_fully_faithfully_ess_surj _

instance Qh_is_localization : Qh.is_localization
  (morphism_property.isomorphisms (termwise_injective C)) :=
begin
  haveI : (𝟭 _).is_localization (morphism_property.isomorphisms (termwise_injective C)) :=
    functor.is_localization.for_id _ (by refl),
  refine functor.is_localization.of_equivalence_target (𝟭 _) _ Qh
    (functor.as_equivalence Qh) (functor.left_unitor _),
end

instance Φ_is_localization_equivalence :
  (Φ : localizor_morphism (morphism_property.isomorphisms (termwise_injective C)) _).is_localization_equivalence :=
begin
  rw localizor_morphism.is_localization_equivalence.iff_is_localization Φ
    (derived_category.plus.Qh : plus C ⥤ _),
  change Qh.is_localization _,
  apply_instance,
end

instance (Y : homotopy_category.plus C) (X : Φ.right_resolution Y) :
  is_iso (derived_category.plus.Qh.map X.hom.f) :=
localization.inverts derived_category.plus.Qh _ _ X.hom.hf

lemma lift_map {Y₁ Y₂ : homotopy_category.plus C} (f : Y₁ ⟶ Y₂)
  (X₁ : Φ.right_resolution Y₁) (X₂ : Φ.right_resolution Y₂) :
  ∃ (f' : X₁.right.obj ⟶ X₂.right.obj), X₁.hom.f ≫ Φ.functor.map f' = f ≫ X₂.hom.f := sorry

instance (Y : homotopy_category.plus C) :
  is_preconnected' (Φ.right_resolution Y) :=
⟨⟨begin
  rintro ⟨X₁⟩ ⟨X₂⟩,
  obtain ⟨g, hg⟩ := lift_map (𝟙 Y) X₁ X₂,
  dsimp at hg,
  rw id_comp at hg,
  haveI : is_iso (Qh.map g),
  { replace hg := derived_category.plus.Qh.congr_map hg,
    rw functor.map_comp at hg,
    change is_iso (derived_category.plus.Qh.map (Φ.functor.map g)),
    exact is_iso.of_is_iso_fac_left hg, },
  exact quot.sound ⟨structured_arrow.hom_mk ⟨g, is_iso_of_reflects_iso g termwise_injective.Qh⟩
    (by { ext, exact hg, })⟩,
end⟩⟩

def right_derivability_structure :
  right_derivability_structure.basic (Φ : localizor_morphism (morphism_property.isomorphisms (termwise_injective C)) _) :=
{ right_resolution_connected := λ Y, { },
  nonempty_arrow_right_resolution := λ Y₁ Y₂ f, begin
    let X₁ : Φ.right_resolution Y₁ := nonempty.some infer_instance,
    let X₂ : Φ.right_resolution Y₂ := nonempty.some infer_instance,
    obtain ⟨f', fac⟩ := lift_map f X₁ X₂,
    exact ⟨X₁, X₂, f', fac⟩,
  end, }

instance Φ_functor_comp_Qh_ess_surj_on_dist_triang : (Φ.functor ⋙
  derived_category.plus.Qh : _ ⥤ derived_category.plus C).ess_surj_on_dist_triang :=
begin
  haveI : (derived_category.plus.Qh : _ ⥤ derived_category.plus C).ess_surj_on_dist_triang := sorry,
  exact right_derivability_structure.Φ_functor_comp_L_ess_surj_on_dist_triang _,
end

section

variables {D : Type*} [category D]
  (F : homotopy_category.plus C ⥤ D)

instance existence_right_derived_functor :
  F.has_right_derived_functor (triangulated.subcategory.W (acyclic C)) :=
right_derivability_structure.basic.existence_derived_functor
  termwise_injective.right_derivability_structure F (morphism_property.isomorphisms.is_inverted_by _)

lemma is_iso_app (RF : derived_category.plus C ⥤ D)
  (α : F ⟶ derived_category.plus.Qh ⋙ RF)
  [RF.is_right_derived_functor α]
  (K : homotopy_category.plus C) [K.obj.as.is_termwise_injective] :
  is_iso (α.app K) :=
right_derivability_structure.basic.is_iso_app
  termwise_injective.right_derivability_structure derived_category.plus.Qh F
  (morphism_property.isomorphisms.is_inverted_by _) RF α ⟨K, infer_instance⟩

instance (K : homotopy_category.plus C) [K.obj.as.is_termwise_injective] :
  is_iso ((F.right_derived_functor_α derived_category.plus.Qh
    (triangulated.subcategory.W (acyclic C))).app K) :=
is_iso_app _ _ _ _

section

variables [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ (n : ℤ), (shift_functor D n).additive] [pretriangulated D]
  [F.has_comm_shift ℤ] [functor.is_triangulated F]

instance right_derived_functor_is_triangulated :
  (F.right_derived_functor derived_category.plus.Qh
    (triangulated.subcategory.W (acyclic C))).is_triangulated :=
right_derivability_structure.basic.derived_functor_is_triangulated'
    termwise_injective.right_derivability_structure F derived_category.plus.Qh
    (morphism_property.isomorphisms.is_inverted_by _)

end

end

end termwise_injective

end plus

end homotopy_category
