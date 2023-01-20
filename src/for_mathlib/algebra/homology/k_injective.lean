import for_mathlib.algebra.homology.k_projective
import for_mathlib.category_theory.localization.derived_functor_triangulated
import category_theory.abelian.injective

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated
open_locale zero_object

instance inverse_image_multiplicative {C D : Type*} [category C] [category D]
  (F : C ⥤ D) (W : morphism_property D)
  [W.multiplicative] : (W.inverse_image F).multiplicative :=
{ contains_identities := ⟨λ X, begin
    change W _,
    rw F.map_id,
    apply morphism_property.contains_identities.id W,
  end⟩,
  comp := (morphism_property.multiplicative.comp W).inverse_image F, }

variables {C : Type*} [category C] [abelian C]

namespace homological_complex

variables {ι : Type*} {c : complex_shape ι} (K L : homological_complex C c)

class is_K_injective : Prop :=
(null_homotopic : ∀ ⦃X : homological_complex C c⦄ (f : X ⟶ K)
  (hX : acyclic X), nonempty (homotopy f 0))

variables {K L}

lemma is_K_injective.of_homotopy_equiv [K.is_K_injective] (e : homotopy_equiv K L) :
  L.is_K_injective :=
⟨λ X f hX, begin
  obtain ⟨h⟩ := is_K_injective.null_homotopic (f ≫ e.inv) hX,
  refine ⟨(homotopy.of_eq (comp_id f)).symm.trans
    (((e.homotopy_inv_hom_id.symm.comp_left f).trans
      (homotopy.of_eq (assoc _ _ _).symm)).trans
        ((h.comp_right e.hom).trans (homotopy.of_eq zero_comp)))⟩,
end⟩

lemma is_K_injective.of_iso [K.is_K_injective] (e : K ≅ L) : L.is_K_injective :=
is_K_injective.of_homotopy_equiv (homotopy_equiv.of_iso e)

lemma is_K_injective.iff_of_iso (e : K ≅ L) :
  K.is_K_injective ↔ L.is_K_injective :=
begin
  split,
  { introI, exact is_K_injective.of_iso e, },
  { introI, exact is_K_injective.of_iso e.symm, },
end

lemma is_K_injective.of_is_zero (h : is_zero K) : K.is_K_injective :=
⟨λ X f hX, begin
  rw h.eq_of_tgt f 0,
  exact ⟨homotopy.refl _⟩
end⟩

instance zero_is_K_injective : is_K_injective (0 : homological_complex C c) :=
is_K_injective.of_is_zero (limits.is_zero_zero _)

end homological_complex

namespace cochain_complex

open homological_complex

variables (K : cochain_complex C ℤ)

lemma is_K_injective_iff : is_K_injective K ↔
  (homotopy_category.quotient _ _).obj K
    ∈ triangulated.right_orthogonal (homotopy_category.acyclic C) :=
begin
  split,
  { introI,
    rintros ⟨X⟩ f hX,
    obtain ⟨f, rfl⟩ := (homotopy_category.quotient _ _).map_surjective f,
    rw ← (homotopy_category.quotient C (complex_shape.up ℤ)).map_zero,
    refine homotopy_category.eq_of_homotopy _ _ (is_K_injective.null_homotopic _ _).some,
    erw homotopy_category.quotient_obj_mem_acyclic_iff at hX,
    exact hX, },
  { intro hK,
    refine ⟨λ X f hX, ⟨homotopy_category.homotopy_of_eq _ _ _⟩⟩,
    simp only [functor.map_zero],
    apply hK,
    simpa only [homotopy_category.quotient_obj_mem_acyclic_iff] using hX, },
end

lemma shift_is_K_injective_iff (K : cochain_complex C ℤ) (r : ℤ) :
  is_K_injective (K⟦r⟧) ↔ is_K_injective K :=
begin
  simp only [is_K_injective_iff],
  erw [set.respects_iso.mem_iff_of_iso (triangulated.right_orthogonal (homotopy_category.acyclic C))
   (((homotopy_category.quotient C (complex_shape.up ℤ)).comm_shift_iso r).app K),
   ← triangulated.is_triangulated_subcategory.shift_iff],
end

lemma is_K_injective_of_bounded_below_of_injective
  (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_ge n]
  [∀ (n : ℤ), injective (K.X n)] : is_K_injective K := sorry

end cochain_complex

namespace homotopy_category

variables {C} {ι : Type*} {c : complex_shape ι}

class is_K_injective (K : homotopy_category C c) : Prop :=
(K_injective : K.as.is_K_injective)

lemma is_K_injective_iff' (K : homotopy_category C c) :
  K.is_K_injective ↔ K.as.is_K_injective :=
begin
  split,
  { exact λ h, h.K_injective, },
  { exact λ h, ⟨h⟩, },
end

lemma is_K_injective_iff (K : homotopy_category C (complex_shape.up ℤ)) : is_K_injective K ↔
  K ∈ triangulated.right_orthogonal (homotopy_category.acyclic C) :=
begin
  rw K.is_K_injective_iff',
  cases K,
  dsimp,
  apply cochain_complex.is_K_injective_iff,
end

variables (C c)


abbreviation K_injective := full_subcategory (λ (K : homotopy_category C c), K.is_K_injective)

instance is_K_injective_is_triangulated_subcategory :
  triangulated.is_triangulated_subcategory (λ (K : homotopy_category C (complex_shape.up ℤ)), K.is_K_injective) := sorry

instance K_injective_is_K_injective (K : K_injective C c) : K.obj.is_K_injective := K.2

--instance : pretriangulated (K_injective C (complex_shape.up ℤ)) := infer_instance

abbreviation K_injective.ι : K_injective C c ⥤ homotopy_category C c :=
full_subcategory_inclusion _

end homotopy_category

namespace derived_category

lemma Qh_map_bijective_of_is_K_injective
  (K L : homotopy_category C (complex_shape.up ℤ)) [L.is_K_injective] :
  function.bijective (λ (f : K ⟶ L), Qh.map f) :=
(triangulated.subcategory.right_orthogonal_bijective_Q_map
  (homotopy_category.acyclic C) _ _
  (by { rw ← L.is_K_injective_iff, apply_instance, }))

lemma Qh_map_bijective_of_is_K_injective'
  (K L : cochain_complex C ℤ) [L.is_K_injective] :
  function.bijective (λ (f : ((homotopy_category.quotient _ _).obj K ⟶
    (homotopy_category.quotient _ _).obj L)), Qh.map f) :=
(triangulated.subcategory.right_orthogonal_bijective_Q_map
  (homotopy_category.acyclic C) _ _
  ((cochain_complex.is_K_injective_iff L).1 infer_instance))

lemma Q_map_surjective_of_is_K_injective
  (K L : cochain_complex C ℤ) [L.is_K_injective] :
  function.surjective (λ (f : K ⟶ L), Q.map f) :=
λ f, begin
  obtain ⟨g, hg⟩ := (Qh_map_bijective_of_is_K_injective' K L).2 f,
  dsimp at hg,
  obtain ⟨g, rfl⟩ := (homotopy_category.quotient _ _).map_surjective g,
  exact ⟨g, hg⟩,
end

def homotopy_of_eq_Qh_map_eq_of_is_K_injective
  {K L : cochain_complex C ℤ} [L.is_K_injective] (f₁ f₂ : K ⟶ L)
  (h : Q.map f₁ = Q.map f₂) : homotopy f₁ f₂ :=
homotopy_category.homotopy_of_eq _ _ ((Qh_map_bijective_of_is_K_injective' K L).1 h)

end derived_category

namespace homotopy_category

variable (C)

namespace K_injective

def W : morphism_property (homotopy_category.K_injective C (complex_shape.up ℤ)) :=
(triangulated.subcategory.W (homotopy_category.acyclic C)).inverse_image (K_injective.ι _ _)

instance W_multiplicative : (W C).multiplicative :=
by { dsimp [W], apply_instance, }

variable {C}

def Φ : localizor_morphism (W C) (triangulated.subcategory.W (homotopy_category.acyclic C)) :=
{ functor := K_injective.ι _ _,
  mapW := λ X Y f hf, hf, }

instance Φ_functor_has_comm_shift :
  (Φ : localizor_morphism (W C) _).functor.has_comm_shift ℤ :=
by { dsimp only [Φ], apply_instance, }

instance Φ_functor_is_triangulated :
  (Φ : localizor_morphism (W C) _).functor.is_triangulated :=
by { dsimp only [Φ], apply_instance, }

end K_injective

end homotopy_category

namespace category_theory

variable (C)

include C

class has_enough_K_injectives : Prop :=
(condition : ∀ (K : homotopy_category C (complex_shape.up ℤ)),
  nonempty (homotopy_category.K_injective.Φ.right_resolution K))

end category_theory

open category_theory

namespace homotopy_category

namespace K_injective

variable {C}

def Qh : K_injective C (complex_shape.up ℤ) ⥤ derived_category C :=
K_injective.ι _ _ ⋙ derived_category.Qh

instance full_Qh : full (Qh : _ ⥤ derived_category C) :=
functor.full_of_surjective _ (λ K L, (derived_category.Qh_map_bijective_of_is_K_injective _ _).2)

instance faithful_Qh : faithful (Qh : _ ⥤ derived_category C) :=
⟨λ K L, (derived_category.Qh_map_bijective_of_is_K_injective _ _).1⟩

variable (C)

lemma W_eq_isomorphisms : W C = morphism_property.isomorphisms _ :=
begin
  ext K L f,
  split,
  { intro hf,
    haveI : is_iso (Qh.map f) := (triangulated.subcategory.is_iso_map_iff
      (acyclic C) derived_category.Qh f).2 hf,
    exact is_iso_of_reflects_iso f Qh, },
  { rintro (h : is_iso _),
    haveI := h,
    exact (triangulated.subcategory.is_iso_map_iff (acyclic C) derived_category.Qh ((ι _ _).map f)).1
      infer_instance, },
end

variable {C}

lemma W_inverts {D : Type*} [category D]
  (G : K_injective C (complex_shape.up ℤ) ⥤ D) :
  (W C).is_inverted_by G :=
begin
  intros X Y f hf,
  haveI : is_iso f := by simpa only [W_eq_isomorphisms] using hf,
  apply_instance,
end

variables [has_enough_K_injectives C]

instance (Y : homotopy_category C (complex_shape.up ℤ)) :
  nonempty (Φ.right_resolution Y) :=
has_enough_K_injectives.condition Y

instance (Y : homotopy_category C (complex_shape.up ℤ)) (X : Φ.right_resolution Y) :
  is_iso (derived_category.Qh.map X.hom.f) :=
by simpa only [triangulated.subcategory.is_iso_map_iff (homotopy_category.acyclic C)
  derived_category.Qh] using X.hom.hf

instance ess_surj_Qh : ess_surj (Qh : _ ⥤ derived_category C) :=
⟨λ Z, begin
  have e := derived_category.Qh.obj_obj_preimage_iso Z,
  let Y := derived_category.Qh.obj_preimage Z,
  let X := (has_enough_K_injectives.condition Y).some,
  exact ⟨X.right.obj, ⟨(as_iso (derived_category.Qh.map X.hom.f)).symm ≪≫
    derived_category.Qh.obj_obj_preimage_iso Z⟩⟩,
end⟩

instance : is_equivalence (Qh : _ ⥤ derived_category C) :=
equivalence.of_fully_faithfully_ess_surj _

instance Qh_is_localization : Qh.is_localization (W C) :=
begin
  haveI : (𝟭 _).is_localization (W C),
  { refine functor.is_localization.for_id _ _,
    rw W_eq_isomorphisms, },
  exact functor.is_localization.of_equivalence_target (𝟭 _) (W C) Qh
    (functor.as_equivalence Qh) (functor.left_unitor _),
end

instance Φ_induced_functor_obj_is_K_injective (Y : homotopy_category C (complex_shape.up ℤ))
  (X : Φ.right_resolution Y) : (Φ.induced_functor.obj X.right).obj.is_K_injective :=
X.right.obj.2

instance Φ_induced_functor_obj_is_K_injective' (Y : homotopy_category C (complex_shape.up ℤ))
  (X : Φ.right_resolution Y) : (Φ.functor.obj X.right.obj).is_K_injective :=
X.right.obj.2

lemma lift_map {Y₁ Y₂ : homotopy_category C (complex_shape.up ℤ)} (f : Y₁ ⟶ Y₂)
  (X₁ : Φ.right_resolution Y₁) (X₂ : Φ.right_resolution Y₂) :
  ∃ (f' : X₁.right.obj ⟶ X₂.right.obj), X₁.hom.f ≫ Φ.functor.map f' = f ≫ X₂.hom.f :=
begin
  let f'' := inv (derived_category.Qh.map (X₁.hom.f)) ≫
    derived_category.Qh.map (f ≫ X₂.hom.f),
  obtain ⟨f', hf'⟩ := (derived_category.Qh_map_bijective_of_is_K_injective _ _).2 f'',
  refine ⟨f', (derived_category.Qh_map_bijective_of_is_K_injective _ _).1 _⟩,
  dsimp [Φ] at hf' ⊢,
  simp only [functor.map_comp, hf', f'', is_iso.hom_inv_id_assoc],
end

instance (Y : homotopy_category C (complex_shape.up ℤ)) :
  is_preconnected' (Φ.right_resolution Y) :=
⟨⟨begin
  rintro ⟨X₁⟩ ⟨X₂⟩,
  obtain ⟨g, hg⟩ := K_injective.lift_map (𝟙 Y) X₁ X₂,
  dsimp at hg,
  rw id_comp at hg,
  refine quot.sound ⟨structured_arrow.hom_mk ⟨g, _⟩ _⟩,
  { change (triangulated.subcategory.W (homotopy_category.acyclic C)) _,
    rw ← triangulated.subcategory.is_iso_map_iff (homotopy_category.acyclic C)
      derived_category.Qh,
    replace hg := derived_category.Qh.congr_map hg,
    rw functor.map_comp at hg,
    exact is_iso.of_is_iso_fac_left hg, },
  { ext, exact hg, },
end⟩⟩

instance Φ_is_localization_equivalence : (Φ : localizor_morphism (W C) _).is_localization_equivalence :=
begin
  rw localizor_morphism.is_localization_equivalence.iff_is_localization Φ
    (derived_category.Qh : _ ⥤ derived_category C),
  change Qh.is_localization _,
  apply_instance,
end

lemma right_derivability_structure :
  right_derivability_structure.basic (Φ : localizor_morphism (W C) _) :=
{ right_resolution_connected := λ Y, { },
  nonempty_arrow_right_resolution := λ Y₁ Y₂ f, begin
    let X₁ := (has_enough_K_injectives.condition Y₁).some,
    let X₂ := (has_enough_K_injectives.condition Y₂).some,
    obtain ⟨f', fac⟩ := K_injective.lift_map f X₁ X₂,
    exact ⟨X₁, X₂, f', fac⟩,
  end, }

instance Φ_functor_comp_Qh_ess_surj_on_dist_triang : (Φ.functor ⋙
  derived_category.Qh : _ ⥤ derived_category C).ess_surj_on_dist_triang :=
K_injective.right_derivability_structure.Φ_functor_comp_L_ess_surj_on_dist_triang _

section

variables {D : Type*} [category D]
  (F : homotopy_category C (complex_shape.up ℤ) ⥤ D)

instance existence_right_derived_functor :
  F.has_right_derived_functor (triangulated.subcategory.W (acyclic C)) :=
right_derivability_structure.basic.existence_derived_functor
  K_injective.right_derivability_structure F (W_inverts _)

lemma is_iso_app (RF : derived_category C ⥤ D)
  (α : F ⟶ derived_category.Qh ⋙ RF)
  [RF.is_right_derived_functor α]
  (K : homotopy_category C (complex_shape.up ℤ)) [K.is_K_injective] :
  is_iso (α.app K) :=
right_derivability_structure.basic.is_iso_app
  K_injective.right_derivability_structure derived_category.Qh F (W_inverts _)
  RF α ⟨K, infer_instance⟩

instance (K : homotopy_category C (complex_shape.up ℤ)) [K.is_K_injective] :
  is_iso ((F.right_derived_functor_α derived_category.Qh
    (triangulated.subcategory.W (acyclic C))).app K) :=
is_iso_app _ _ _ _

section

variables [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ (n : ℤ), (shift_functor D n).additive] [pretriangulated D]
  [F.has_comm_shift ℤ] [functor.is_triangulated F]

instance right_derived_functor_is_triangulated :
  (F.right_derived_functor derived_category.Qh
    (triangulated.subcategory.W (acyclic C))).is_triangulated :=
right_derivability_structure.basic.derived_functor_is_triangulated'
    K_injective.right_derivability_structure F derived_category.Qh (W_inverts _)

end

end

end K_injective

end homotopy_category
