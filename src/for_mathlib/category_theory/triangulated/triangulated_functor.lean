import for_mathlib.category_theory.functor.shift
import category_theory.triangulated.pretriangulated
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.triangulated.yoneda

open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated

noncomputable theory

namespace category_theory

namespace functor

variables {C D E : Type*} [category C] [category D] [category E]
  [has_shift C ℤ] [has_shift D ℤ] [has_shift E ℤ]
  [preadditive C] [preadditive D] [preadditive E]
  (F : C ⥤ D) [F.has_comm_shift ℤ] (G : D ⥤ E) [G.has_comm_shift ℤ]

@[simps]
def map_triangle : pretriangulated.triangle C ⥤ pretriangulated.triangle D :=
{ obj := λ T, pretriangulated.triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.comm_shift_iso (1 : ℤ)).hom.app T.obj₁),
  map := λ S T f,
  { hom₁ := F.map f.hom₁,
    hom₂ := F.map f.hom₂,
    hom₃ := F.map f.hom₃,
    comm₁' := by { dsimp, simp only [← F.map_comp, f.comm₁], },
    comm₂' := by { dsimp, simp only [← F.map_comp, f.comm₂], },
    comm₃' := begin
      dsimp,
      erw [category.assoc, ←nat_trans.naturality],
      simp only [functor.comp_map, ← F.map_comp_assoc, f.comm₃],
    end, }, }

instance [faithful F] : faithful F.map_triangle :=
⟨λ K L f₁ f₂ hf, begin
  ext; apply F.map_injective,
  { change (F.map_triangle.map f₁).hom₁ = (F.map_triangle.map f₂).hom₁, rw hf, },
  { change (F.map_triangle.map f₁).hom₂ = (F.map_triangle.map f₂).hom₂, rw hf, },
  { change (F.map_triangle.map f₁).hom₃ = (F.map_triangle.map f₂).hom₃, rw hf, },
end⟩

instance [full F] [faithful F] : full F.map_triangle :=
full_of_surjective _ (λ K L f, begin
  refine
  ⟨{ hom₁ := F.preimage f.hom₁,
    hom₂ := F.preimage f.hom₂,
    hom₃ := F.preimage f.hom₃,
    comm₁' := F.map_injective (by simpa only [F.map_comp, image_preimage] using f.comm₁),
    comm₂' := F.map_injective (by simpa only [F.map_comp, image_preimage] using f.comm₂),
    comm₃' := F.map_injective (begin
      have eq := f.comm₃,
      dsimp at eq,
      simp only [map_comp, image_preimage, assoc,
        ← cancel_mono ((F.comm_shift_iso (1 : ℤ)).hom.app L.obj₁), ← eq],
      erw (F.comm_shift_iso (1 : ℤ)).hom.naturality (F.preimage f.hom₁),
      simp only [comp_map, image_preimage],
    end), }, by tidy⟩,
end)

@[simps]
def map_triangle_rotate [functor.additive F] :
  F.map_triangle ⋙ pretriangulated.rotate D ≅
    pretriangulated.rotate C ⋙ F.map_triangle :=
nat_iso.of_components (λ T, triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
  ((F.comm_shift_iso (1 : ℤ)).symm.app _) (by tidy) (by tidy) begin
    dsimp,
    simp only [map_id, preadditive.neg_comp, comp_id,
      map_neg, preadditive.comp_neg, neg_inj],
    erw ← nat_trans.naturality_assoc,
    simp only [comp_map, iso.inv_hom_id_app, comp_id],
  end)
  (λ X Y f, begin
    ext,
    { dsimp, simp, },
    { dsimp, simp, },
    { dsimp, erw ← nat_trans.naturality, refl, },
  end)

@[simps]
def map_triangle_inv_rotate [functor.additive F]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [∀ (n : ℤ), (shift_functor D n).additive] :
  F.map_triangle ⋙ pretriangulated.inv_rotate D ≅
    pretriangulated.inv_rotate C ⋙ F.map_triangle :=
calc F.map_triangle ⋙ inv_rotate D ≅ _ : (functor.left_unitor _).symm
... ≅ _ : iso_whisker_right (pretriangulated.triangle_rotation C).counit_iso.symm _
... ≅ _ : functor.associator _ _ _
... ≅ _ : iso_whisker_left _ (functor.associator _ _ _).symm
... ≅ _ : iso_whisker_left _ (iso_whisker_right (map_triangle_rotate F).symm _)
... ≅ _ : iso_whisker_left _ (functor.associator _ _ _)
... ≅ _ : iso_whisker_left _ (iso_whisker_left _ (pretriangulated.triangle_rotation D).unit_iso.symm)
... ≅ _: iso_whisker_left _ (functor.right_unitor _)

variable (C)

@[simps]
def map_triangle_id : (𝟭 C).map_triangle ≅ 𝟭 _ :=
nat_iso.of_components (λ T, pretriangulated.triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _)
  (by tidy) (by tidy) (by tidy)) (by tidy)

variable {C}

@[simps]
def map_triangle_comp : (F ⋙ G).map_triangle ≅ F.map_triangle ⋙ G.map_triangle :=
nat_iso.of_components (λ T, pretriangulated.triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _)
  (by tidy) (by tidy) (by { dsimp, simp, })) (λ T₁ T₂ f, by { ext; dsimp; simp, })

variables {F}

@[simps]
def map_triangle_nat_trans {F' : C ⥤ D} [F'.has_comm_shift ℤ] (τ : F ⟶ F')
  [τ.respects_comm_shift ℤ] :
  F.map_triangle ⟶ F'.map_triangle :=
{ app := λ X,
  { hom₁ := τ.app _,
    hom₂ := τ.app _,
    hom₃ := τ.app _,
    comm₃' := begin
      dsimp,
      simp only [assoc, nat_trans.respects_comm_shift.comm_app τ (1 : ℤ),
        nat_trans.naturality_assoc],
    end, }, }

@[simps]
def map_triangle_nat_iso {F' : C ⥤ D} [F'.has_comm_shift ℤ] (e : F ≅ F')
  [e.hom.respects_comm_shift ℤ] : F.map_triangle ≅ F'.map_triangle :=
nat_iso.of_components
  (λ T, pretriangulated.triangle.mk_iso _ _ (e.app _) (e.app _) (e.app _) (by tidy) (by tidy)
  begin
    dsimp,
    simp only [assoc, nat_trans.respects_comm_shift.comm_app e.hom (1 : ℤ),
      nat_trans.naturality_assoc],
  end) (by tidy)

variables (F) [∀ (n : ℤ), (shift_functor C n).additive]
  [∀ (n : ℤ), (shift_functor D n).additive]
  [∀ (n : ℤ), (shift_functor E n).additive]
  [has_zero_object C] [has_zero_object D] [has_zero_object E]
  [pretriangulated C] [pretriangulated D] [pretriangulated E]

@[protected]
class is_triangulated : Prop :=
(map_distinguished' [] : ∀ (T : pretriangulated.triangle C)
  (hT : T ∈ dist_triang C), F.map_triangle.obj T ∈ dist_triang D)

lemma map_distinguished [F.is_triangulated] (T : pretriangulated.triangle C)
  (hT : T ∈ dist_triang C) : F.map_triangle.obj T ∈ dist_triang D :=
is_triangulated.map_distinguished' F T hT

instance id_is_triangulated : (𝟭 C).is_triangulated :=
{ map_distinguished' :=
    λ T hT, pretriangulated.isomorphic_distinguished _ hT _ ((map_triangle_id C).app T), }

instance comp_is_triangulated [F.is_triangulated] [G.is_triangulated] :
  (F ⋙ G).is_triangulated :=
{ map_distinguished' := λ T hT, pretriangulated.isomorphic_distinguished _
    (G.map_distinguished _ (F.map_distinguished _ hT)) _ ((map_triangle_comp F G).app T), }

lemma reflects_distinguished [F.is_triangulated] [full F] [faithful F]
  (T : pretriangulated.triangle C) (hT : F.map_triangle.obj T ∈ dist_triang D) :
  T ∈ dist_triang C :=
begin
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle _ _ T.mor₁,
  exact pretriangulated.isomorphic_distinguished _ mem _
    (F.map_triangle.preimage_iso (pretriangulated.iso_triangle_of_distinguished_of_is_iso₁₂ _ _ hT
    (F.map_distinguished _ mem) (iso.refl _) (iso.refl _) (by tidy))),
end

variable {F}

lemma is_triangulated.of_iso {G : C ⥤ D} (e : F ≅ G) [F.is_triangulated] [G.has_comm_shift ℤ]
  [e.hom.respects_comm_shift ℤ] : G.is_triangulated :=
⟨λ T hT, pretriangulated.isomorphic_distinguished _
  (F.map_distinguished _ hT) _ ((map_triangle_nat_iso e).symm.app T)⟩

end functor

namespace pretriangulated

variables {C : Type*} [category C] [has_shift C ℤ] [preadditive C]
  (S : set C) [S.is_stable_by_shift ℤ]

variables (T : pretriangulated.triangle C)
  (h₁ : T.obj₁ ∈ S) (h₂ : T.obj₂ ∈ S) (h₃ : T.obj₃ ∈ S)

@[simps]
def full_subcategory_lift_triangle :
  pretriangulated.triangle (full_subcategory S) :=
{ obj₁ := ⟨T.obj₁, h₁⟩,
  obj₂ := ⟨T.obj₂, h₂⟩,
  obj₃ := ⟨T.obj₃, h₃⟩,
  mor₁ := T.mor₁,
  mor₂ := T.mor₂,
  mor₃ := T.mor₃, }

def full_subcategory_lift_triangle_iso :
  (full_subcategory_inclusion S).map_triangle.obj
    (full_subcategory_lift_triangle S T h₁ h₂ h₃) ≅ T :=
triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) begin
  dsimp,
  simp only [functor.map_id, comp_id, id_comp],
  erw comp_id,
end

end pretriangulated

end category_theory
