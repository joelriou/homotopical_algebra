import for_mathlib.category_theory.functor.shift
import category_theory.triangulated.pretriangulated
import for_mathlib.category_theory.triangulated.pretriangulated_misc

open category_theory category_theory.category category_theory.limits

namespace category_theory

namespace functor

variables {C D E : Type*} [category C] [category D] [category E]
  [has_zero_object C] [has_zero_object D] [has_zero_object E]
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

variables [∀ (n : ℤ), (shift_functor C n).additive]
  [∀ (n : ℤ), (shift_functor D n).additive]
  [∀ (n : ℤ), (shift_functor E n).additive]
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

end functor

end category_theory
