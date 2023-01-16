import for_mathlib.category_theory.localization.shift
import for_mathlib.category_theory.triangulated.triangulated_functor

open category_theory category_theory.limits

namespace category_theory

namespace functor

variables {C H D : Type*} [category C] [category H] [category D]
  [has_shift C ℤ] [has_shift H ℤ] [has_shift D ℤ]
  [has_zero_object C] [has_zero_object H] [has_zero_object D]
  [preadditive C] [preadditive H] [preadditive D]
  [∀ (n : ℤ), (shift_functor C n).additive]
  [∀ (n : ℤ), (shift_functor H n).additive]
  [∀ (n : ℤ), (shift_functor D n).additive]
  [pretriangulated C] [pretriangulated H] [pretriangulated D]
  (L : C ⥤ H) [L.has_comm_shift ℤ]

class ess_surj_on_dist_triang :=
(condition [] : ∀ (T : pretriangulated.triangle H) (hT : T ∈ dist_triang H),
  ∃ (T' : pretriangulated.triangle C) (hT' : T' ∈ dist_triang C),
    nonempty (L.map_triangle.obj T' ≅ T))

variables {L}

lemma is_triangulated.of_ess_surj_on_dist_triang [L.ess_surj_on_dist_triang]
  {F : C ⥤ D} {G : H ⥤ D} (e : L ⋙ G ≅ F) [G.has_comm_shift ℤ] [F.has_comm_shift ℤ]
  [F.is_triangulated] [e.hom.respects_comm_shift ℤ] : G.is_triangulated :=
{ map_distinguished' := λ T hT, begin
    obtain ⟨T', hT', ⟨e₁⟩⟩ := ess_surj_on_dist_triang.condition L T hT,
    exact pretriangulated.isomorphic_distinguished _ (F.map_distinguished _ hT') _
      (G.map_triangle.map_iso e₁.symm ≪≫ (map_triangle_comp L G).symm.app T' ≪≫
      (map_triangle_nat_iso e).app T'),
  end }

instance localization_lift_is_triangulated [L.ess_surj_on_dist_triang]
  (W : morphism_property C) [L.is_localization W]
  (F : C ⥤ D) (hF : W.is_inverted_by F) [F.has_comm_shift ℤ] [F.is_triangulated] :
  (localization.lift F hF L).is_triangulated :=
is_triangulated.of_ess_surj_on_dist_triang (localization.fac F hF L)

end functor

end category_theory
