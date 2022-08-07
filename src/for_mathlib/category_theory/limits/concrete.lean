import category_theory.limits.concrete_category
import category_theory.limits.preserves.limits

noncomputable theory

universes v u w

open category_theory

namespace category_theory

namespace limits

section
variables {J : Type w} (G : discrete J ⥤ Type (max w v))

@[simps]
def concrete.coproduct_cocone : cocone G :=
{ X := Σ (j : J), G.obj ⟨j⟩,
  ι := discrete.nat_trans begin
    rintros ⟨j⟩ x,
    exact ⟨j, x⟩,
  end, }

@[simps]
def concrete.coproduct_cocone_is_colimit :
  is_colimit (concrete.coproduct_cocone G) :=
{ desc := λ s x, s.ι.app ⟨x.1⟩ x.2,
  fac' := λ s, by { rintro ⟨j⟩, refl, },
  uniq' := λ s m hm, begin
    ext1 x,
    rcases x with ⟨j, y⟩,
    exact congr_fun (hm ⟨j⟩) y,
  end, }

@[simps]
lemma concrete.coproduct_iso : (concrete.coproduct_cocone G).X ≅ colimit G :=
is_colimit.cocone_point_unique_up_to_iso (concrete.coproduct_cocone_is_colimit G)
    (colimit.is_colimit _)

end

variables {C : Type u} [category.{v} C] [concrete_category.{(max w v)} C]
  {J : Type w} (F : J → C) [has_coproduct F]

@[simp]
def concrete.coproduct_map :
  (Σ (j : J), (forget C).obj (F j)) → (forget C).obj (sigma_obj F) :=
λ a, (forget C).map (sigma.ι F a.1) a.2

@[reassoc]
lemma concrete.coproduct_cocone_compat (j : discrete J) :
  (concrete.coproduct_cocone (discrete.functor F ⋙ forget C)).ι.app j ≫
    (concrete.coproduct_iso (discrete.functor F ⋙ forget C)).hom =
    colimit.ι (discrete.functor F ⋙ forget C) j :=
begin
  sorry,
end

lemma concrete.coproduct_map_bijective [hF : preserves_colimit (discrete.functor F) (forget C)] :
  function.bijective (concrete.coproduct_map F) :=
begin
  rw ← is_iso_iff_bijective,
  convert is_iso.of_iso (concrete.coproduct_iso (discrete.functor F ⋙ forget C) ≪≫
    (preserves_colimit_iso (forget C) (discrete.functor F)).symm),
  apply (concrete.coproduct_cocone_is_colimit (discrete.functor F ⋙ forget C)).hom_ext,
  intro j,
  dsimp only [iso.trans],
  rw [concrete.coproduct_cocone_compat_assoc],
  rw ← cancel_mono ((preserves_colimit_iso (forget C) (discrete.functor F)).symm.inv),
  simp only [category.assoc, iso.hom_inv_id, category.comp_id],
--  rintro ⟨j⟩,
--  dsimp only [iso.trans],
--  simp only [concrete.coproduct_map, concrete.coproduct_cocone_ι, id.def, discrete.nat_trans_app, forget_map_eq_coe, iso.symm_hom],
  sorry,
end

end limits

end category_theory
