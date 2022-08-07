import category_theory.limits.concrete_category
import category_theory.limits.preserves.limits

noncomputable theory

universes v u w

open category_theory

namespace category_theory

namespace limits

section

variables {J : Type w} (G : J → Type (max w v))

@[simps]
def concrete.coproduct_cocone : cocone (discrete.functor G) :=
{ X := Σ (j : J), G j,
  ι := discrete.nat_trans (λ j x, ⟨j.as, x⟩), }

lemma concrete.coproduct_cocone_is_colimit : is_colimit (concrete.coproduct_cocone G) :=
{ desc := λ s x, s.ι.app ⟨x.1⟩ x.2,
  fac' := λ s, by { rintro ⟨j⟩, refl, },
  uniq' := λ s m hm, begin
    ext1 x,
    rcases x with ⟨j, y⟩,
    exact congr_fun (hm ⟨j⟩) y,
  end, }

lemma concrete.coproduct_iso : (concrete.coproduct_cocone G).X ≅ colimit (discrete.functor G) :=
is_colimit.cocone_point_unique_up_to_iso (concrete.coproduct_cocone_is_colimit G)
    (colimit.is_colimit _)

end

variables {C : Type u} [category.{v} C] [concrete_category.{(max w v)} C]
  {J : Type w} (F : J → C) [has_coproduct F]

@[simp]
def concrete.coproduct_map :
  (Σ (j : J), (forget C).obj (F j)) → (forget C).obj (sigma_obj F) :=
λ a, (forget C).map (sigma.ι F a.1) a.2

lemma concrete.coproduct_map_bijective [hF : preserves_colimit (discrete.functor F) (forget C)] :
  function.bijective (concrete.coproduct_map F) :=
begin
  rw ← is_iso_iff_bijective,
  let e₁ := concrete.coproduct_iso ((forget C).obj ∘ F),
  let e₃ := (preserves_colimit_iso (forget C) (discrete.functor F)).symm,
  let E := e₁ ≪≫ has_colimit.iso_of_equivalence (by refl)
    (by exact discrete.nat_iso (λ i, iso.refl _)) ≪≫ e₃,
  convert is_iso.of_iso E,
  ext x,
  rcases x with ⟨j, y⟩,
  sorry,
end

end limits

end category_theory
