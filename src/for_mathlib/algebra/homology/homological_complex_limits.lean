import algebra.homology.homological_complex
import category_theory.limits.shapes.finite_products
import category_theory.limits.preserves.finite

noncomputable theory

open category_theory category_theory.limits
  category_theory.category

namespace homological_complex

namespace limits

variables {C ι J : Type*} [category C] [category J] [has_zero_morphisms C]
  {c : complex_shape ι}

section

variables (F : J ⥤ homological_complex C c)
  [∀ (n : ι), has_limit (F ⋙ homological_complex.eval C c n)]

@[simps]
def cone : cone F :=
{ X :=
  { X := λ n, limit (F ⋙ homological_complex.eval C c n),
    d := λ n m, lim_map { app := λ j, (F.obj j).d n m, },
    shape' := λ n m h, begin
      ext j,
      simp only [lim_map_π, zero_comp, (F.obj j).shape _ _ h, comp_zero],
    end, },
  π :=
  { app := λ j,
    { f := λ n, limit.π _ j, },
    naturality' := λ i j φ, begin
      ext n,
      dsimp,
      erw [limit.w, id_comp],
    end, }, }

lemma is_limit_cone : is_limit (cone F) :=
{ lift := λ s,
  { f := λ n, limit.lift _ ((eval C c n).map_cone s), },
  uniq' := λ s m hm, begin
    ext n j,
    simp only [limit.lift_π, functor.map_cone_π_app, eval_map,
      ← hm, comp_f, cone_π_app_f],
  end, }

instance : has_limit F := ⟨⟨⟨ _, is_limit_cone F⟩⟩⟩

end

instance [has_limits_of_shape J C] :
  has_limits_of_shape J (homological_complex C c) :=
⟨λ F, infer_instance⟩

instance [has_limits_of_shape J C] (n : ι) :
  preserves_limits_of_shape J (homological_complex.eval C c n) :=
⟨λ F, preserves_limit_of_preserves_limit_cone (is_limit_cone F)
  (is_limit.of_iso_limit (limit.is_limit _)
    (cones.ext (iso.refl _) (by tidy)))⟩

instance [has_finite_limits C] :
  has_finite_limits (homological_complex C c) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_limits C] (n : ι) :
  preserves_finite_limits (homological_complex.eval C c n) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_products C] :
  has_finite_products (homological_complex C c) :=
⟨λ n, infer_instance⟩

end limits

end homological_complex
