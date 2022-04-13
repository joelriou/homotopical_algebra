
import category_theory.limits.opposites

universes v u

open category_theory category_theory.limits opposite

namespace category_theory

lemma functor.assoc {C D E F : Type*} [category C] [category D]
  [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl

namespace limits

variables (J : Type v)

@[simps]
def wide_pullback_shape_op : wide_pullback_shape J ⥤ (wide_pushout_shape J)ᵒᵖ :=
{ obj := λ X, op X,
  map := λ X Y f, begin
    apply quiver.hom.op,
    cases f,
    { apply wide_pushout_shape.hom.id, },
    { apply wide_pushout_shape.hom.init, },
  end, }

@[simps]
def wide_pushout_shape_op : wide_pushout_shape J ⥤ (wide_pullback_shape J)ᵒᵖ :=
{ obj := λ X, op X,
  map := λ X Y f, begin
    apply quiver.hom.op,
    cases f,
    { apply wide_pullback_shape.hom.id, },
    { apply wide_pullback_shape.hom.term, },
  end, }

@[simps]
def wide_pullback_shape_unop : (wide_pullback_shape J)ᵒᵖ ⥤ wide_pushout_shape J :=
(wide_pullback_shape_op J).left_op

@[simps]
def wide_pushout_shape_unop : (wide_pushout_shape J)ᵒᵖ ⥤ wide_pullback_shape J :=
(wide_pushout_shape_op J).left_op

lemma wide_pushout_shape_op_unop : wide_pushout_shape_unop J ⋙ wide_pullback_shape_op J = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f, simp only [eq_iff_true_of_subsingleton], },
  { intro X, refl, }
end

lemma wide_pushout_shape_unop_op : wide_pushout_shape_op J ⋙ wide_pullback_shape_unop J = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f, simp only [eq_iff_true_of_subsingleton], },
  { intro X, refl, }
end

lemma wide_pullback_shape_op_unop : wide_pullback_shape_unop J ⋙ wide_pushout_shape_op J = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f, simp only [eq_iff_true_of_subsingleton], },
  { intro X, refl, }
end

lemma wide_pullback_shape_unop_op : wide_pullback_shape_op J ⋙ wide_pushout_shape_unop J = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f, simp only [eq_iff_true_of_subsingleton], },
  { intro X, refl, }
end

@[simps]
def wide_pushout_shape_op_equiv : (wide_pushout_shape J)ᵒᵖ ≌ wide_pullback_shape J :=
{ functor := wide_pushout_shape_unop J,
  inverse := wide_pullback_shape_op J,
  unit_iso := eq_to_iso (wide_pushout_shape_op_unop J).symm,
  counit_iso := eq_to_iso (wide_pullback_shape_unop_op J), }

def wide_pullback_shape_op_equiv : (wide_pullback_shape J)ᵒᵖ ≌ wide_pushout_shape J :=
{ functor := wide_pullback_shape_unop J,
  inverse := wide_pushout_shape_op J,
  unit_iso := eq_to_iso (wide_pullback_shape_op_unop J).symm,
  counit_iso := eq_to_iso (wide_pushout_shape_unop_op J), }

def walking_span_op_equiv : walking_spanᵒᵖ ≌ walking_cospan :=
wide_pushout_shape_op_equiv _
def walking_cospan_op_equiv : walking_cospanᵒᵖ ≌ walking_span :=
wide_pullback_shape_op_equiv _

variables {C : Type u} [category.{v} C]

namespace pushout_cocone

def span_op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} :
  span f.op g.op = walking_cospan_op_equiv.inverse ⋙ (cospan f g).op :=
begin
  apply functor.ext,
  { intros i j g,
    rcases g with (_|_|_),
    { erw [functor.map_id, functor.map_id],
      simp only [category.id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { erw [category.id_comp, category.comp_id], refl, },
    { erw [category.id_comp, category.comp_id], refl, }, },
  { intro i,
    rcases i with (_|_|_); refl, }
end

def op_cospan {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} :
  (cospan f g).op = walking_cospan_op_equiv.functor ⋙ span f.op g.op :=
begin
  nth_rewrite 0 ← functor.id_comp (cospan f g).op,
  rw [span_op, ← functor.assoc],
  congr,
  symmetry,
  apply wide_pullback_shape_op_unop,
end

def unop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pushout_cocone f.op g.op) :
  pullback_cone f g :=
begin
  apply cocone.unop,
  convert cocone.whisker walking_cospan_op_equiv.functor c,
  apply op_cospan,
end

def unop_is_colimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pushout_cocone f.op g.op)
  (h : is_colimit c) : is_limit c.unop :=
begin
  apply is_limit.of_whisker_equivalence walking_span_op_equiv,
  convert is_limit_cone_left_op_of_cocone _ h,
  sorry,
  sorry,
end

end pushout_cocone

lemma unop_has_pushout {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
  [h : has_pushout f.op g.op] : has_pullback f g :=
begin
  refine ⟨nonempty.intro ⟨_,
    pushout_cocone.unop_is_colimit (colimit.cocone (span f.op g.op)) _⟩⟩,
  apply colimit.is_colimit,
end



end limits

end category_theory