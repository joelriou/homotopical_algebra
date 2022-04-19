
import category_theory.limits.opposites
import tactic.equiv_rw

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

def span_op {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
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

def op_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).op = walking_cospan_op_equiv.functor ⋙ span f.op g.op :=
begin
  nth_rewrite 0 ← functor.id_comp (cospan f g).op,
  rw [span_op, ← functor.assoc],
  congr,
  symmetry,
  apply wide_pullback_shape_op_unop,
end

def cospan_op {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  cospan f.op g.op = walking_span_op_equiv.inverse ⋙ (span f g).op :=
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

def op_span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).op = walking_span_op_equiv.functor ⋙ cospan f.op g.op :=
begin
  nth_rewrite 0 ← functor.id_comp (span f g).op,
  rw [cospan_op, ← functor.assoc],
  congr,
  symmetry,
  apply wide_pushout_shape_op_unop,
end

namespace pushout_cocone

def unop {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pushout_cocone f.op g.op) :
  pullback_cone f g :=
begin
  apply cocone.unop,
  apply (cocones.precompose (eq_to_iso (op_cospan f g)).hom).obj,
  exact cocone.whisker walking_cospan_op_equiv.functor c,
end

def unop_is_colimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pushout_cocone f.op g.op)
  (h : is_colimit c) : is_limit c.unop :=
begin
  apply is_limit_cocone_unop,
  equiv_rw is_colimit.precompose_hom_equiv _ _,
  equiv_rw (is_colimit.whisker_equivalence_equiv _).symm,
  exact h,
end

def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.op g.op :=
begin
  apply (cones.postcompose (eq_to_iso (cospan_op f g).symm).hom).obj,
  exact cone.whisker walking_span_op_equiv.inverse (cocone.op c),
end

def op_is_colimit {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g)
  (h : is_colimit c) : is_limit c.op :=
begin
  equiv_rw is_limit.postcompose_hom_equiv _ _,
  equiv_rw (is_limit.whisker_equivalence_equiv walking_span_op_equiv.symm).symm,
  exact is_limit_cocone_op _ h,
end

end pushout_cocone

namespace pullback_cone

def unop {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pullback_cone f.op g.op) :
  pushout_cocone f g :=
begin
  apply cone.unop,
  apply (cones.postcompose (eq_to_iso (op_span f g)).symm.hom).obj,
  exact cone.whisker walking_span_op_equiv.functor c,
end

def unop_is_limit {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pullback_cone f.op g.op)
  (h : is_limit c) : is_colimit c.unop :=
begin
  apply is_colimit_cone_unop,
  equiv_rw is_limit.postcompose_hom_equiv _ _,
  equiv_rw (is_limit.whisker_equivalence_equiv _).symm,
  exact h,
end

def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.op g.op :=
begin
  apply (cocones.precompose (eq_to_iso (span_op f g)).hom).obj,
  exact cocone.whisker walking_cospan_op_equiv.inverse (cone.op c),
end

def op_is_limit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g)
  (h : is_limit c) : is_colimit c.op :=
begin
  equiv_rw is_colimit.precompose_hom_equiv _ _,
  equiv_rw (is_colimit.whisker_equivalence_equiv walking_cospan_op_equiv.symm).symm,
  exact is_colimit_cone_op _ h,
end

end pullback_cone

lemma unop_has_pushout {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [h : has_pushout f.op g.op] : has_pullback f g :=
begin
  refine ⟨nonempty.intro ⟨_,
    pushout_cocone.unop_is_colimit (colimit.cocone (span f.op g.op)) _⟩⟩,
  apply colimit.is_colimit,
end

lemma op_has_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  [h : has_pushout f g] : has_pullback f.op g.op :=
begin
  refine ⟨nonempty.intro ⟨_,
    pushout_cocone.op_is_colimit (colimit.cocone (span f g)) _⟩⟩,
  apply colimit.is_colimit,
end

lemma unop_has_pullback {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  [h : has_pullback f.op g.op] : has_pushout f g :=
begin
  refine ⟨nonempty.intro ⟨_,
    pullback_cone.unop_is_limit (limit.cone (cospan f.op g.op)) _⟩⟩,
  apply limit.is_limit,
end

lemma op_has_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [h : has_pullback f g] : has_pushout f.op g.op :=
begin
  refine ⟨nonempty.intro ⟨_,
    pullback_cone.op_is_limit (limit.cone (cospan f g)) _⟩⟩,
  apply limit.is_limit,
end

lemma has_pullbacks_opposite [has_pushouts C] : has_pullbacks Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape walking_cospan.{v}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_cospan_op_equiv.symm,
  apply has_limits_of_shape_op_of_has_colimits_of_shape,
end

lemma has_pushouts_opposite [has_pullbacks C] : has_pushouts Cᵒᵖ :=
begin
  haveI : has_limits_of_shape walking_span.{v}ᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_span_op_equiv.symm,
  apply has_colimits_of_shape_op_of_has_limits_of_shape,
end

end limits

end category_theory