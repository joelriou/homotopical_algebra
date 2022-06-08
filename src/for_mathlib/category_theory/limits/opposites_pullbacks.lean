
import category_theory.limits.opposites
import tactic.equiv_rw

universes v u

open category_theory category_theory.limits opposite

namespace category_theory

namespace limits

variables {C : Type u} [category.{v} C]

def span_op {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  span f.op g.op ≅ walking_cospan_op_equiv.inverse ⋙ (cospan f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, }) (by { rintros i j (_|_|_); tidy, })

def op_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).op ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op :=
begin
  calc (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op : by refl
  ... ≅ (walking_cospan_op_equiv.functor ⋙ walking_cospan_op_equiv.inverse) ⋙ (cospan f g).op : iso_whisker_right walking_cospan_op_equiv.unit_iso _
  ... ≅ walking_cospan_op_equiv.functor ⋙ (walking_cospan_op_equiv.inverse ⋙ (cospan f g).op) : functor.associator _ _ _
  ... ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op : iso_whisker_left _ (span_op f g).symm,
end

def cospan_op {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  cospan f.op g.op ≅ walking_span_op_equiv.inverse ⋙ (span f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, }) (by { rintros i j (_|_|_); tidy, })

def op_span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).op ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op :=
begin
  calc (span f g).op ≅ 𝟭 _ ⋙ (span f g).op : by refl
  ... ≅ (walking_span_op_equiv.functor ⋙ walking_span_op_equiv.inverse) ⋙ (span f g).op :
    iso_whisker_right walking_span_op_equiv.unit_iso _
  ... ≅ walking_span_op_equiv.functor ⋙ (walking_span_op_equiv.inverse ⋙ (span f g).op) : functor.associator _ _ _
  ... ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op : iso_whisker_left _ (cospan_op f g).symm,
end

namespace pushout_cocone

def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.unop g.unop :=
begin
  apply cocone.unop,
  refine (cocones.precompose (op_cospan f.unop g.unop).hom).obj _,
  exact cocone.whisker walking_cospan_op_equiv.functor c,  
end

def unop_is_colimit {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g)
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
  apply (cones.postcompose (cospan_op f g).symm.hom).obj,
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

def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.unop g.unop :=
begin
  apply cone.unop, 
  apply (cones.postcompose (op_span f.unop g.unop).symm.hom).obj,
  exact cone.whisker walking_span_op_equiv.functor c,  
end

def unop_is_limit {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g)
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
  apply (cocones.precompose (span_op f g).hom).obj,
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

lemma unop_has_pushout {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : X ⟶ Z)
  [h : has_pushout f g] : has_pullback f.unop g.unop :=
begin
  haveI : has_pushout f.unop.op g.unop.op := h,
  refine ⟨nonempty.intro ⟨_,
    pushout_cocone.unop_is_colimit (colimit.cocone (span f g)) _⟩⟩,
  apply colimit.is_colimit,
end

lemma op_has_pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
  [h : has_pushout f g] : has_pullback f.op g.op :=
begin
  refine ⟨nonempty.intro ⟨_,
    pushout_cocone.op_is_colimit (colimit.cocone (span f g)) _⟩⟩,
  apply colimit.is_colimit,
end

lemma unop_has_pullback {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z)
  [h : has_pullback f g] : has_pushout f.unop g.unop :=
begin
  refine ⟨nonempty.intro ⟨_,
    pullback_cone.unop_is_limit (limit.cone (cospan f g)) _⟩⟩,
  apply limit.is_limit,
end

lemma op_has_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  [h : has_pullback f g] : has_pushout f.op g.op :=
begin
  refine ⟨nonempty.intro ⟨_,
    pullback_cone.op_is_limit (limit.cone (cospan f g)) _⟩⟩,
  apply limit.is_limit,
end


end limits

end category_theory