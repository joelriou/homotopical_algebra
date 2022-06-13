
import category_theory.limits.opposites
import tactic.equiv_rw

universes v u

open category_theory category_theory.limits opposite

namespace category_theory

namespace limits

variables {C : Type u} [category.{v} C]

/-- The canonical isomorphism relating `span f.op g.op` and `(cospan f g).op` -/
@[simps]
def span_op {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  span f.op g.op ≅ walking_cospan_op_equiv.inverse ⋙ (cospan f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, })
(by { rintros (_|_|_) (_|_|_) f; cases f; tidy, })

/-- The canonical isomorphism relating `(cospan f g).op` and `span f.op g.op` -/
@[simps]
def op_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  (cospan f g).op ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op :=
begin
  calc (cospan f g).op ≅ 𝟭 _ ⋙ (cospan f g).op : by refl
  ... ≅ (walking_cospan_op_equiv.functor ⋙ walking_cospan_op_equiv.inverse) ⋙ (cospan f g).op :
    iso_whisker_right walking_cospan_op_equiv.unit_iso _
  ... ≅ walking_cospan_op_equiv.functor ⋙ (walking_cospan_op_equiv.inverse ⋙ (cospan f g).op) :
    functor.associator _ _ _
  ... ≅ walking_cospan_op_equiv.functor ⋙ span f.op g.op : iso_whisker_left _ (span_op f g).symm,
end

/-- The canonical isomorphism relating `cospan f.op g.op` and `(span f g).op` -/
@[simps]
def cospan_op {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  cospan f.op g.op ≅ walking_span_op_equiv.inverse ⋙ (span f g).op :=
nat_iso.of_components (by { rintro (_|_|_); refl, })
(by { rintros (_|_|_) (_|_|_) f; cases f; tidy, })

/-- The canonical isomorphism relating `(span f g).op` and `cospan f.op g.op` -/
@[simps]
def op_span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  (span f g).op ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op :=
begin
  calc (span f g).op ≅ 𝟭 _ ⋙ (span f g).op : by refl
  ... ≅ (walking_span_op_equiv.functor ⋙ walking_span_op_equiv.inverse) ⋙ (span f g).op :
    iso_whisker_right walking_span_op_equiv.unit_iso _
  ... ≅ walking_span_op_equiv.functor ⋙ (walking_span_op_equiv.inverse ⋙ (span f g).op) :
    functor.associator _ _ _
  ... ≅ walking_span_op_equiv.functor ⋙ cospan f.op g.op :
    iso_whisker_left _ (cospan_op f g).symm,
end

namespace pushout_cocone

/-- The obvious map `pushout_cocone f g → pullback_cone f.unop g.unop` -/
@[simps]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.unop g.unop :=
cocone.unop ((cocones.precompose (op_cospan f.unop g.unop).hom).obj
  (cocone.whisker walking_cospan_op_equiv.functor c))

/-- A colimit pushout_cocone in the opposite category can be transformed into
a limit pullback_cone -/
def unop_is_limit {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g)
  (h : is_colimit c) : is_limit c.unop :=
begin
  apply is_limit_cocone_unop,
  equiv_rw is_colimit.precompose_hom_equiv _ _,
  equiv_rw (is_colimit.whisker_equivalence_equiv _).symm,
  exact h,
end

/-- The obvious map `pushout_cocone f.op g.op → pullback_cone f g` -/
@[simps]
def op {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g) :
  pullback_cone f.op g.op :=
(cones.postcompose ((cospan_op f g).symm).hom).obj
  (cone.whisker walking_span_op_equiv.inverse (cocone.op c))

/-- A colimit pushout_cocone can be transformed into a limit pullback_cone
in the opposite category -/
def op_is_limit {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (c : pushout_cocone f g)
  (h : is_colimit c) : is_limit c.op :=
begin
  equiv_rw is_limit.postcompose_hom_equiv _ _,
  equiv_rw (is_limit.whisker_equivalence_equiv walking_span_op_equiv.symm).symm,
  exact is_limit_cocone_op _ h,
end

end pushout_cocone

namespace pullback_cone

/-- The obvious map `pullback_cone f g → pushout_cocone f.unop g.unop` -/
@[simps]
def unop {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.unop g.unop :=
cone.unop ((cones.postcompose (op_span f.unop g.unop).symm.hom).obj
  (cone.whisker walking_span_op_equiv.functor c))

/-- A colimit pullback_cone in the opposite category can be transformed into
a limit pushout_cocone -/
def unop_is_colimit {X Y Z : Cᵒᵖ} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g)
  (h : is_limit c) : is_colimit c.unop :=
begin
  apply is_colimit_cone_unop,
  equiv_rw is_limit.postcompose_hom_equiv _ _,
  equiv_rw (is_limit.whisker_equivalence_equiv _).symm,
  exact h,
end

/-- The obvious map `pullback_cone f g → pushout_cocone f.op g.op` -/
@[simps]
def op {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g) :
  pushout_cocone f.op g.op :=
(cocones.precompose (span_op f g).hom).obj
  (cocone.whisker walking_cospan_op_equiv.inverse (cone.op c))

/-- A colimit pullback_cone can be transformed into a limit pushout_cocone
in the opposite category -/
def op_is_colimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : pullback_cone f g)
  (h : is_limit c) : is_colimit c.op :=
begin
  equiv_rw is_colimit.precompose_hom_equiv _ _,
  equiv_rw (is_colimit.whisker_equivalence_equiv walking_cospan_op_equiv.symm).symm,
  exact is_colimit_cone_op _ h,
end

end pullback_cone

end limits

end category_theory
