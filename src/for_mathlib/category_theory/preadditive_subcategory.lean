import category_theory.full_subcategory
import category_theory.preadditive.basic

namespace category_theory

variables {C : Type*} [category C] [preadditive C]

instance (A : C → Prop) : preadditive (full_subcategory A) :=
{ hom_group := λ X Y, (infer_instance : add_comm_group (X.1 ⟶ Y.1)),
  add_comp' := λ P Q R f f' g, by convert preadditive.add_comp P.1 Q.1 R.1 f f' g,
  comp_add' := λ P Q R f g g', by convert preadditive.comp_add P.1 Q.1 R.1 f g g', }

end category_theory
