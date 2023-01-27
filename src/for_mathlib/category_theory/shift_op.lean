import for_mathlib.category_theory.triangulated.shift_compatibility

noncomputable theory

open category_theory category_theory.category
namespace category_theory

variables {C A : Type*} [category C] [add_monoid A]

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

variables (C A)

def has_shift_op [s : has_shift C A] : has_shift Cᵒᵖ A :=
has_shift_mk _ _
{ F := λ a, (shift_functor C a).op,
  ε := (functor.op_unop_equiv C C).functor.map_iso (shift_functor_zero C A).op,
  μ := λ a b, (functor.op_unop_equiv C C).functor.map_iso (shift_functor_add C a b).op,
  associativity := λ a b c X, quiver.hom.unop_inj begin
    have eq := congr_arg iso.inv (monoidal_functor.associativity_iso_eq (shift_monoidal_functor C A)
      (discrete.mk a) (discrete.mk b) (discrete.mk c)),
    replace eq := congr_app eq (opposite.unop X),
    dsimp at ⊢ eq,
    erw [comp_id, id_comp, functor.map_id, functor.map_id, comp_id] at eq,
    simpa only [← eq, eq_to_hom_unop, eq_to_hom_map, eq_to_hom_app],
  end,
  left_unitality := sorry,
  right_unitality := sorry, }

local attribute [instance] has_shift_op

def has_shift.op (s : has_shift C A) : has_shift Cᵒᵖ A :=
by { letI := s, apply_instance, }

end category_theory
