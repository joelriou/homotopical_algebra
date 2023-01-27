import for_mathlib.category_theory.triangulated.shift_compatibility
import tactic.abel

noncomputable theory

universe u

open category_theory category_theory.category

namespace category_theory

variables {C : Type*} {A B : Type u} [category C] [add_monoid A] [add_monoid B]
  {G : Type*} [add_comm_group G]

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

variables (C A)

def has_shift_op [has_shift C A] : has_shift Cᵒᵖ A :=
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
  left_unitality := λ a X, quiver.hom.unop_inj begin
    dsimp,
    simpa only [obj_ε_inv_app, eq_to_iso.hom, μ_inv_hom_app_assoc, eq_to_hom_unop,
      eq_to_hom_map, eq_to_hom_app],
  end,
  right_unitality := λ a X, quiver.hom.unop_inj begin
    dsimp,
    simpa only [ε_inv_app_obj, eq_to_iso.hom, μ_inv_hom_app_assoc, eq_to_hom_unop,
      eq_to_hom_map, eq_to_hom_app],
  end, }

variable {A}

def has_shift_pull [has_shift C B] (φ : A →+ B) : has_shift C A :=
⟨monoidal_functor.comp (discrete.add_monoidal_functor φ) (shift_monoidal_functor C B)⟩

local attribute [instance] has_shift_op

variable {C}

def has_shift.op (s : has_shift C A) : has_shift Cᵒᵖ A :=
by { letI := s, apply_instance, }

def has_shift.pull (s : has_shift C B) (φ : A →+ B) : has_shift C A :=
by { letI := s, exact has_shift_pull C φ, }

def has_shift.op_neg (s : has_shift C G) :
  has_shift Cᵒᵖ G :=
s.op.pull (⟨λ g, -g, by tidy, λ x y, by abel⟩ : G →+ G)

variables (C G)

def has_shift_op_neg [has_shift C G] : has_shift Cᵒᵖ G :=
has_shift.op_neg infer_instance

def has_shift_op_neg_ℤ [has_shift C ℤ] : has_shift Cᵒᵖ ℤ :=
has_shift.op_neg infer_instance

end category_theory
