import category_theory.preadditive.basic

namespace category_theory

namespace preadditive

variables {C : Type*} [category C] [preadditive C] {X Y : C}

@[simps]
def mul_iso (a : units ℤ) (e : X ≅ Y) : X ≅ Y :=
{ hom := (a : ℤ) • e.hom,
  inv := ((a⁻¹ : units ℤ) : ℤ) • e.inv,
  hom_inv_id' := by rw [preadditive.comp_zsmul, preadditive.zsmul_comp, smul_smul,
    units.inv_mul, one_smul, e.hom_inv_id],
  inv_hom_id' := by rw [preadditive.comp_zsmul, preadditive.zsmul_comp, smul_smul,
    units.mul_inv, one_smul, e.inv_hom_id], }

end preadditive

end category_theory
