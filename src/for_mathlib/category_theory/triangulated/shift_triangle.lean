import for_mathlib.category_theory.localization.triangulated
import tactic.linarith

noncomputable theory

namespace category_theory

section
open category

variables (C : Type*) [category C] {A : Type*} [add_comm_monoid A]
  [has_shift C A]

def shift_functor_add_comm (a₁ a₂ : A) :
  shift_functor C a₁ ⋙ shift_functor C a₂ ≅
  shift_functor C a₂ ⋙ shift_functor C a₁ :=
(shift_functor_add C a₁ a₂).symm ≪≫ eq_to_iso (by rw add_comm a₁ a₂) ≪≫ (shift_functor_add C a₂ a₁)

@[simp]
lemma shift_functor_add_comm_hom_app (a₁ a₂ : A) (X : C) :
  (shift_functor_add_comm C a₁ a₂).hom.app X  = (shift_functor_add C a₁ a₂).inv.app X ≫
  eq_to_hom (by rw add_comm a₁ a₂) ≫ (shift_functor_add C a₂ a₁).hom.app X :=
begin
  dsimp only [shift_functor_add_comm, iso.trans, eq_to_iso],
  simp only [iso.symm_hom, nat_trans.comp_app, eq_to_hom_app],
end

@[simp]
lemma shift_functor_add_comm_eq_refl (a : A) :
  shift_functor_add_comm C a a = iso.refl _ :=
begin
  ext X,
  dsimp only [shift_functor_add_comm, iso.trans, eq_to_iso, iso.symm, iso.refl],
  rw [eq_to_hom_refl, id_comp, iso.inv_hom_id],
end

end

open limits

namespace triangulated

open preadditive category pretriangulated

variables (C : Type*) [category C] [preadditive C] [has_shift C ℤ]

@[simps]
def triangle.shift_functor (n : ℤ) : triangle C ⥤ triangle C :=
{ obj := λ T, begin
    let ε : ℤ := ↑((-1 : units ℤ) ^ n),
    exact triangle.mk C (ε • (shift_functor C n).map T.mor₁)
      (ε • (shift_functor C n).map T.mor₂)
      ((ε • (shift_functor C n).map T.mor₃) ≫ (shift_functor_add_comm C 1 n).hom.app _),
  end,
  map := λ T₁ T₂ f,
  { hom₁ := (shift_functor C n).map f.hom₁,
    hom₂ := (shift_functor C n).map f.hom₂,
    hom₃ := (shift_functor C n).map f.hom₃,
    comm₁' := by { dsimp, simp only [preadditive.zsmul_comp, preadditive.comp_zsmul,
      ← functor.map_comp, f.comm₁], },
    comm₂' := by { dsimp, simp only [preadditive.zsmul_comp, preadditive.comp_zsmul,
      ← functor.map_comp, f.comm₂], },
    comm₃' := by { dsimp,
      simp only [assoc, preadditive.zsmul_comp, preadditive.comp_zsmul, ← functor.map_comp_assoc,
        ← f.comm₃],
      simp only [functor.map_comp, assoc],
      erw ← nat_trans.naturality,
      refl, }, }, }

variables [has_zero_object C] [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

def triangle.shift_functor_one_iso : triangle.shift_functor C 1 ≅ rotate C ⋙ rotate C ⋙ rotate C :=
nat_iso.of_components
  (λ T, triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) begin
    dsimp,
    simp only [zpow_one, units.coe_neg_one, neg_smul, one_zsmul, neg_comp, functor.map_id,
      comp_id, id_comp, neg_inj, shift_functor_add_comm_eq_refl, iso.refl_hom, nat_trans.id_app],
    apply comp_id,
  end)
  (by tidy)

local attribute [reducible] discrete.add_monoidal

def triangle.shift_functor_zero : triangle.shift_functor C 0 ≅ 𝟭 _ :=
nat_iso.of_components (λ T, triangle.mk_iso _ _ ((shift_functor_zero C ℤ).app _)
  ((shift_functor_zero C ℤ).app _) ((shift_functor_zero C ℤ).app _) (by tidy) (by tidy) begin
  dsimp,
  simp only [zpow_zero, units.coe_one, one_zsmul, assoc, shift_functor_add_comm_hom_app],
  erw ← nat_trans.naturality,
  congr' 1,
  dsimp,
  simp only [obj_ε_inv_app, discrete.functor_map_id, nat_trans.id_app, comp_id,
    μ_inv_hom_app, ε_inv_app_obj],
end) (by tidy)

def triangle.shift_functor_add (a₁ a₂ : ℤ) :
  triangle.shift_functor C (a₁ + a₂) ≅
    triangle.shift_functor C a₁ ⋙ triangle.shift_functor C a₂ :=
nat_iso.of_components (λ T, begin
  dsimp only [triangle.shift_functor],
  refine triangle.mk_iso _ _ ((shift_functor_add C a₁ a₂).app _) ((shift_functor_add C a₁ a₂).app _)
    ((shift_functor_add C a₁ a₂).app _) _ _ _,
  { dsimp only [triangle.mk, functor.comp],
    simp only [zsmul_comp, comp_zsmul, functor.map_zsmul, smul_smul],
    congr' 1,
    { rw [zpow_add, units.coe_mul, mul_comm], },
    { exact (shift_functor_add C a₁ a₂).hom.naturality T.mor₁, }, },
  { dsimp only [triangle.mk, functor.comp],
    simp only [zsmul_comp, comp_zsmul, functor.map_zsmul, smul_smul,
      zpow_add, units.coe_mul, mul_comm],
    congr' 1,
    exact (shift_functor_add C a₁ a₂).hom.naturality T.mor₂, },
  { dsimp only [triangle.mk, functor.comp],
    simp only [zsmul_comp, comp_zsmul, functor.map_zsmul, smul_smul,
      zpow_add, units.coe_mul, mul_comm],
    congr' 1,
    simp only [functor.map_comp, assoc],
    erw ← nat_trans.naturality_assoc,
    congr' 1,
    sorry, },
end)
(λ T T' f, by ext; apply nat_trans.naturality)

def triangle.shift_functor_sub_one_iso : triangle.shift_functor C (-1) ≅ inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C :=
begin
  symmetry,
  calc inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C ≅ 𝟭 _ ⋙ inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C : (functor.left_unitor _).symm
  ... ≅ triangle.shift_functor C 0 ⋙ inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C :
    iso_whisker_right (triangle.shift_functor_zero C).symm _
  ... ≅ triangle.shift_functor C ((-1) + 1) ⋙ inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C :
    iso_whisker_right (eq_to_iso (by congr)) _
  ... ≅ (triangle.shift_functor C (-1) ⋙ triangle.shift_functor C 1) ⋙ inv_rotate C ⋙ inv_rotate C ⋙ inv_rotate C :
    iso_whisker_right (triangle.shift_functor_add C _ _) _
  ... ≅ _ : functor.associator _ _ _
  ... ≅ _ : iso_whisker_left _ _
  ... ≅ triangle.shift_functor C (-1) : functor.right_unitor _,
  let e : rotate C ⋙ inv_rotate C ≅ 𝟭 _ := (triangle_rotation C).unit_iso.symm,
  let α := iso_whisker_left (rotate C ⋙ rotate C) (iso_whisker_right e (inv_rotate C ⋙ inv_rotate C)),
  let β := iso_whisker_left (rotate C) (iso_whisker_right e (inv_rotate C)),
  exact iso_whisker_right (triangle.shift_functor_one_iso C) _ ≪≫ α ≪≫ β ≪≫ e,
end

def triangle.shift_functor_iso_of_eq {a₁ a₂ : ℤ} (h : a₁ = a₂) :
  triangle.shift_functor C a₁ ≅ triangle.shift_functor C a₂ := by subst h

lemma triangle.shift_distinguished (T : triangle C) (hT : T ∈ dist_triang C) (n : ℤ) :
  (triangle.shift_functor C n).obj T ∈ dist_triang C :=
begin
  have hpos : ∀ (T' : triangle C) (hT' : T' ∈ dist_triang C),
    (triangle.shift_functor C (1 : ℤ)).obj T' ∈ dist_triang C,
  { intros T' hT',
    exact pretriangulated.isomorphic_distinguished _ (rot_of_dist_triangle C _
      (rot_of_dist_triangle C _ (rot_of_dist_triangle C _ hT'))) _
      ((triangle.shift_functor_one_iso C).app T'), },
  have hneg : ∀ (T' : triangle C) (hT' : T' ∈ dist_triang C),
    (triangle.shift_functor C (-1 : ℤ)).obj T' ∈ dist_triang C,
  { intros T' hT',
    exact pretriangulated.isomorphic_distinguished _ (inv_rot_of_dist_triangle C _
      (inv_rot_of_dist_triangle C _ (inv_rot_of_dist_triangle C _ hT'))) _
      ((triangle.shift_functor_sub_one_iso C).app T'), },
  by_cases 0 ≤ n,
  { obtain ⟨m, hm⟩ : ∃ (m : ℕ), n = m := int.eq_coe_of_zero_le h,
    subst hm, clear h,
    induction m with n hn,
    { exact pretriangulated.isomorphic_distinguished _ hT _
        ((triangle.shift_functor_zero C).app T), },
    { refine pretriangulated.isomorphic_distinguished _ _ _
        ((triangle.shift_functor_add C (↑n) 1).app T),
      apply hpos,
      apply hn, }, },
  { obtain ⟨m, hm⟩ : ∃ (m : ℕ), n = -(m : ℤ),
    { obtain ⟨k, hk⟩ := int.eq_coe_of_zero_le (show 0 ≤ -n, by linarith),
      exact ⟨k, by linarith⟩, },
    subst hm, clear h,
    induction m with n hn,
    { exact pretriangulated.isomorphic_distinguished _ hT _
        ((triangle.shift_functor_zero C).app T), },
    { refine pretriangulated.isomorphic_distinguished _ _ _
        (_ ≪≫ (triangle.shift_functor_add C (-↑n) (-1 : ℤ)).app T),
      { apply hneg,
        apply hn, },
      { refine (triangle.shift_functor_iso_of_eq C _).app _,
        simp only [nat.cast_succ, neg_add_rev, int.add_neg_one],
        linarith, }, }, },
end

end triangulated

end category_theory
