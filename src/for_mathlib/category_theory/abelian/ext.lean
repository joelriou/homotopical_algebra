import for_mathlib.category_theory.triangulated.hom_homological
import for_mathlib.algebra.homology.trunc

noncomputable theory

namespace category_theory

open derived_category category limits

variables {C : Type*} [category C] [abelian C]

def Ext (n : ℕ) (X Y : C) :=
((single_functor C 0).obj X ⟶ ((single_functor C 0).obj Y)⟦(n : ℤ)⟧)

def Ext_functor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ AddCommGroup :=
(single_functor C 0).op ⋙ preadditive_coyoneda ⋙
  (whiskering_left _ _ AddCommGroup).obj (single_functor C 0 ⋙ shift_functor _ (n : ℤ))

instance (n : ℕ) (X Y : C) : add_comm_group (Ext n X Y) :=
by { dsimp only [Ext], apply_instance, }

def Ext_map₁ (n : ℕ) {X X' : C} (f : X' ⟶ X) (Y : C) :
  Ext n X Y →+ Ext n X' Y :=
{ to_fun := λ e, ((single_functor C 0).map f) ≫ e,
  map_zero' := by simp,
  map_add' := by simp, }

def Ext_map₂ (n : ℕ) (X : C) {Y Y' : C} (g : Y ⟶ Y') :
  Ext n X Y →+ Ext n X Y' :=
{ to_fun := λ e, e ≫ ((single_functor C 0).map g)⟦(n : ℤ)⟧',
  map_zero' := by simp,
  map_add' := by simp, }

lemma Ext_map₁₂_comm (n : ℕ) {X X' Y Y' : C} (f : X' ⟶ X) (g : Y ⟶ Y') :
  (Ext_map₂ n X' g).comp (Ext_map₁ n f Y) = (Ext_map₁ n f Y').comp (Ext_map₂ n X g) :=
begin
  ext x,
  dsimp [Ext_map₂, Ext_map₁],
  rw assoc,
end

@[simp]
lemma Ext_map₁_id (n : ℕ) (X Y : C) :
  Ext_map₁ n (𝟙 X) Y = add_monoid_hom.id _ :=
begin
  ext x,
  dsimp [Ext_map₁],
  simp only [functor.map_id, id_comp],
end

@[simp]
lemma Ext_map₁_zero (n : ℕ) (X X' Y : C) :
  Ext_map₁ n (0 : X ⟶ X') Y = 0 :=
begin
  ext x,
  dsimp [Ext_map₁],
  simp only [functor.map_zero, zero_comp],
end

@[simp]
lemma Ext_map₁_comp (n : ℕ) {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
  Ext_map₁ n (f ≫ f') Y = (Ext_map₁ n f Y).comp (Ext_map₁ n f' Y) :=
begin
  ext x,
  dsimp [Ext_map₁],
  simp only [functor.map_comp, assoc],
end

@[simp]
lemma Ext_map₂_id (n : ℕ) (X Y : C) :
  Ext_map₂ n X (𝟙 Y) = add_monoid_hom.id _ :=
begin
  ext x,
  dsimp [Ext_map₂],
  simp only [functor.map_id, comp_id],
end

@[simp]
lemma Ext_map₂_zero (n : ℕ) (X Y Y' : C) :
  Ext_map₂ n X (0 : Y ⟶ Y') = 0 :=
begin
  ext x,
  dsimp [Ext_map₂],
  simp only [functor.map_zero, comp_zero],
end

@[simp]
lemma Ext_map₂_comp (n : ℕ) (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
  Ext_map₂ n X (g ≫ g') = (Ext_map₂ n X g').comp (Ext_map₂ n X g) :=
begin
  ext x,
  dsimp [Ext_map₂],
  simp only [functor.map_comp, assoc],
end

namespace short_complex

namespace short_exact

variables {S : short_complex C} (ex : S.short_exact)

include ex

def triangle : pretriangulated.triangle (derived_category C) :=
triangle_of_ses
  (short_complex.short_exact.map_of_exact ex
  (homological_complex.single C (complex_shape.up ℤ) 0))

lemma triangle_dist : ex.triangle ∈ dist_triang (derived_category C) :=
triangle_of_ses_dist _

def Ext_δ₂ (X : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  Ext n₀ X S.X₃ →+ Ext n₁ X S.X₁ :=
{ to_fun := λ x, x ≫ ex.triangle.mor₃⟦(n₀ : ℤ)⟧' ≫
    (shift_functor_add' (derived_category C) (1 : ℤ) n₀ n₁
      (by rw [h, nat.cast_add, add_comm, algebra_map.coe_one])).inv.app _,
  map_zero' := by simp,
  map_add' := by simp, }

lemma Ext_comp_δ₂ (X : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (ex.Ext_δ₂ X n₀ n₁ h).comp (Ext_map₂ n₀ X S.g) = 0 :=
begin
  ext x,
  dsimp [Ext_map₂, Ext_δ₂],
  simp only [assoc],
  erw [← functor.map_comp_assoc, pretriangulated.triangle.comp_zero₂₃ _ ex.triangle_dist,
    functor.map_zero, zero_comp, comp_zero],
end

lemma Ext_δ₂_comp (X : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (Ext_map₂ n₁ X S.f).comp (ex.Ext_δ₂ X n₀ n₁ h) = 0 :=
begin
  ext x,
  dsimp [Ext_map₂, Ext_δ₂],
  simp only [assoc],
  erw [← nat_trans.naturality, ← functor.map_comp_assoc,
    pretriangulated.triangle.comp_zero₃₁ _ ex.triangle_dist, functor.map_zero,
    zero_comp, comp_zero],
end

lemma Ext_ex₂₂ (X : C) (n : ℕ) :
  (short_complex.mk (AddCommGroup.of_hom (Ext_map₂ n X S.f))
    (AddCommGroup.of_hom (Ext_map₂ n X S.g)) begin
      ext x,
      simp only [comp_apply, AddCommGroup.of_hom_apply, AddCommGroup.zero_apply],
      rw [← add_monoid_hom.comp_apply, ← Ext_map₂_comp, S.zero,
        Ext_map₂_zero, add_monoid_hom.zero_apply],
    end).exact :=
functor.is_homological.ex₂
  (preadditive_coyoneda.obj (opposite.op ((single_functor C 0).obj X))) _ ex.triangle_dist n

lemma Ext_ex₂₂' {X : C} {n : ℕ} (x₂ : Ext n X S.X₂)
  (hx₂ : Ext_map₂ n X S.g x₂ = 0) :
  ∃ (x₁ : Ext n X S.X₁), Ext_map₂ n X S.f x₁ = x₂ :=
begin
  have h := ex.Ext_ex₂₂ X n,
  rw AddCommGroup_exact_iff at h,
  exact h x₂ hx₂,
end

lemma Ext_ex₂₃ (X : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (short_complex.mk (AddCommGroup.of_hom (Ext_map₂ n₀ X S.g))
    (AddCommGroup.of_hom (ex.Ext_δ₂ X n₀ n₁ h)) begin
      ext x,
      simp only [comp_apply, AddCommGroup.of_hom_apply, AddCommGroup.zero_apply],
      rw [← add_monoid_hom.comp_apply, ex.Ext_comp_δ₂, add_monoid_hom.zero_apply],
    end).exact :=
functor.is_homological.ex₃
  (preadditive_coyoneda.obj (opposite.op ((single_functor C 0).obj X))) _ ex.triangle_dist _ _
  (by simp [h])

lemma Ext_ex₂₃' {X : C} (n₀ n₁ : ℕ) (h : n₁ = n₀+1)
  (x₃ : Ext n₀ X S.X₃)
  (hx₃ : ex.Ext_δ₂ X n₀ n₁ h x₃ = 0) :
  ∃ (x₂ : Ext n₀ X S.X₂), Ext_map₂ n₀ X S.g x₂ = x₃ :=
begin
  have h := ex.Ext_ex₂₃ X n₀ n₁ h,
  rw AddCommGroup_exact_iff at h,
  exact h x₃ hx₃,
end

lemma Ext_ex₂₁ (X : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (short_complex.mk (AddCommGroup.of_hom (ex.Ext_δ₂ X n₀ n₁ h))
    (AddCommGroup.of_hom (Ext_map₂ n₁ X S.f)) begin
      ext x,
      simp only [comp_apply, AddCommGroup.of_hom_apply, AddCommGroup.zero_apply],
      rw [← add_monoid_hom.comp_apply, ex.Ext_δ₂_comp, add_monoid_hom.zero_apply],
    end).exact :=
functor.is_homological.ex₁
  (preadditive_coyoneda.obj (opposite.op ((single_functor C 0).obj X))) _ ex.triangle_dist _ _ (by simp [h])

lemma Ext_ex₂₁' {X : C} (n₀ n₁ : ℕ) (h : n₁ = n₀+1)
  (x₁ : Ext n₁ X S.X₁)
  (hx₁ : Ext_map₂ n₁ X S.f x₁ = 0) :
  ∃ (x₃ : Ext n₀ X S.X₃), ex.Ext_δ₂ X n₀ n₁ h x₃ = x₁ :=
begin
  have h := ex.Ext_ex₂₁ X n₀ n₁ h,
  rw AddCommGroup_exact_iff at h,
  exact h x₁ hx₁,
end

def Ext_δ₁ (Y : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  Ext n₀ S.X₁ Y →+ Ext n₁ S.X₃ Y :=
{ to_fun := λ x, ((-1 : units ℤ)^n₁) • ex.triangle.mor₃ ≫ x⟦(1 : ℤ)⟧' ≫
    (shift_functor_add' (derived_category C) (n₀ : ℤ) 1 n₁
      (by rw [h, nat.cast_add, algebra_map.coe_one])).inv.app _,
  map_zero' := by simp only [functor.map_zero, zero_comp, comp_zero, smul_zero],
  map_add' := λ a b, by simp only [functor.map_add, preadditive.add_comp,
    preadditive.comp_add, smul_add], }

lemma Ext_δ₁_comp (Y : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (ex.Ext_δ₁ Y n₀ n₁ h).comp (Ext_map₁ n₀ S.f Y) = 0 :=
begin
  ext x,
  dsimp [Ext_δ₁, Ext_map₁],
  simp only [assoc, functor.map_comp],
  erw [pretriangulated.triangle.comp_zero₃₁_assoc _ ex.triangle_dist, zero_comp, smul_zero],
end

lemma Ext_comp_δ₁ (Y : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  (Ext_map₁ n₁ S.g Y).comp (ex.Ext_δ₁ Y n₀ n₁ h) = 0 :=
begin
  ext x,
  dsimp [Ext_map₁, Ext_δ₁],
  erw [preadditive.comp_zsmul, pretriangulated.triangle.comp_zero₂₃_assoc _ ex.triangle_dist,
    zero_comp, zsmul_zero],
end

lemma Ext_δ₁_δ₂ {S' : short_complex C} (ex' : S'.short_exact) (n₀ n₁ n₂ : ℕ)
  (hn₁ : n₁ = n₀+1) (hn₂ : n₂ = n₁+1) :
  (ex.Ext_δ₁ S'.X₁ n₁ n₂ hn₂).comp (ex'.Ext_δ₂ S.X₁ n₀ n₁ hn₁) =
    -(ex'.Ext_δ₂ S.X₃ n₁ n₂ hn₂).comp (ex.Ext_δ₁ S'.X₃ n₀ n₁ hn₁) :=
begin
  ext x,
  dsimp [Ext_δ₁, Ext_δ₂],
  simp only [hn₂, pow_add, pow_one, mul_neg, mul_one],
  erw preadditive.zsmul_comp,
  rw units.neg_smul,
  simp only [assoc, functor.map_comp],
  erw ← nat_trans.naturality_assoc,
  congr' 5,
  erw ← shift_functor_add₃'_inv_app (1 : ℤ) n₀ 1 n₂ (by linarith) n₁ (by linarith),
  rw ← shift_functor_add₃'_inv_app' (1 : ℤ) n₀ 1,
end

end short_exact

end short_complex

end category_theory
