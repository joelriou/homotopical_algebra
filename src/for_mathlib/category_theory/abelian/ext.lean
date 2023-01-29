import for_mathlib.category_theory.triangulated.hom_homological
import for_mathlib.algebra.homology.trunc

noncomputable theory

namespace category_theory

open derived_category category limits

variables {C : Type*} [category C] [abelian C]

def Ext (n : ℕ) (X Y : C) :=
((single_functor C 0).obj X ⟶ ((single_functor C 0).obj Y)⟦(n : ℤ)⟧)

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

lemma Ext_δ₁ (Y : C) (n₀ n₁ : ℕ) (h : n₁ = n₀+1) :
  Ext n₀ S.X₁ Y →+ Ext n₁ S.X₃ Y :=
begin
  sorry,
end

end short_exact

end short_complex

--def Ext_functor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ AddCommGroup :=
--(single_functor C 0).op ⋙ preadditive_coyoneda ⋙
--  (whiskering_left _ _ AddCommGroup).obj (single_functor C 0 ⋙ shift_functor _ (n : ℤ))


end category_theory
