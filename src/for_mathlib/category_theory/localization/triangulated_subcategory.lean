import for_mathlib.category_theory.localization.triangulated
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.triangulated.shift_triangle
import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.category_theory.preadditive_subcategory
import for_mathlib.category_theory.triangulated.coproducts

noncomputable theory

universes v₁ v₂ u₁ u₂

open_locale zero_object

namespace set

open category_theory

class respects_iso {X : Type*} [category X] (A : set X) : Prop :=
(condition : ∀ ⦃x y : X⦄ (e : x ≅ y) (hx : x ∈ A), y ∈ A)

end set

namespace category_theory

open limits category preadditive

namespace functor

@[simps]
def map_arrow_nat_trans_of_nat_trans {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  {F G : C ⥤ D} (τ : F ⟶ G) : F.map_arrow ⟶ G.map_arrow :=
{ app := λ f,
  { left := τ.app _,
    right := τ.app _, }, }

@[simps]
def map_arrow_nat_iso_of_nat_iso {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
  {F G : C ⥤ D} (e : F ≅ G) : F.map_arrow ≅ G.map_arrow :=
{ hom := map_arrow_nat_trans_of_nat_trans e.hom,
  inv := map_arrow_nat_trans_of_nat_trans e.inv, }

end functor

namespace triangulated

open pretriangulated

variables (C : Type*) [category C] [has_zero_object C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), functor.additive (shift_functor C n)]
  [pretriangulated C] [triangulated C]

structure subcategory :=
(set : set C)
(zero : (0 : C) ∈ set)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ set), (shift_functor C n).obj X ∈ set)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ set) (h₃ : T.obj₃ ∈ set), T.obj₂ ∈ set)

variable {C}

namespace subcategory

variable (A : subcategory C)

lemma respects_iso : A.set.respects_iso :=
⟨λ X Y e hX, A.ext₂ _ (pretriangulated.isomorphic_distinguished _
  (pretriangulated.contractible_distinguished X) (triangle.mk C e.hom (0 : Y ⟶ 0) 0)
  (triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy))) hX A.zero⟩

lemma ext₁
  (T : triangle C) (hT : T ∈ dist_triang C) (h₂ : T.obj₂ ∈ A.set) (h₃ : T.obj₃ ∈ A.set) :
  T.obj₁ ∈ A.set :=
A.ext₂ T.inv_rotate (pretriangulated.inv_rot_of_dist_triangle C T hT) (A.shift _ (-1 : ℤ) h₃) h₂

lemma ext₃
  (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ A.set) (h₂ : T.obj₂ ∈ A.set) :
  T.obj₃ ∈ A.set :=
A.ext₂ T.rotate (pretriangulated.rot_of_dist_triangle C T hT) h₂ (A.shift _ (1 : ℤ) h₁)

def W : morphism_property C :=
λ X Y f, ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor C (1 : ℤ)).obj X)
  (H : triangle.mk C f g h ∈ dist_triang C), Z ∈ A.set

def W' : morphism_property C :=
λ Y Z g, ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧) (H : triangle.mk C f g h ∈ dist_triang C),
    X ∈ A.set

variable {A}

def W.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₃ ∈ A.set) :
  (W A) T.mor₁ :=
⟨T.obj₃, T.mor₂, T.mor₃, (by { cases T, exact hT, }), h⟩

def W'.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₁ ∈ A.set) :
  (W' A) T.mor₂ :=
⟨T.obj₁, T.mor₁, T.mor₃, (by { cases T, exact hT, }), h⟩

def W.triangle {X Y : C} (f : X ⟶ Y) (hf : (W A) f) : triangle C :=
triangle.mk C f hf.some_spec.some hf.some_spec.some_spec.some

lemma W.triangle_distinguished {X Y : C} (f : X ⟶ Y) (hf : (W A) f) :
  W.triangle f hf ∈ dist_triang C := hf.some_spec.some_spec.some_spec.some

lemma W.triangle_obj₃_mem {X Y : C} (f : X ⟶ Y) (hf : (W A) f) :
  (W.triangle f hf).obj₃ ∈ A.set :=
hf.some_spec.some_spec.some_spec.some_spec

variable (A)

lemma W_eq_W' : W A = W' A :=
begin
  ext X Y f,
  split,
  { rintro ⟨Z, g, h, H, mem⟩,
    exact ⟨_, _, _, inv_rot_of_dist_triangle C _ H, subcategory.shift A _ (-1 : ℤ) mem⟩, },
  { rintro ⟨Z, g, h, H, mem⟩,
    refine ⟨_, _, _, rot_of_dist_triangle C _ H, subcategory.shift A _ (1 : ℤ) mem⟩, },
end

variable {A}

def W.mk' {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₁ ∈ A.set) :
  (W A) T.mor₂ :=
by simpa only [W_eq_W'] using W'.mk hT h

instance W_contains_identities : (W A).contains_identities :=
⟨λ X, ⟨0, 0, 0, pretriangulated.contractible_distinguished X, subcategory.zero A⟩⟩

variable (A)

lemma W_stable_under_composition : (W A).stable_under_composition :=
λ X₁ X₂ X₃ u₁₂ u₂₃ h₁₂ h₂₃,
begin
  rcases h₁₂ with ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩,
  rcases h₂₃ with ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩,
  rcases pretriangulated.distinguished_cocone_triangle _ _ (u₁₂ ≫ u₂₃) with ⟨Z₁₃, v₁₃, w₁₃, H₁₃⟩,
  refine ⟨_, _, _, H₁₃, _⟩,
  exact subcategory.ext₂ A _ (octahedron.triangle_distinguished rfl H₁₂ H₂₃ H₁₃) mem₁₂ mem₂₃,
end

lemma W_respects_iso : (W A).respects_iso :=
begin
  split,
  { rintro X' X Y e f ⟨Z, g, h, mem, mem'⟩,
    refine ⟨Z, g, h ≫ (shift_functor C 1).map e.inv, _, mem'⟩,
    refine pretriangulated.isomorphic_distinguished _ mem _ _,
    refine triangle.mk_iso _ _ e (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
    dsimp,
    simp only [assoc, ← functor.map_comp, e.inv_hom_id, functor.map_id, comp_id, id_comp], },
  { rintro X Y Y' e f ⟨Z, g, h, mem, mem'⟩,
    refine ⟨Z, e.inv ≫ g, h, _, mem'⟩,
    refine pretriangulated.isomorphic_distinguished _ mem _ _,
    refine triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy), },
end

instance : left_calculus_of_fractions (W A) :=
{ id := infer_instance,
  comp := W_stable_under_composition A,
  ex := λ X' X Y s hs u, begin
    obtain ⟨Z, f, g, H, mem⟩ := hs,
    obtain ⟨Y', s', f', mem'⟩ := pretriangulated.distinguished_cocone_triangle₂ (g ≫ u⟦1⟧'),
    obtain ⟨b, ⟨hb₁, hb₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism₂ _ _
      H mem' u (𝟙 Z) (by { dsimp, rw id_comp, }),
    exact nonempty.intro ⟨Y', b, s', ⟨Z, f', g ≫ u⟦1⟧', mem', mem⟩, hb₁.symm⟩,
  end,
  ext := λ X' X Y f₁ f₂ s hs hf₁, begin
    let f := f₁ - f₂,
    have hf₂ : s ≫ f = 0 := by { dsimp [f], rw [comp_sub, hf₁, sub_self], },
    obtain ⟨Z, g, h, H, mem⟩ := hs,
    obtain ⟨q, hq⟩ := contravariant_yoneda_exact₂ _ H f hf₂,
    dsimp at q hq,
    obtain ⟨Y', r, t, mem'⟩ := pretriangulated.distinguished_cocone_triangle _ _ q,
    refine ⟨Y', r, _, _⟩,
    { exact ⟨_, _, _, rot_of_dist_triangle C _ mem', subcategory.shift A _ 1 mem⟩, },
    { rw [← sub_eq_zero, ← sub_comp],
      change f ≫ r = 0,
      have eq := comp_dist_triangle_mor_zero₁₂ C _ mem',
      dsimp at eq,
      rw [hq, assoc, eq, comp_zero], },
  end, }

instance : right_calculus_of_fractions (W A) :=
{ id := infer_instance,
  comp := W_stable_under_composition A,
  ex := λ X Y Y' s hs u, begin
    obtain ⟨Z, f, g, H, mem⟩ := hs,
    obtain ⟨X', f', h', mem'⟩ := pretriangulated.distinguished_cocone_triangle₁ (u ≫ f),
    obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism₁ _ _ mem' H u (𝟙 Z)
      (comp_id _),
    exact nonempty.intro ⟨X', a, f', ⟨Z, u ≫ f, h', mem', mem⟩, ha₁⟩,
  end,
  ext := λ Y Z Z' f₁ f₂ s hs hf₁, begin
    let f := f₁ - f₂,
    have hf₂ : f ≫ s = 0 := by { dsimp [f], rw [sub_comp, hf₁, sub_self], },
    rw W_eq_W' at hs,
    obtain ⟨X, g, h, H, mem⟩ := hs,
    obtain ⟨q, hq⟩ := covariant_yoneda_exact₂ _ H f hf₂,
    dsimp at q hq,
    obtain ⟨Y', r, t, mem'⟩ := pretriangulated.distinguished_cocone_triangle₁ q,
    refine ⟨Y', r, _, _⟩,
    { exact ⟨_, _, _, mem', mem⟩, },
    { rw [← sub_eq_zero, ← comp_sub],
    change r ≫ f = 0,
    have eq := comp_dist_triangle_mor_zero₁₂ C _ mem',
    dsimp at eq,
    rw [hq, ← assoc, eq, zero_comp], },
  end, }

lemma mul_mem_W_iff {X Y : C} (f : X ⟶ Y) (n : ℤ) :
  (W A) ((↑((-1 : units ℤ) ^ n) : ℤ) • f) ↔ (W A) f :=
(W_respects_iso A).arrow_mk_iso_iff
begin
  let e : X ≅ X :=
  { hom := (↑((-1 : units ℤ) ^ n) : ℤ) • 𝟙 X,
    inv := (↑((-1 : units ℤ) ^ n) : ℤ) • 𝟙 X,
    hom_inv_id' := by simp only [zsmul_comp, id_comp, smul_smul, int.units_coe_mul_self, one_smul],
    inv_hom_id' := by simp only [zsmul_comp, id_comp, smul_smul, int.units_coe_mul_self, one_smul], },
  refine arrow.iso_mk e (iso.refl _) _,
  dsimp,
  rw [comp_id, zsmul_comp, id_comp],
end

instance W_compatible_with_shift : (W A).compatible_with_shift ℤ :=
⟨begin
  have h : ∀ (X Y : C) (f : X ⟶ Y) (hf : (W A) f) (n : ℤ), (W A) (f⟦n⟧'),
  { rintro X Y f ⟨Z, g, h, H, mem⟩ n,
    rw ← mul_mem_W_iff A _ n,
    exact ⟨_, _, _, triangle.shift_distinguished C _ H n, subcategory.shift A Z n mem⟩, },
  intro n,
  ext X Y f,
  refine ⟨λ hf, _, λ hf, h _ _ f hf n⟩,
   exact ((W_respects_iso A).arrow_mk_iso_iff
    ((functor.map_arrow_nat_iso_of_nat_iso
    (shift_functor_comp_shift_functor_neg C n)).app (arrow.mk f))).mp (h _ _ _ hf (-n)),
end⟩

lemma pi_finite_stable {J : Type*} [finite J] (X : J → C) (hX : ∀ j, X j ∈ A.set)
  [has_product X] : (∏ X) ∈ A.set := sorry

instance W_stable_under_finite_products : (W A).stable_under_finite_products :=
⟨λ J, begin
  introI,
  refine morphism_property.stable_under_products_of_shape.mk _ _ (W_respects_iso A) _,
  intros X₁ X₂ f hf,
  let T := λ j, W.triangle _ (hf j),
  exact W.mk (triangle.product_distinghished T (λ j, W.triangle_distinguished _ (hf j)))
    (pi_finite_stable A (λ j, (T j).obj₃) (λ j, W.triangle_obj₃_mem _ (hf j))),
end⟩

instance W_compatible_with_triangulation : (W A).compatible_with_triangulation :=
⟨λ T₁ T₃ hT₁ hT₃ a b ha hb comm, begin
  let T'₁ := triangle.mk _ T₁.mor₁ T₁.mor₂ T₁.mor₃,
  let T'₃ := triangle.mk _ T₃.mor₁ T₃.mor₂ T₃.mor₃,
  have mem₁ : T'₁ ∈ dist_triang C := by { cases T₁, exact hT₁, },
  have mem₃ : T'₃ ∈ dist_triang C := by { cases T₃, exact hT₃, },
  rcases pretriangulated.distinguished_cocone_triangle _ _ (T₁.mor₁ ≫ b) with ⟨Z₂, g₂, h₂, mem₂⟩,
  let T'₂ := triangle.mk _ (T₁.mor₁ ≫ b) g₂ h₂,
  change T'₂ ∈ dist_triang C at mem₂,
  rcases hb with ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩,
  let φ₁₂ : T'₁ ⟶ T'₂ := octahedron.triangle_morphism₁ rfl mem₁ mem₄ mem₂,
  have hφ₁₂ : (W A) φ₁₂.hom₃ := W.mk (octahedron.triangle_distinguished rfl mem₁ mem₄ mem₂) mem₄',
  rcases ha with ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩,
  let φ₂₃ : T'₂ ⟶ T'₃ := octahedron.triangle_morphism₂ comm.symm mem₅ mem₃ mem₂,
  have hφ₂₃ : (W A) φ₂₃.hom₃ := W.mk' (octahedron.triangle_distinguished comm.symm mem₅ mem₃ mem₂) mem₅',
  refine ⟨(φ₁₂ ≫ φ₂₃).hom₃, W_stable_under_composition A _ _ hφ₁₂ hφ₂₃, ⟨_, _⟩⟩,
  { have h := (φ₁₂ ≫ φ₂₃).comm₂,
    dsimp at h,
    simpa only [comp_id] using h, },
  { have h := (φ₁₂ ≫ φ₂₃).comm₃,
    dsimp at h,
    simpa only [triangle_category_comp, triangle_morphism.comp_hom₃, id_comp] using h, },
end⟩

instance W_is_saturated : (W A).is_saturated := sorry

lemma test [has_finite_products C] : pretriangulated (W A).localization := infer_instance

@[protected, derive category, derive preadditive]
def category := full_subcategory A.set

instance : preadditive (subcategory.category A) := infer_instance

instance : has_zero_object (subcategory.category A) :=
⟨⟨⟨0, A.zero⟩, ⟨λ X, nonempty.intro (unique_of_subsingleton 0),
  λ X, nonempty.intro (unique_of_subsingleton 0)⟩⟩⟩

end subcategory

end triangulated

end category_theory
