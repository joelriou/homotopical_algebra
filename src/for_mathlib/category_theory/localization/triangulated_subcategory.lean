import for_mathlib.category_theory.localization.triangulated
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.triangulated.shift_triangle
import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.category_theory.preadditive_subcategory
import for_mathlib.category_theory.triangulated.coproducts
import for_mathlib.category_theory.limits.products
import category_theory.limits.full_subcategory
import data.int.order.units

noncomputable theory

universes v₁ v₂ u₁ u₂

open_locale zero_object

namespace set

open category_theory

class respects_iso {X : Type*} [category X] (A : set X) : Prop :=
(condition' : ∀ ⦃x y : X⦄ (e : x ≅ y) (hx : x ∈ A), y ∈ A)

lemma respects_iso.condition {X : Type*} [category X] (A : set X) [A.respects_iso]
  {x y : X} (e : x ≅ y) (hx : x ∈ A) : y ∈ A :=
respects_iso.condition' e hx

lemma respects_iso.mem_iff_of_iso {X : Type*} [category X] (A : set X) [A.respects_iso]
  {x y : X} (e : x ≅ y) : x ∈ A ↔ y ∈ A :=
begin
  split,
  { exact respects_iso.condition A e, },
  { exact respects_iso.condition A e.symm, },
end

end set

open category_theory

namespace category_theory

open limits category preadditive category_theory

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
  [pretriangulated C]

structure subcategory :=
(set : set C)
(zero : (0 : C) ∈ set)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ set), (shift_functor C n).obj X ∈ set)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ set) (h₃ : T.obj₃ ∈ set), T.obj₂ ∈ set)

variable {C}

namespace subcategory

variable (A : subcategory C)

instance set_respects_iso : A.set.respects_iso :=
⟨λ X Y e hX, A.ext₂ _ (pretriangulated.isomorphic_distinguished _
  (pretriangulated.contractible_distinguished X) (triangle.mk e.hom (0 : Y ⟶ 0) 0)
  (triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy))) hX A.zero⟩

lemma ext₁
  (T : triangle C) (hT : T ∈ dist_triang C) (h₂ : T.obj₂ ∈ A.set) (h₃ : T.obj₃ ∈ A.set) :
  T.obj₁ ∈ A.set :=
A.ext₂ T.inv_rotate (pretriangulated.inv_rot_of_dist_triangle C T hT) (A.shift _ (-1 : ℤ) h₃) h₂

lemma ext₃
  (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ A.set) (h₂ : T.obj₂ ∈ A.set) :
  T.obj₃ ∈ A.set :=
A.ext₂ T.rotate (pretriangulated.rot_of_dist_triangle C T hT) h₂ (A.shift _ (1 : ℤ) h₁)

lemma shift_iff (X : C) (n : ℤ) : X ∈ A.set ↔ (shift_functor C n).obj X ∈ A.set :=
begin
  split,
  { intro h,
    exact A.shift X n h, },
  { intro h,
    exact set.respects_iso.condition A.set
      ((add_neg_equiv (shift_monoidal_functor C ℤ) n).unit_iso.symm.app X) (A.shift _ (-n) h), },
end

def W : morphism_property C :=
λ X Y f, ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor C (1 : ℤ)).obj X)
  (H : triangle.mk f g h ∈ dist_triang C), Z ∈ A.set

def W' : morphism_property C :=
λ Y Z g, ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧) (H : triangle.mk f g h ∈ dist_triang C),
    X ∈ A.set

variable {A}

def W.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₃ ∈ A.set) :
  (W A) T.mor₁ :=
⟨T.obj₃, T.mor₂, T.mor₃, (by { cases T, exact hT, }), h⟩

def W'.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₁ ∈ A.set) :
  (W' A) T.mor₂ :=
⟨T.obj₁, T.mor₁, T.mor₃, (by { cases T, exact hT, }), h⟩

def W.triangle {X Y : C} (f : X ⟶ Y) (hf : (W A) f) : triangle C :=
triangle.mk f hf.some_spec.some hf.some_spec.some_spec.some

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

lemma W_stable_under_composition [is_triangulated C] : (W A).stable_under_composition :=
λ X₁ X₂ X₃ u₁₂ u₂₃ h₁₂ h₂₃,
begin
  rcases h₁₂ with ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩,
  rcases h₂₃ with ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩,
  rcases pretriangulated.distinguished_cocone_triangle _ _ (u₁₂ ≫ u₂₃) with ⟨Z₁₃, v₁₃, w₁₃, H₁₃⟩,
  refine ⟨_, _, _, H₁₃, _⟩,
  exact subcategory.ext₂ A _ (is_triangulated.octahedron_axiom rfl H₁₂ H₂₃ H₁₃).some.mem
    mem₁₂ mem₂₃,
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

instance [is_triangulated C] : left_calculus_of_fractions (W A) :=
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

instance [is_triangulated C] : right_calculus_of_fractions (W A) :=
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

variable {A}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : (W A) f) (n : ℤ) :
  (W A) ((shift_functor C n).map f) :=
by simpa only [(morphism_property.compatible_with_shift.iff (W A) f n)] using hf

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (n : ℤ) (hf : (W A) ((shift_functor C n).map f)) :
  (W A) f :=
by simpa only [← (morphism_property.compatible_with_shift.iff (W A) f n)] using hf

variable (A)

lemma binary_product_stable (X₁ X₂ : C) (hX₁ : X₁ ∈ A.set)
  (hX₂ : X₂ ∈ A.set) : (X₁ ⨯ X₂) ∈ A.set :=
A.ext₂ _ (binary_product_triangle_distinguished X₁ X₂) hX₁ hX₂

lemma pi_finite_stable {J : Type} [finite J]
  (X : J → C) (hX : ∀ j, X j ∈ A.set) : (∏ X) ∈ A.set :=
begin
  revert hX X,
  let P : Type → Prop := λ J,
    ∀ [hJ : finite J] (X : J → C) (hX : ∀ j, X j ∈ A.set),
      by { haveI := hJ, exact (∏ X) ∈ A.set, },
  suffices : P J,
  { exact this, },
  refine finite.induction_empty_option _ _ _ J,
  { intros J₁ J₂ e hJ₁, introI, intros X hX,
    haveI : finite J₁ := finite.of_equiv _ e.symm,
    haveI := has_product_of_equiv X e,
    exact set.respects_iso.condition A.set(product_iso_of_equiv X e)
      (hJ₁ (X ∘ e) (λ j₁, hX _)), },
  { introI, intros X hX,
    refine set.respects_iso.condition A.set  _ A.zero,
    refine (limits.is_zero.iso_zero _).symm,
    haveI : mono (0 : ∏ X ⟶ 0),
    { constructor,
      intros Z f₁ f₂ hf,
      ext,
      discrete_cases,
      induction j, },
    exact limits.is_zero.of_mono (0 : ∏ X ⟶ 0) (is_zero_zero C), },
  { intro J,
    introI,
    intros hJ hJ' X hX,
    exact set.respects_iso.condition _ (product_iso_option X).symm
      (binary_product_stable A _ _ (hJ (λ j, X (some j)) (λ j, hX _)) (hX none)), },
end

instance W_stable_under_finite_products : (W A).stable_under_finite_products :=
⟨λ J, begin
  introI,
  refine morphism_property.stable_under_products_of_shape.mk _ _ (W_respects_iso A) _,
  intros X₁ X₂ f hf,
  let T := λ j, W.triangle _ (hf j),
  exact W.mk (triangle.product_distinghished T (λ j, W.triangle_distinguished _ (hf j)))
    (pi_finite_stable A (λ j, (T j).obj₃) (λ j, W.triangle_obj₃_mem _ (hf j))),
end⟩

instance W_compatible_with_triangulation [is_triangulated C] :
  (W A).compatible_with_triangulation :=
⟨λ T₁ T₃ hT₁ hT₃ a b ha hb comm, begin
  let T'₁ := triangle.mk T₁.mor₁ T₁.mor₂ T₁.mor₃,
  let T'₃ := triangle.mk T₃.mor₁ T₃.mor₂ T₃.mor₃,
  have mem₁ : T'₁ ∈ dist_triang C := by { cases T₁, exact hT₁, },
  have mem₃ : T'₃ ∈ dist_triang C := by { cases T₃, exact hT₃, },
  rcases pretriangulated.distinguished_cocone_triangle _ _ (T₁.mor₁ ≫ b) with ⟨Z₂, g₂, h₂, mem₂⟩,
  let T'₂ := triangle.mk (T₁.mor₁ ≫ b) g₂ h₂,
  change T'₂ ∈ dist_triang C at mem₂,
  rcases hb with ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩,
  let H := (is_triangulated.octahedron_axiom rfl mem₁ mem₄ mem₂).some,
  let φ₁₂ : T'₁ ⟶ T'₂ := H.triangle_morphism₁,
  have hφ₁₂ : (W A) φ₁₂.hom₃ := W.mk H.mem mem₄',
  rcases ha with ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩,
  let H' := (is_triangulated.octahedron_axiom comm.symm mem₅ mem₃ mem₂).some,
  let φ₂₃ : T'₂ ⟶ T'₃ := H'.triangle_morphism₂,
  have hφ₂₃ : (W A) φ₂₃.hom₃ := W.mk' H'.mem mem₅',
  refine ⟨(φ₁₂ ≫ φ₂₃).hom₃, W_stable_under_composition A _ _ hφ₁₂ hφ₂₃, ⟨_, _⟩⟩,
  { have h := (φ₁₂ ≫ φ₂₃).comm₂,
    dsimp at h,
    simpa only [comp_id] using h, },
  { have h := (φ₁₂ ≫ φ₂₃).comm₃,
    dsimp at h,
    simpa only [triangle_category_comp, triangle_morphism.comp_hom₃, id_comp] using h, },
end⟩

class saturated : Prop :=
(condition : ∀ ⦃X Y : C⦄ (i : Y ⟶ X) [hi : is_split_mono i] (hX : X ∈ A.set), Y ∈ A.set)

instance W_is_saturated [A.saturated] [is_triangulated C] : (W A).is_saturated :=
⟨λ X₁ X₂ X₃ X₄ f₁₂ f₂₃ f₃₄ h₁₃ h₂₄, begin
  obtain ⟨Y₁₃, g₁₃, h₁₃, H₁₃, mem₁₃⟩ := h₁₃,
  obtain ⟨Y₂₄, g₂₄, h₂₄, H₂₄, mem₂₄⟩ := h₂₄,
  obtain ⟨Y₁₂, g₁₂, h₁₂, H₁₂⟩ := pretriangulated.distinguished_cocone_triangle _ _ f₁₂,
  obtain ⟨Y₂₃, g₂₃, h₂₃, H₂₃⟩ := pretriangulated.distinguished_cocone_triangle _ _ f₂₃,
  obtain ⟨Y₃₄, g₃₄, h₃₄, H₃₄⟩ := pretriangulated.distinguished_cocone_triangle _ _ f₃₄,
  refine ⟨Y₂₃, g₂₃, h₂₃, H₂₃, _⟩,
  have H₁₂₃ := (is_triangulated.octahedron_axiom rfl H₁₂ H₂₃ H₁₃).some,
  have H₂₃₄ := (is_triangulated.octahedron_axiom rfl H₂₃ H₃₄ H₂₄).some,
  let s := h₂₃ ≫ g₁₂⟦1⟧',
  let t := h₃₄ ≫ g₂₃⟦1⟧',
  have hs : (W A) s := W.mk (rot_of_dist_triangle _ _
    (rot_of_dist_triangle _ _ H₁₂₃.mem)) (A.shift _ 1 mem₁₃),
  have ht : (W A) t := W.mk (rot_of_dist_triangle _ _
    (rot_of_dist_triangle _ _ H₂₃₄.mem)) (A.shift _ 1 mem₂₄),
  let st := t ≫ s⟦1⟧',
  have hst : st = 0,
  { dsimp [st],
    have eq : g₂₃ ≫ h₂₃ = 0 := triangle.comp_zero₂₃ _ H₂₃,
    simp only [assoc, ← functor.map_comp, reassoc_of eq,
      zero_comp, functor.map_zero, comp_zero], },
  have hst' := W_stable_under_composition A t (s⟦1⟧') ht (hs.shift 1),
  obtain ⟨Z, g, h, H, mem⟩ := hst',
  let i := (triangle.mk (t ≫ (shift_functor C 1).map s) g h).mor₂,
  haveI : mono i := mono_of_dist_triang₂ _ H hst,
  haveI : is_split_mono i := is_split_mono_of_mono i,
  have mem₁₂ := subcategory.saturated.condition i mem,
  dsimp [triangle.mk] at mem₁₂,
  rw [← A.shift_iff, ← A.shift_iff] at mem₁₂,
  exact A.ext₃ _ H₁₂₃.mem mem₁₂ mem₁₃,
end⟩

lemma test [is_triangulated C] : pretriangulated (W A).localization := infer_instance

@[protected, derive category, derive preadditive]
def category := full_subcategory A.set

instance : has_zero_object (subcategory.category A) :=
⟨⟨⟨0, A.zero⟩, ⟨λ X, nonempty.intro (unique_of_subsingleton 0),
  λ X, nonempty.intro (unique_of_subsingleton 0)⟩⟩⟩

@[simps]
def category.shift_functor (n : ℤ) : A.category ⥤ A.category :=
full_subcategory.lift A.set (full_subcategory_inclusion A.set ⋙ shift_functor C n)
  (λ X, (A.shift_iff X.obj n).mp X.property)

@[simps]
def category.comm_shift (n : ℤ) :
  category.shift_functor A n ⋙ full_subcategory_inclusion A.set ≅
    full_subcategory_inclusion A.set ⋙ shift_functor C n :=
    full_subcategory.lift_comp_inclusion _ _ _

@[simps]
instance : has_shift A.category ℤ := has_shift_of_fully_faithful
  (full_subcategory_inclusion A.set) (category.shift_functor A)
  (category.comm_shift A)

lemma category_closed_under_finite_products (J : Type) [finite J] :
  closed_under_limits_of_shape (discrete J) A.set :=
λ F c hc mem, begin
  let X := λ j, F.obj ⟨j⟩,
  refine set.respects_iso.condition A.set _ (A.pi_finite_stable X (λ j, mem ⟨j⟩)),
  exact
  { hom := hc.lift (cone.mk (∏ X) (discrete.nat_trans (by { rintro ⟨i⟩, exact pi.π _ i,}))),
    inv := pi.lift (λ i, c.π.app ⟨i⟩),
    hom_inv_id' := begin
      ext i,
      discrete_cases,
      simp only [assoc, limit.lift_π, fan.mk_π_app, is_limit.fac, discrete.nat_trans_app, id_comp],
    end,
    inv_hom_id' := hc.hom_ext begin
      rintro ⟨i⟩,
      simp only [assoc, is_limit.fac, discrete.nat_trans_app, limit.lift_π, fan.mk_π_app, id_comp],
    end, },
end

instance category_has_finite_products : has_finite_products (A.category) :=
⟨λ n, has_limits_of_shape_of_closed_under_limits (category_closed_under_finite_products A _)⟩

instance shift_functor_additive (n : ℤ) : (shift_functor A.category n).additive := infer_instance

@[simps]
def category_inclusion' : triangulated_functor_struct A.category C :=
{ comm_shift := category.comm_shift A 1,
  .. full_subcategory_inclusion A.set }

instance category_inclusion_additive : (category_inclusion' A).additive := { }

namespace category_pretriangulated

@[simp]
def distinguished_triangles : _root_.set (triangle A.category) :=
λ T, A.category_inclusion'.map_triangle.obj T ∈ dist_triang C

variable {A}

lemma isomorphic_distinguished (T₁ : triangle A.category)
  (hT₁ : T₁ ∈ distinguished_triangles A) (T₂ : triangle A.category) (e : T₂ ≅ T₁) :
  T₂ ∈ distinguished_triangles A :=
pretriangulated.isomorphic_distinguished _ hT₁ _
      (A.category_inclusion'.map_triangle.map_iso e)

lemma contractible_distinguished (X : A.category) :
  triangle.mk (𝟙 X) (0 : X ⟶ 0) 0 ∈ distinguished_triangles A :=
begin
  refine pretriangulated.isomorphic_distinguished _
    (pretriangulated.contractible_distinguished (A.category_inclusion'.obj X)) _ _,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) A.category_inclusion'.map_zero_object _ _ _,
  tidy,
end

lemma distinguished_cocone_triangle (X Y : A.category) (f : X ⟶ Y) :
  ∃ (Z : A.category) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor A.category (1 : ℤ)).obj X),
  triangle.mk f g h ∈ category_pretriangulated.distinguished_triangles A :=
begin
  obtain ⟨Z, g, h, mem⟩ := pretriangulated.distinguished_cocone_triangle
    _ _ ((category_inclusion' A).map f),
  refine ⟨⟨Z, A.ext₃ _ mem X.2 Y.2,⟩, g, h,
    pretriangulated.isomorphic_distinguished _ mem _ _⟩,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
  dsimp,
  simp only [functor.map_id, comp_id, id_comp],
  apply comp_id,
end

lemma rotate_distinguished_triangle (T : triangle A.category) :
  T ∈ category_pretriangulated.distinguished_triangles A ↔
    T.rotate ∈ category_pretriangulated.distinguished_triangles A :=
begin
  change (A.category_inclusion'.map_triangle.obj T ∈ dist_triang C) ↔
    (A.category_inclusion'.map_triangle.obj T.rotate ∈ dist_triang C),
  rw pretriangulated.rotate_distinguished_triangle,
  let e := (map_triangle_rotate A.category_inclusion').app T,
  split,
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e.symm, },
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e, },
end

lemma complete_distinguished_triangle_morphism (T₁ T₂ : triangle A.category)
  (hT₁ : T₁ ∈ distinguished_triangles A) (hT₂ : T₂ ∈ distinguished_triangles A)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (h : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫
    (shift_functor A.category 1).map a = c ≫ T₂.mor₃ :=
begin
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism
    (A.category_inclusion'.map_triangle.obj T₁) (A.category_inclusion'.map_triangle.obj T₂)
    hT₁ hT₂ a b h,
  refine ⟨c, ⟨hc₁, _⟩⟩,
  dsimp at hc₂,
  erw [comp_id, comp_id] at hc₂,
  exact hc₂,
end

end category_pretriangulated

instance : pretriangulated A.category :=
{ distinguished_triangles := category_pretriangulated.distinguished_triangles A,
  isomorphic_distinguished := category_pretriangulated.isomorphic_distinguished,
  contractible_distinguished := category_pretriangulated.contractible_distinguished,
  distinguished_cocone_triangle := category_pretriangulated.distinguished_cocone_triangle,
  rotate_distinguished_triangle := category_pretriangulated.rotate_distinguished_triangle,
  complete_distinguished_triangle_morphism :=
    category_pretriangulated.complete_distinguished_triangle_morphism, }

lemma dist_triang_iff {X Y Z : A.category} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) :
  (triangle.mk f g h ∈ dist_triang A.category) ↔
    (@triangle.mk C _ _ _ _ _ f g h ∈ dist_triang C) :=
begin
  change (_ ∈ dist_triang C) ↔ _,
  let e : A.category_inclusion'.map_triangle.obj (triangle.mk f g h) ≅
    @triangle.mk C _ _ _ _ _ f g h,
  { refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
    dsimp,
    erw [id_comp, functor.map_id, comp_id, comp_id], },
  split,
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e.symm, },
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e, },
end

instance [is_triangulated C] : is_triangulated A.category :=
⟨λ X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃, begin
  have comm' := A.category_inclusion'.congr_map comm,
  rw [functor.map_comp] at comm',
  have H := (is_triangulated.octahedron_axiom comm' h₁₂ h₂₃ h₁₃).some,
  obtain ⟨m₁, m₃, comm₁, comm₂, comm₃, comm₄, H'⟩ := H,
  refine nonempty.intro
  { m₁ := m₁,
    m₃ := m₃,
    comm₁ := comm₁,
    comm₂ := begin
      erw [comp_id, comp_id] at comm₂,
      exact comm₂,
    end,
    comm₃ := comm₃,
    comm₄ := begin
      erw [comp_id, comp_id] at comm₄,
      exact comm₄,
    end,
    mem := begin
      rw dist_triang_iff,
      refine pretriangulated.isomorphic_distinguished _ H' _ _,
      refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
      dsimp,
      erw [functor.map_id, comp_id, comp_id, id_comp],
      refl,
    end, }
end⟩

@[simps]
def category_inclusion : triangulated_functor A.category C :=
{ map_distinguished' := λ T hT, hT,
  ..A.category_inclusion' }

def Q [is_triangulated C] : triangulated_functor C A.W.localization :=
begin
  let F := localization_functor (W A).Q (W A),
  exact F,
end

/- TODO :
1) show a universal property for the triangulated functor `L` : if
`G : D ⥤ E` is a functor which lifts a triangulated functor `F : C ⥤ E`
then `G` is a triangulated functor.
 -/

instance Q_to_functor_is_localization [is_triangulated C] : A.Q.to_functor.is_localization A.W :=
(infer_instance : A.W.Q.is_localization A.W)

lemma is_iso_map_iff [A.saturated] [is_triangulated C] {X Y : C} (f : X ⟶ Y) : is_iso (A.Q.map f) ↔ A.W f :=
by convert localization.is_iso_map_iff_of_calculus_of_fractions (W A).Q (W A) f

lemma is_zero_obj_iff' [is_triangulated C] (X : C) :
  is_zero (A.Q.obj X) ↔ ∃ (Y : C) (i : X ⟶ Y) [is_split_mono i], Y ∈ A.set :=
begin
  rw limits.is_zero.iff_id_eq_zero,
  split,
  { intro h,
    have h' : A.W.Q.map (𝟙 X) = A.W.Q.map 0 :=
      by simpa only [functor.map_id, functor.map_zero] using h,
    rw right_calculus_of_fractions.L_map_eq_iff A.W.Q A.W at h',
    obtain ⟨Z, s, hs, eq⟩ := h',
    rw [comp_id, comp_zero] at eq,
    obtain ⟨Y, i, p, H, mem⟩ := hs,
    haveI : mono i := mono_of_dist_triang₂ _ H eq,
    exact ⟨Y, i, is_split_mono_of_mono i, mem⟩, },
  { rintro ⟨Y, i, hi, mem⟩,
    haveI : is_iso (A.W.Q.map (0 : Y ⟶ 0)) := localization.inverts A.W.Q A.W _
      (W.mk' (contractible_distinguished Y) mem),
    rw [← cancel_mono (A.W.Q.map i), id_comp, zero_comp,
      ← cancel_mono (A.W.Q.map (0 : Y ⟶ 0)), functor.map_zero, comp_zero, comp_zero], },
end

lemma is_zero_obj_iff [A.saturated] [is_triangulated C] (X : C) : is_zero (A.Q.obj X) ↔ X ∈ A.set :=
begin
  rw is_zero_obj_iff',
  split,
  { intro h,
    obtain ⟨Y, i, hi, mem⟩ := h,
    haveI := hi,
    exact saturated.condition i mem, },
  { exact λ h, ⟨X, 𝟙 X, infer_instance, h⟩, },
end

def left_orthogonal : subcategory C :=
{ set := λ X, ∀ ⦃Y : C⦄ (f : X ⟶ Y) (hY : Y ∈ A.set), f = 0,
  zero := by tidy,
  shift := λ X n h Y f hY, begin
    let adj : shift_functor C n ⊣ shift_functor C (-n) :=
      (add_neg_equiv (shift_monoidal_functor C ℤ) n).to_adjunction,
    apply (adj.hom_equiv _ _).injective,
    rw [(h _ (A.shift Y (-n) hY) : adj.hom_equiv _ _ f = 0),
      adjunction.hom_equiv_unit, functor.map_zero, comp_zero],
  end,
  ext₂ := λ T hT h₁ h₃ Y f hY, begin
    obtain ⟨g, hg⟩ := contravariant_yoneda_exact₂ T hT f (h₁ _ hY),
    rw [hg, h₃ g hY, comp_zero],
  end, }

instance left_orthogonal_saturated : A.left_orthogonal.saturated :=
⟨λ X Y i hi hX Z f hZ, begin
  haveI := hi,
  have pif := retraction i,
  rw [← cancel_epi (retraction i), comp_zero],
  exact hX _ hZ,
end⟩

lemma left_orthogonal_comp_W_bijective (X : C) (hX : X ∈ A.left_orthogonal.set)
  {Y Z : C} (w : Y ⟶ Z) (hw : A.W w) :
  function.bijective (λ (f : X ⟶ Y), f ≫ w) :=
begin
  rw W_eq_W' at hw,
  obtain ⟨U, f, g, H, mem⟩ := hw,
  split,
  { intros y₁ y₂ hy,
    let y := y₁ - y₂,
    suffices : y = 0,
    { rw ← sub_eq_zero,
      exact this, },
    dsimp at hy,
    obtain ⟨u, hu⟩ := covariant_yoneda_exact₂ _ H y
      (by { dsimp [y], rw [sub_comp, hy, sub_self], }),
    rw [hu, hX u mem, zero_comp], },
  { intro z,
    obtain ⟨y, hy⟩ := covariant_yoneda_exact₃ _ H z (hX _ (A.shift _ 1 mem)),
    exact ⟨y, hy.symm⟩, },
end

lemma left_orthogonal_bijective_L_map [is_triangulated C] {D : Type*} [category D]
  (L : C ⥤ D) [L.is_localization A.W] (X Y : C) (hX : X ∈ A.left_orthogonal.set) :
  function.bijective (λ (f : X ⟶ Y), L.map f) :=
begin
  split,
  { intros f₁ f₂ hf,
    dsimp at hf,
    rw left_calculus_of_fractions.L_map_eq_iff L A.W at hf,
    rcases hf with ⟨Z, s, hs, eq⟩,
    exact (A.left_orthogonal_comp_W_bijective _ hX s hs).1 eq, },
  { intro g,
    obtain ⟨z, hz⟩ := left_calculus_of_fractions.L_map_fac L A.W g,
    dsimp [left_calculus_of_fractions.map_roof] at hz,
    obtain ⟨f, hf⟩ := (A.left_orthogonal_comp_W_bijective _ hX z.s z.hs).2 z.f,
    refine ⟨f, _⟩,
    dsimp at hf ⊢,
    rw [hz, ← hf, L.map_comp, assoc, is_iso.hom_inv_id, comp_id], },
end

lemma left_orthogonal_bijective_Q_map [is_triangulated C] (X Y : C) (hX : X ∈ A.left_orthogonal.set) :
  function.bijective (λ (f : X ⟶ Y), A.Q.map f) :=
A.left_orthogonal_bijective_L_map A.W.Q _ _ hX

end subcategory

end triangulated

end category_theory
