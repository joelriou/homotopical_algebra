import for_mathlib.category_theory.localization.derived_functor
import for_mathlib.category_theory.localization.triangulated
import for_mathlib.category_theory.triangulated.pretriangulated_misc
import for_mathlib.category_theory.triangulated.shift_triangle
import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.category_theory.preadditive_subcategory
import for_mathlib.category_theory.triangulated.coproducts
import for_mathlib.category_theory.limits.products
import for_mathlib.category_theory.triangulated.is_triangulated_subcategory
import category_theory.limits.full_subcategory
import data.int.order.units

noncomputable theory

universes v₁ v₂ u₁ u₂

open_locale zero_object

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

/-structure subcategory :=
(set : set C)
(zero : (0 : C) ∈ set)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ set), (shift_functor C n).obj X ∈ set)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ set) (h₃ : T.obj₃ ∈ set), T.obj₂ ∈ set)-/

variable {C}

namespace subcategory

variables (S : set C) [is_triangulated_subcategory S]

def W : morphism_property C :=
λ X Y f, ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor C (1 : ℤ)).obj X)
  (H : triangle.mk f g h ∈ dist_triang C), Z ∈ S

def W' : morphism_property C :=
λ Y Z g, ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧) (H : triangle.mk f g h ∈ dist_triang C),
    X ∈ S

variable {S}

def W.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₃ ∈ S) :
  (W S) T.mor₁ :=
⟨T.obj₃, T.mor₂, T.mor₃, (by { cases T, exact hT, }), h⟩

def W'.mk {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₁ ∈ S) :
  (W' S) T.mor₂ :=
⟨T.obj₁, T.mor₁, T.mor₃, (by { cases T, exact hT, }), h⟩

def W.triangle {X Y : C} (f : X ⟶ Y) (hf : (W S) f) : triangle C :=
triangle.mk f hf.some_spec.some hf.some_spec.some_spec.some

lemma W.triangle_distinguished {X Y : C} (f : X ⟶ Y) (hf : (W S) f) :
  W.triangle f hf ∈ dist_triang C := hf.some_spec.some_spec.some_spec.some

lemma W.triangle_obj₃_mem {X Y : C} (f : X ⟶ Y) (hf : (W S) f) :
  (W.triangle f hf).obj₃ ∈ S :=
hf.some_spec.some_spec.some_spec.some_spec

variable (S)

lemma W_eq_W' : W S = W' S :=
begin
  ext X Y f,
  split,
  { rintro ⟨Z, g, h, H, mem⟩,
    exact ⟨_, _, _, inv_rot_of_dist_triangle C _ H,
      is_triangulated_subcategory.shift _ _ mem⟩, },
  { rintro ⟨Z, g, h, H, mem⟩,
    refine ⟨_, _, _, rot_of_dist_triangle C _ H,
      is_triangulated_subcategory.shift _ _ mem⟩, },
end

variable {S}

def W.mk' {T : triangle C} (hT : T ∈ dist_triang C) (h : T.obj₁ ∈ S) :
  (W S) T.mor₂ :=
by simpa only [W_eq_W'] using W'.mk hT h

instance W_contains_identities : (W S).contains_identities :=
⟨λ X, ⟨0, 0, 0, pretriangulated.contractible_distinguished X,
  is_triangulated_subcategory.zero S⟩⟩

variable (S)

lemma W_stable_under_composition [is_triangulated C] : (W S).stable_under_composition :=
λ X₁ X₂ X₃ u₁₂ u₂₃ h₁₂ h₂₃,
begin
  rcases h₁₂ with ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩,
  rcases h₂₃ with ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩,
  rcases pretriangulated.distinguished_cocone_triangle _ _ (u₁₂ ≫ u₂₃) with ⟨Z₁₃, v₁₃, w₁₃, H₁₃⟩,
  refine ⟨_, _, _, H₁₃, _⟩,
  exact is_triangulated_subcategory.ext₂ _
    (is_triangulated.octahedron_axiom rfl H₁₂ H₂₃ H₁₃).some.mem mem₁₂ mem₂₃,
end

instance W_multiplicative [is_triangulated C] : (W S).multiplicative :=
{ contains_identities := infer_instance,
  comp := W_stable_under_composition S, }

lemma W_respects_iso : (W S).respects_iso :=
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

instance [is_triangulated C] : left_calculus_of_fractions (W S) :=
{ id := infer_instance,
  comp := W_stable_under_composition S,
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
    { exact ⟨_, _, _, rot_of_dist_triangle C _ mem',
        is_triangulated_subcategory.shift _ _ mem⟩, },
    { rw [← sub_eq_zero, ← sub_comp],
      change f ≫ r = 0,
      have eq := comp_dist_triangle_mor_zero₁₂ C _ mem',
      dsimp at eq,
      rw [hq, assoc, eq, comp_zero], },
  end, }

instance [is_triangulated C] : right_calculus_of_fractions (W S) :=
{ id := infer_instance,
  comp := W_stable_under_composition S,
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
  (W S) ((↑((-1 : units ℤ) ^ n) : ℤ) • f) ↔ (W S) f :=
(W_respects_iso S).arrow_mk_iso_iff
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

instance W_compatible_with_shift : (W S).compatible_with_shift ℤ :=
⟨begin
  have h : ∀ (X Y : C) (f : X ⟶ Y) (hf : (W S) f) (n : ℤ), (W S) (f⟦n⟧'),
  { rintro X Y f ⟨Z, g, h, H, mem⟩ n,
    rw ← mul_mem_W_iff S _ n,
    exact ⟨_, _, _, triangle.shift_distinguished C _ H n,
      is_triangulated_subcategory.shift Z n mem⟩, },
  intro n,
  ext X Y f,
  refine ⟨λ hf, _, λ hf, h _ _ f hf n⟩,
   exact ((W_respects_iso S).arrow_mk_iso_iff
    ((functor.map_arrow_nat_iso_of_nat_iso
    (shift_functor_comp_shift_functor_neg C n)).app (arrow.mk f))).mp (h _ _ _ hf (-n)),
end⟩

variable {S}

lemma W.shift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : (W S) f) (n : ℤ) :
  (W S) ((shift_functor C n).map f) :=
by simpa only [(morphism_property.compatible_with_shift.iff (W S) f n)] using hf

lemma W.unshift {X₁ X₂ : C} {f : X₁ ⟶ X₂} (n : ℤ) (hf : (W S) ((shift_functor C n).map f)) :
  (W S) f :=
by simpa only [← (morphism_property.compatible_with_shift.iff (W S) f n)] using hf

variable (S)

lemma binary_product_stable (X₁ X₂ : C) (hX₁ : X₁ ∈ S)
  (hX₂ : X₂ ∈ S) : (X₁ ⨯ X₂) ∈ S :=
is_triangulated_subcategory.ext₂ _ (binary_product_triangle_distinguished X₁ X₂) hX₁ hX₂

lemma pi_finite_stable {J : Type} [finite J]
  (X : J → C) (hX : ∀ j, X j ∈ S) : (∏ X) ∈ S :=
begin
  revert hX X,
  let P : Type → Prop := λ J,
    ∀ [hJ : finite J] (X : J → C) (hX : ∀ j, X j ∈ S),
      by { haveI := hJ, exact (∏ X) ∈ S, },
  suffices : P J,
  { exact this, },
  refine finite.induction_empty_option _ _ _ J,
  { intros J₁ J₂ e hJ₁, introI, intros X hX,
    haveI : finite J₁ := finite.of_equiv _ e.symm,
    haveI := has_product_of_equiv X e,
    exact set.respects_iso.condition S (product_iso_of_equiv X e)
      (hJ₁ (X ∘ e) (λ j₁, hX _)), },
  { introI, intros X hX,
    refine set.respects_iso.condition S  _ (is_triangulated_subcategory.zero S),
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
      (binary_product_stable S _ _ (hJ (λ j, X (some j)) (λ j, hX _)) (hX none)), },
end

instance W_stable_under_finite_products : (W S).stable_under_finite_products :=
⟨λ J, begin
  introI,
  refine morphism_property.stable_under_products_of_shape.mk _ _ (W_respects_iso S) _,
  intros X₁ X₂ f hf,
  let T := λ j, W.triangle _ (hf j),
  exact W.mk (triangle.product_distinghished T (λ j, W.triangle_distinguished _ (hf j)))
    (pi_finite_stable S (λ j, (T j).obj₃) (λ j, W.triangle_obj₃_mem _ (hf j))),
end⟩

instance W_compatible_with_triangulation [is_triangulated C] :
  (W S).compatible_with_triangulation :=
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
  have hφ₁₂ : (W S) φ₁₂.hom₃ := W.mk H.mem mem₄',
  rcases ha with ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩,
  let H' := (is_triangulated.octahedron_axiom comm.symm mem₅ mem₃ mem₂).some,
  let φ₂₃ : T'₂ ⟶ T'₃ := H'.triangle_morphism₂,
  have hφ₂₃ : (W S) φ₂₃.hom₃ := W.mk' H'.mem mem₅',
  refine ⟨(φ₁₂ ≫ φ₂₃).hom₃, W_stable_under_composition S _ _ hφ₁₂ hφ₂₃, ⟨_, _⟩⟩,
  { have h := (φ₁₂ ≫ φ₂₃).comm₂,
    dsimp at h,
    simpa only [comp_id] using h, },
  { have h := (φ₁₂ ≫ φ₂₃).comm₃,
    dsimp at h,
    simpa only [triangle_category_comp, triangle_morphism.comp_hom₃, id_comp] using h, },
end⟩


instance W_is_saturated [saturated S] [is_triangulated C] : (W S).is_saturated :=
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
  have hs : (W S) s := W.mk (rot_of_dist_triangle _ _
    (rot_of_dist_triangle _ _ H₁₂₃.mem)) (set.is_stable_by_shift.condition 1 _ mem₁₃),
  have ht : (W S) t := W.mk (rot_of_dist_triangle _ _
    (rot_of_dist_triangle _ _ H₂₃₄.mem)) (set.is_stable_by_shift.condition 1 _ mem₂₄),
  let st := t ≫ s⟦1⟧',
  have hst : st = 0,
  { dsimp [st],
    have eq : g₂₃ ≫ h₂₃ = 0 := triangle.comp_zero₂₃ _ H₂₃,
    simp only [assoc, ← functor.map_comp, reassoc_of eq,
      zero_comp, functor.map_zero, comp_zero], },
  have hst' := W_stable_under_composition S t (s⟦1⟧') ht (hs.shift 1),
  obtain ⟨Z, g, h, H, mem⟩ := hst',
  let i := (triangle.mk (t ≫ (shift_functor C 1).map s) g h).mor₂,
  haveI : mono i := mono_of_dist_triang₂ _ H hst,
  haveI : is_split_mono i := is_split_mono_of_mono i,
  have mem₁₂ := saturated.condition i mem,
  dsimp [triangle.mk] at mem₁₂,
  rw [← is_triangulated_subcategory.shift_iff, ← is_triangulated_subcategory.shift_iff] at mem₁₂,
  exact is_triangulated_subcategory.ext₃ _ H₁₂₃.mem mem₁₂ mem₁₃,
end⟩

lemma category_closed_under_finite_products (J : Type) [finite J] :
  closed_under_limits_of_shape (discrete J) S :=
λ F c hc mem, begin
  let X := λ j, F.obj ⟨j⟩,
  refine set.respects_iso.condition S _ (pi_finite_stable S X (λ j, mem ⟨j⟩)),
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

--instance category_has_finite_products : has_finite_products (full_subcategory S) :=
--infer_instance

--instance shift_functor_additive (n : ℤ) : (shift_functor (full_subcategory S) n).additive :=
--  infer_instance

--instance full_subcategory_inclusion_has_comm_shift :
--  A.inclusion.has_comm_shift ℤ := infer_instance

--instance category_inclusion_additive : A.inclusion.additive := infer_instance

--instance : pretriangulated (full_subcategory S) := infer_instance

lemma dist_triang_iff {X Y Z : full_subcategory S} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) :
  (triangle.mk f g h ∈ dist_triang (full_subcategory S)) ↔
    (@triangle.mk C _ _ _ _ _ f g h ∈ dist_triang C) :=
begin
  change (_ ∈ dist_triang C) ↔ _,
  let e : (full_subcategory_inclusion S).map_triangle.obj (triangle.mk f g h) ≅
    @triangle.mk C _ _ _ _ _ f g h,
  { refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
    dsimp,
    erw [id_comp, functor.map_id, comp_id, comp_id], },
  split,
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e.symm, },
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e, },
end

instance is_triangulated_full_subcategory [is_triangulated C] :
  is_triangulated (full_subcategory S) := infer_instance

--instance inclusion_is_triangulated : (full_subcategory_inclusion S).is_triangulated :=
--infer_instance


def Q [is_triangulated C] : C ⥤ (W S).localization :=
begin
  let F := localization_functor (W S).Q (W S),
  exact F,
end

instance Q_has_comm_shift [is_triangulated C] : (Q S).has_comm_shift ℤ :=
(infer_instance : (localization_functor (W S).Q (W S)).has_comm_shift ℤ)

instance Q_is_triangulated [is_triangulated C] : (Q S).is_triangulated :=
(infer_instance : (localization_functor (W S).Q (W S)).is_triangulated)


/- TODO :
1) show a universal property for the triangulated functor `L` : if
`G : D ⥤ E` is a functor which lifts a triangulated functor `F : C ⥤ E`
then `G` is a triangulated functor.
 -/

instance Q_to_functor_is_localization [is_triangulated C] : (Q S).is_localization (W S) :=
(infer_instance : (W S).Q.is_localization (W S))

lemma is_iso_map_iff [saturated S] [is_triangulated C] {D : Type*} [category D] (L : C ⥤ D)
  [L.is_localization (W S)] {X Y : C} (f : X ⟶ Y) : is_iso (L.map f) ↔ (W S) f :=
localization.is_iso_map_iff_of_calculus_of_fractions L (W S) f

lemma is_zero_obj_iff' [is_triangulated C] (X : C) :
  is_zero ((Q S).obj X) ↔ ∃ (Y : C) (i : X ⟶ Y) [is_split_mono i], Y ∈ S :=
begin
  rw limits.is_zero.iff_id_eq_zero,
  split,
  { intro h,
    have h' : (W S).Q.map (𝟙 X) = (W S).Q.map 0 :=
      by simpa only [functor.map_id, functor.map_zero] using h,
    rw right_calculus_of_fractions.L_map_eq_iff (W S).Q (W S) at h',
    obtain ⟨Z, s, hs, eq⟩ := h',
    rw [comp_id, comp_zero] at eq,
    obtain ⟨Y, i, p, H, mem⟩ := hs,
    haveI : mono i := mono_of_dist_triang₂ _ H eq,
    exact ⟨Y, i, is_split_mono_of_mono i, mem⟩, },
  { rintro ⟨Y, i, hi, mem⟩,
    haveI : is_iso ((W S).Q.map (0 : Y ⟶ 0)) := localization.inverts (W S).Q (W S) _
      (W.mk' (contractible_distinguished Y) mem),
    rw [← cancel_mono ((W S).Q.map i), id_comp, zero_comp,
      ← cancel_mono ((W S).Q.map (0 : Y ⟶ 0)), functor.map_zero, comp_zero, comp_zero], },
end

lemma is_zero_obj_iff [saturated S] [is_triangulated C] (X : C) :
  is_zero ((Q S).obj X) ↔ X ∈ S :=
begin
  rw is_zero_obj_iff',
  split,
  { intro h,
    obtain ⟨Y, i, hi, mem⟩ := h,
    haveI := hi,
    exact saturated.condition i mem, },
  { exact λ h, ⟨X, 𝟙 X, infer_instance, h⟩, },
end

lemma left_orthogonal_comp_W_bijective (X : C) (hX : X ∈ left_orthogonal S)
  {Y Z : C} (w : Y ⟶ Z) (hw : (W S) w) :
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
    obtain ⟨y, hy⟩ := covariant_yoneda_exact₃ _ H z
      (hX _ (is_triangulated_subcategory.shift _ _ mem)),
    exact ⟨y, hy.symm⟩, },
end

lemma left_orthogonal_bijective_L_map [is_triangulated C] {D : Type*} [category D]
  (L : C ⥤ D) [L.is_localization (W S)] (X Y : C) (hX : X ∈ left_orthogonal S) :
  function.bijective (λ (f : X ⟶ Y), L.map f) :=
begin
  split,
  { intros f₁ f₂ hf,
    dsimp at hf,
    rw left_calculus_of_fractions.L_map_eq_iff L (W S) at hf,
    rcases hf with ⟨Z, s, hs, eq⟩,
    exact (left_orthogonal_comp_W_bijective S _ hX s hs).1 eq, },
  { intro g,
    obtain ⟨z, hz⟩ := left_calculus_of_fractions.L_map_fac L (W S) g,
    dsimp [left_calculus_of_fractions.map_roof] at hz,
    obtain ⟨f, hf⟩ := (left_orthogonal_comp_W_bijective S _ hX z.s z.hs).2 z.f,
    refine ⟨f, _⟩,
    dsimp at hf ⊢,
    rw [hz, ← hf, L.map_comp, assoc, is_iso.hom_inv_id, comp_id], },
end

lemma left_orthogonal_bijective_Q_map [is_triangulated C]
  (X Y : C) (hX : X ∈ left_orthogonal S) :
  function.bijective (λ (f : X ⟶ Y), (Q S).map f) :=
left_orthogonal_bijective_L_map S (Q S) _ _ hX

lemma right_orthogonal_comp_W_bijective (Z : C) (hZ : Z ∈ right_orthogonal S)
  {X Y : C} (w : X ⟶ Y) (hw : (W S) w) :
  function.bijective (λ (f : Y ⟶ Z), w ≫ f) :=
begin
  split,
  { intros y₁ y₂ hy,
    let y := y₁ - y₂,
    suffices : y = 0,
    { rw ← sub_eq_zero,
      exact this, },
    dsimp at hy,
    obtain ⟨U, f, g, H, mem⟩ := hw,
    obtain ⟨u, hu⟩ := contravariant_yoneda_exact₂ _ H y
      (by { dsimp [y], rw [comp_sub, hy, sub_self], }),
    rw [hu, hZ u mem, comp_zero], },
  { intro z,
    rw W_eq_W' at hw,
    obtain ⟨U, f, g, H, mem⟩ := hw,
    obtain ⟨y, hy⟩ := contravariant_yoneda_exact₂ _ H z (hZ _ mem),
    exact ⟨y, hy.symm⟩, },
end

lemma right_orthogonal_bijective_L_map [is_triangulated C] {D : Type*} [category D]
  (L : C ⥤ D) [L.is_localization (W S)] (X Y : C) (hY : Y ∈ right_orthogonal S) :
  function.bijective (λ (f : X ⟶ Y), L.map f) :=
begin
  split,
  { intros f₁ f₂ hf,
    dsimp at hf,
    rw right_calculus_of_fractions.L_map_eq_iff L (W S) at hf,
    rcases hf with ⟨Z, s, hs, eq⟩,
    exact (right_orthogonal_comp_W_bijective S _ hY s hs).1 eq, },
  { intro g,
    obtain ⟨z, hz⟩ := right_calculus_of_fractions.L_map_fac L (W S) g,
    dsimp [right_calculus_of_fractions.map_roof] at hz,
    obtain ⟨f, hf⟩ := (right_orthogonal_comp_W_bijective S _ hY z.s z.hs).2 z.f,
    refine ⟨f, _⟩,
    dsimp at hf ⊢,
    rw [hz, ← hf, L.map_comp, is_iso.inv_hom_id_assoc], },
end

lemma right_orthogonal_bijective_Q_map
  [is_triangulated C] (X Y : C) (hY : Y ∈ right_orthogonal S) :
  function.bijective (λ (f : X ⟶ Y), (Q S).map f) :=
right_orthogonal_bijective_L_map S (Q S) _ _ hY

end subcategory

end triangulated

end category_theory
