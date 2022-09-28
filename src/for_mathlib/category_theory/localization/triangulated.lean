import for_mathlib.category_theory.localization.preadditive
import category_theory.triangulated.pretriangulated
import for_mathlib.category_theory.localization.calculus_of_fractions

noncomputable theory

namespace category_theory

open category limits

class morphism_property.compatible_with_shift {C : Type*} [category C]
  (W : morphism_property C) (A : Type*) [add_monoid A] [has_shift C A] : Prop :=
(translate : ∀ (a : A), W.inverse_image (shift_functor C a) = W)

lemma morphism_property.compatible_with_shift.iff {C : Type*} [category C]
  (W : morphism_property C) {A : Type*} [add_monoid A] [has_shift C A]
  [h : W.compatible_with_shift A]
  {X Y : C} (f : X ⟶ Y) (a : A) : W ((shift_functor C a).map f) ↔ W f :=
by { conv_rhs { rw ← h.translate a }, refl, }

namespace shift

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  {A : Type*} [add_monoid A] [has_shift C A] [W.compatible_with_shift A]

variable (C)

local attribute [reducible] discrete.add_monoidal

variable {C}

include L W

lemma comp_localization_inverts (a : A) : W.is_inverted_by (shift_functor C a ⋙ L) :=
λ X Y f hf,
begin
  dsimp,
  rw ← morphism_property.compatible_with_shift.iff W f a at hf,
  exact localization.inverts L W _ hf,
end

variable (A)

def localization : has_shift D A :=
begin
  let F := λ (a : A), localization.lift (shift_functor C a ⋙ L)
    (shift.comp_localization_inverts L W a) L,
  let H : Π (a : A), Comm_sq (shift_functor C a) L L (F a) :=
    λ a, ⟨localization.lifting.iso L W (shift_functor C a ⋙ L) (F a)⟩,
  let H₀ : Comm_sq (𝟭 C) L L (𝟭 D) := Comm_sq.horiz_refl L,
  let ε : 𝟭 D ≅ F 0 := localization.lift_nat_iso' H₀ (H 0) W (shift_functor_zero C A).symm,
  let μ : Π (a₁ a₂ : A), F a₁ ⋙ F a₂ ≅ F (a₁ + a₂) := λ a₁ a₂,
    localization.lifting_comp_iso (H a₁) (H a₂) (H (a₁+a₂))
      (shift_functor_add C a₁ a₂).symm W W,
  let e : Π {a₁ a₂ : A} (h : a₁ = a₂), shift_functor C a₁ ≅ shift_functor C a₂ :=
    λ a₁ a₂ h, eq_to_iso (by rw h),
  have Heq : Π {a b : A} (h : a = b) (X : C), (H a).iso.inv.app X = eq_to_hom (by rw h) ≫ (H b).iso.inv.app X ≫ eq_to_hom (by rw h),
  { intros a b h X,
    subst h,
    simp only [eq_to_hom_refl, id_comp, comp_id], },
  have associativity : ∀ (a₁ a₂ a₃ : A),
    eq_to_hom (by rw functor.assoc) ≫ (μ a₁ a₂).hom ◫ 𝟙 (F a₃) ≫ (μ (a₁ + a₂) a₃).hom ≫ eq_to_hom (congr_arg F (add_assoc a₁ a₂ a₃)) =
    𝟙 (F a₁) ◫ (μ a₂ a₃).hom ≫ (μ a₁ (a₂ + a₃)).hom,
  { intros a₁ a₂ a₃,
    dsimp only [μ],
    simp only [eq_to_hom_refl, id_comp, ← localization.lift_nat_trans'_id (H a₃) W,
      ← localization.lift_nat_trans'_id (H a₁) W, localization.lifting_comp_iso_hom,
      localization.hcomp_lift_nat_trans', localization.comp_lift_nat_trans', localization.comp_lift_nat_trans'_assoc],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    have this : (shift_functor_add C a₁ a₂).symm.hom ◫ 𝟙 (shift_functor C a₃) ≫ (shift_functor_add C (a₁ + a₂) a₃).symm.hom =
      eq_to_hom (functor.assoc _ _ _) ≫ (𝟙 (shift_functor C a₁) ◫ (shift_functor_add C a₂ a₃).symm.hom ≫ (shift_functor_add C a₁ (a₂ + a₃)).symm.hom) ≫
        eq_to_hom (by rw (add_assoc a₁ a₂ a₃)),
    { ext X,
      dsimp,
      simp only [obj_μ_app, eq_to_iso.inv, id_comp, assoc, μ_inv_hom_app, comp_id, functor.map_id, eq_to_hom_app, eq_to_hom_map], },
    simp only [nat_trans.comp_app, eq_to_hom_app, localization.lift_nat_trans'_app,
      localization.lift_nat_trans'_app, Comm_sq.horiz_comp_assoc_iso, assoc, this,
      Heq (add_assoc a₁ a₂ a₃), eq_to_hom_trans, L.map_comp, eq_to_hom_map, eq_to_hom_refl,
      eq_to_hom_trans_assoc, id_comp, comp_id], },
  have left_unitality : ∀ (a : A), ε.hom ◫ 𝟙 (F a) ≫ (μ 0 a).hom =
    eq_to_hom (by simpa only [zero_add]),
  { intro a,
    dsimp [ε, μ],
    rw ← localization.lift_nat_trans'_id (H a) W,
    erw localization.lifting_comp_iso_nat_trans_compatibility H₀ (H a) (H (0 + a)) (H 0) (H a) (H (0 + a))
      ((functor.right_unitor _) ≪≫ e (zero_add a).symm) (shift_functor_add C 0 a).symm W W
      (shift_functor_zero C A).inv (𝟙 _) (𝟙 _) begin
        ext X,
        dsimp,
        simp only [eq_to_hom_map, obj_ε_app, eq_to_iso.inv, eq_to_hom_app, id_comp, assoc,
          μ_inv_hom_app],
      end,
    simp only [localization.lifting_comp_iso_hom, localization.lift_nat_trans'_id, comp_id],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    rw [localization.lift_nat_trans'_app, eq_to_hom_app, Heq (zero_add a), iso.trans_hom,
      nat_trans.comp_app, functor.right_unitor_hom_app, eq_to_iso.hom, eq_to_hom_app],
    erw id_comp,
    simpa only [eq_to_hom_map, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp,
      Comm_sq.refl_horiz_comp_iso, iso.hom_inv_id_app_assoc], },
  have right_unitality : ∀ (a : A), 𝟙 (F a) ◫ ε.hom ≫ (μ a 0).hom =
    eq_to_hom (by simpa only [add_zero]),
  { intro a,
    dsimp only [ε, μ],
    rw ← localization.lift_nat_trans'_id (H a) W,
    rw localization.lift_nat_iso'_hom,
    erw localization.lifting_comp_iso_nat_trans_compatibility (H a) H₀ (H (a + 0)) (H a) (H 0) (H (a + 0))
      ((functor.right_unitor _) ≪≫ e (add_zero a).symm) (shift_functor_add C a 0).symm W W
      (𝟙 _) (shift_functor_zero C A).inv (𝟙 _) begin
        ext X,
        dsimp,
        simp only [ε_app_obj, eq_to_iso.inv, functor.map_id, assoc, comp_id, μ_inv_hom_app, eq_to_hom_app, id_comp,
          eq_to_hom_map],
      end,
    simp only [localization.lifting_comp_iso_hom, localization.lift_nat_trans'_id, comp_id],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    rw [localization.lift_nat_trans'_app, eq_to_hom_app, Heq (add_zero a), iso.trans_hom,
      nat_trans.comp_app, functor.right_unitor_hom_app, eq_to_iso.hom, eq_to_hom_app],
    erw id_comp,
    simpa only [eq_to_hom_map, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp,
      Comm_sq.horiz_comp_refl_iso, iso.hom_inv_id_app_assoc], },
  exact has_shift_mk D A
  { F := F,
    ε := ε,
    μ := μ,
    associativity := λ a₁ a₂ a₃ X, begin
      have h := congr_app (associativity a₁ a₂ a₃) X,
      simp only [nat_trans.comp_app, nat_trans.hcomp_app, eq_to_hom_app, eq_to_hom_refl,
        nat_trans.id_app, id_comp, functor.map_id, comp_id] at h,
      erw id_comp at h,
      exact h,
    end,
    left_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, nat_trans.hcomp_id_app,
      iso.refl_hom] using congr_app (left_unitality a) X,
    right_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, iso.refl_hom,
      nat_trans.id_hcomp_app] using congr_app (right_unitality a) X, },
end

variable {A}

@[simp]
def localization_comm_shift (a : A) :
  shift_functor C a ⋙ L ≅ L ⋙ @shift_functor D A _ _ (shift.localization L W A) a :=
(localization.fac _ _ _).symm

/- show that the localized shift functors are additive if `A` is an add_comm_group
  and D has finite products: this is because these functors are equivalences of categories. -/

end shift

namespace triangulated

open pretriangulated

section

variables (C : Type*) [category C] [has_shift C ℤ] [has_zero_object C] [has_zero_morphisms C]

@[simps]
def contractible_triangle_functor : C ⥤ triangle C :=
{ obj := λ X, contractible_triangle C X,
  map := λ X Y f,
  { hom₁ := f,
    hom₂ := f,
    hom₃ := 0, }, }

variable {C}

def triangle.mk_iso (T T' : triangle C) (e₁ : T.obj₁ ≅ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂)
  (e₃ : T.obj₃ ≅ T'.obj₃)
  (comm₁ : T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁)
  (comm₂ : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
  (comm₃ : T.mor₃ ≫ (shift_functor C 1).map e₁.hom = e₃.hom ≫ T'.mor₃) : T ≅ T' :=
{ hom :=
  { hom₁ := e₁.hom,
    hom₂ := e₂.hom,
    hom₃ := e₃.hom,
    comm₁' := comm₁,
    comm₂' := comm₂,
    comm₃' := comm₃, },
  inv :=
  { hom₁ := e₁.inv,
    hom₂ := e₂.inv,
    hom₃ := e₃.inv,
    comm₁' := by rw [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, comp_id, assoc, comm₁, e₁.inv_hom_id_assoc],
    comm₂' := by { rw [← cancel_mono e₃.hom, assoc, e₃.inv_hom_id, comp_id, assoc, comm₂, e₂.inv_hom_id_assoc], },
    comm₃' := by { rw [← cancel_epi e₃.hom, ← assoc, ← comm₃, assoc, ← functor.map_comp, e₁.hom_inv_id, functor.map_id, comp_id, e₃.hom_inv_id_assoc], }, },
  hom_inv_id' := by { ext; apply iso.hom_inv_id, },
  inv_hom_id' := by { ext; apply iso.inv_hom_id, }, }

end


variables {C D : Type*} [category C] [category D]
  [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ n : ℤ, functor.additive (shift_functor C n)] [hC : pretriangulated C]
  [∀ n : ℤ, functor.additive (shift_functor D n)]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  [W.compatible_with_shift ℤ] [functor.additive L]
  (comm_shift : shift_functor C (1 : ℤ) ⋙ L ≅ L ⋙ shift_functor D (1 : ℤ))
  [left_calculus_of_fractions W] [right_calculus_of_fractions W]
--  [hL₂ : functor.additive L]
/- state SM6 -/

include L comm_shift

namespace localization

@[simps]
def functor : triangulated_functor_struct C D :=
{ comm_shift := comm_shift,
  .. L }

include hC
@[simp]
def distinguished_triangles : set (triangle D) :=
λ T, ∃ (T' : triangle C) (e : T ≅ (functor L comm_shift).map_triangle.obj T'), T' ∈ dist_triang C

lemma isomorphic_distinguished {T₁ T₂ : triangle D} (e : T₂ ≅ T₁)
  (h : T₁ ∈ distinguished_triangles L comm_shift) : T₂ ∈ distinguished_triangles L comm_shift :=
by { rcases h with ⟨T', e', hT'⟩, exact ⟨T', e ≪≫ e',  hT'⟩, }

include W

lemma contractible_distinguished (X : D) : contractible_triangle D X ∈ distinguished_triangles L comm_shift :=
begin
  haveI := localization.ess_surj L W,
  let e := ((contractible_triangle_functor D).map_iso
    (L.obj_obj_preimage_iso X)),
  refine ⟨contractible_triangle C (L.obj_preimage X), _, contractible_distinguished _⟩,
  { refine e.symm ≪≫ triangle.mk_iso _ _ (iso.refl _) (iso.refl _) L.map_zero_object.symm _ _ _,
    tidy, },
end

end localization

def localization [pretriangulated C] : pretriangulated D :=
{ distinguished_triangles := localization.distinguished_triangles L comm_shift,
  isomorphic_distinguished := λ T₁ hT₁ T₂ e,
    localization.isomorphic_distinguished L comm_shift e hT₁,
  contractible_distinguished := localization.contractible_distinguished L W comm_shift,
  distinguished_cocone_triangle := sorry,
  rotate_distinguished_triangle := sorry,
  complete_distinguished_triangle_morphism := sorry, }

end triangulated

end category_theory
