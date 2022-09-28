import for_mathlib.category_theory.localization.preadditive
import category_theory.triangulated.basic

noncomputable theory

namespace category_theory

open category

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

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal

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
    associativity := sorry,
    left_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, nat_trans.hcomp_id_app,
      iso.refl_hom] using congr_app (left_unitality a) X,
    right_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, iso.refl_hom,
      nat_trans.id_hcomp_app] using congr_app (right_unitality a) X, },
end

end shift

end category_theory
