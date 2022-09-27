import for_mathlib.category_theory.localization.preadditive
import category_theory.triangulated.basic

noncomputable theory

namespace category_theory

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
  letI : localization.lifting L W (shift_functor C (0 : A) ⋙ L) (𝟭 D) :=
    ⟨iso_whisker_right (shift_functor_zero C A).symm L⟩,
  let F := λ (a : A), localization.lift (shift_functor C a ⋙ L)
    (shift.comp_localization_inverts L W a) L,
  let H : Π (a : A), Comm_sq (shift_functor C a) L L (F a) :=
    λ a, ⟨localization.lifting.iso L W (shift_functor C a ⋙ L) (F a)⟩,
  let ε : 𝟭 D ≅ F 0 := localization.lifting.uniq L W (shift_functor C (0 : A) ⋙ L) _ _,
  let μ : Π (a₁ a₂ : A), F a₁ ⋙ F a₂ ≅ F (a₁ + a₂) := λ a₁ a₂,
    localization.lifting_comp_iso (H a₁) (H a₂) (H (a₁+a₂))
      (shift_functor_add C a₁ a₂).symm W W W,
  have left_unitality : ∀ (a : A), nat_iso.hcomp ε (iso.refl (F a)) ≪≫ μ 0 a =
    eq_to_iso (by simpa only [zero_add]),
  { sorry, },
  exact has_shift_mk D A
  { F := F,
    ε := ε,
    μ := μ,
    associativity := sorry,
    left_unitality := λ a X, begin
      have h := congr_arg (λ (e : _ ≅ _), e.hom) (left_unitality a),
      simpa only [iso.trans_hom, nat_trans.comp_app, eq_to_iso.hom, eq_to_hom_app,
        nat_iso.hcomp, nat_trans.hcomp_id_app, iso.refl_hom] using congr_app h X,
    end,
    right_unitality := sorry, },
end

end shift

end category_theory
