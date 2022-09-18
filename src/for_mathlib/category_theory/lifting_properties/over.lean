import category_theory.lifting_properties.basic
import category_theory.over

namespace category_theory

open category

variables {C : Type*} [category C] {M : C} {A B X Y : under M}
  {i : A ⟶ B} {p : X ⟶ Y} {f : A ⟶ X} {g : B ⟶ Y}
  (sq : comm_sq f i p g)

namespace comm_sq

def lift_struct.map {D : Type*} [category D] (F : C ⥤ D)
  {A B X Y : C} {i : A ⟶ B} {p : X ⟶ Y} {f : A ⟶ X} {g : B ⟶ Y}
  {sq : comm_sq f i p g} (l : sq.lift_struct) : (F.map_comm_sq sq).lift_struct :=
{ l := F.map l.l,
  fac_left' := by { rw [← F.map_comp, l.fac_left], },
  fac_right' := by { rw [← F.map_comp, l.fac_right], }, }

variable (sq)

def under_forget_equiv_lift_struct :
  sq.lift_struct ≃ ((under.forget M).map_comm_sq sq).lift_struct :=
{ to_fun := lift_struct.map (under.forget M),
  inv_fun := λ l,
  { l := structured_arrow.hom_mk l.l begin
      simp only [functor.id_map],
      have w₁ := f.w,
      have w₂ := i.w,
      dsimp at w₁ w₂,
      rw [id_comp] at w₁ w₂,
      have h := l.fac_left,
      dsimp at h,
      rw [w₂, assoc, h, w₁],
    end,
    fac_left' := by { ext, exact l.fac_left, },
    fac_right' := by { ext, exact l.fac_right, }, },
  left_inv := by tidy,
  right_inv := by tidy, }

lemma under_sq_has_lift_iff :
  sq.has_lift ↔ ((under.forget M).map_comm_sq sq).has_lift :=
by simpa only [comm_sq.has_lift.iff] using nonempty.congr
    (under_forget_equiv_lift_struct sq).to_fun (under_forget_equiv_lift_struct sq).inv_fun

end comm_sq

variables (i p)

instance has_lifting_property_under
  [has_lifting_property ((under.forget M).map i) ((under.forget M).map p)] :
  has_lifting_property i p :=
⟨λ f g sq, by { rw comm_sq.under_sq_has_lift_iff, apply_instance, }⟩

end category_theory
