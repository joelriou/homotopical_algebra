import category_theory.lifting_properties.basic
import category_theory.limits.shapes.comm_sq
import for_mathlib.category_theory.morphism_property_misc

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C : Type*} [category C]
namespace comm_sq.lift_struct
attribute [reassoc] fac_left
attribute [reassoc] fac_right
end comm_sq.lift_struct

namespace is_pullback

/-

A     X'     X


B     Y'     Y
-/

section

variables {A B X Y Z : C}
  {i : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
  (h : is_pullback f' i p f) (f₁ : Z ⟶ X) (f₂ : Z ⟶ B)
  (fac : f₁ ≫ p = f₂ ≫ f)

def lift : Z ⟶ A := (pullback_cone.is_limit.lift' h.is_limit f₁ f₂ fac).1

@[simp, reassoc]
lemma lift_fst : h.lift f₁ f₂ fac ≫ f' = f₁ :=
(pullback_cone.is_limit.lift' h.is_limit f₁ f₂ fac).2.1

@[simp, reassoc]
lemma lift_snd : h.lift f₁ f₂ fac ≫ i = f₂ :=
(pullback_cone.is_limit.lift' h.is_limit f₁ f₂ fac).2.2

include h
def hom_ext {l₁ l₂ : Z ⟶ A} (h₁ : l₁ ≫ f' = l₂ ≫ f')
  (h₂ : l₁ ≫ i = l₂ ≫ i) : l₁ = l₂ :=
pullback_cone.is_limit.hom_ext h.is_limit h₁ h₂

end


section

variables
{A B X X' Y Y' : C}
  {i : A ⟶ B} {f : B ⟶ Y'} {f' : A ⟶ X'}
  {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
  {fg : B ⟶ Y} {fg' : A ⟶ X}
  (sq₂ : is_pullback g' p' p g) (sq₁ : comm_sq f' i p' f)
  (sq₁₂ : comm_sq fg' i p fg)
  (hfg : fg = f ≫ g) (hfg' : fg' = f' ≫ g')

include hfg hfg'

def lift_struct_equiv : sq₁.lift_struct ≃ sq₁₂.lift_struct :=
{ to_fun := λ l,
  { l := l.l ≫ g',
    fac_left' := by rw [hfg', l.fac_left_assoc],
    fac_right' := by rw [assoc, sq₂.w, l.fac_right_assoc, hfg], },
  inv_fun := λ l,
  { l := sq₂.lift l.l f (by rw [l.fac_right, hfg]),
    fac_left' := sq₂.hom_ext (by rw [assoc, lift_fst, l.fac_left, hfg'])
      (by rw [assoc, lift_snd, sq₁.w]),
    fac_right' := by rw [lift_snd], },
  left_inv := λ l, by { ext, exact sq₂.hom_ext (by rw lift_fst) (by rw [lift_snd, l.fac_right]), },
  right_inv := λ l, by { ext, simp only [lift_fst], }, }

include sq₂
def has_lift_iff : sq₁.has_lift ↔ sq₁₂.has_lift :=
begin
  split,
  { intro h₁,
    exact comm_sq.has_lift.mk'
      ((sq₂.lift_struct_equiv sq₁ sq₁₂ hfg hfg').to_fun h₁.exists_lift.some), },
  { intro h₁₂,
    exact comm_sq.has_lift.mk'
      ((sq₂.lift_struct_equiv sq₁ sq₁₂ hfg hfg').inv_fun h₁₂.exists_lift.some), },
end

end

lemma has_lifting_property_imp {A B X Y X' Y' : C} {p : X ⟶ Y} {p' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq₂ : is_pullback g' p' p g) (i : A ⟶ B)
  (hip : has_lifting_property i p) : has_lifting_property i p' :=
⟨λ f' f sq₁, begin
  have sq₁₂ : comm_sq (f' ≫ g') i p (f ≫ g) := comm_sq.mk (by rw [assoc, sq₂.w, sq₁.w_assoc]),
  rw sq₂.has_lift_iff sq₁ sq₁₂ rfl rfl,
  haveI := hip,
  apply_instance,
end⟩

end is_pullback


namespace is_pushout

lemma has_lifting_property_imp {A B A' B' X Y : C} {f : A ⟶ A'} {i : A ⟶ B}
  {f' : B ⟶ B'} {i' : A' ⟶ B'} (sq₁ : is_pushout f i i' f') (p : X ⟶ Y)
  (hip : has_lifting_property i p) : has_lifting_property i' p :=
sorry

end is_pushout

end category_theory
