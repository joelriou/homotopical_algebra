/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cylinder

noncomputable theory

open category_theory
open category_theory.limits
open category_theory.category
open algebraic_topology

/- for category_theory/quotient.lean -/
namespace category_theory

namespace quotient

lemma functor_map_surj {C : Type*} [category C] (r : hom_rel C) (s t : C) :
  function.surjective (λ (f : s ⟶ t), (functor r).map f) :=
begin
  intro f,
  cases surjective_quot_mk _ f with g hg,
  use [g, hg],
end

end quotient

end category_theory

namespace algebraic_topology

namespace model_category

variables (M : model_category)

@[derive category]
def cofibrant_objects := { X : M.C // nonempty (is_cofibrant X) }

namespace cofibrant_objects

variable {M}

def right_homotopy : hom_rel M.cofibrant_objects := λ A X f₁ f₂,
∃ (P : path_object X.1), nonempty (P.pre.right_homotopy f₁ f₂)

namespace right_homotopy

def symm {A X : M.cofibrant_objects } {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) :
  right_homotopy f₂ f₁ := 
by { cases H with P hP, use P.symm, exact nonempty.intro hP.some.symm, }

lemma comp_left {A B X : M.cofibrant_objects}
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_homotopy g g') :
  right_homotopy (f ≫ g) (f ≫ g') :=
by { cases H with P hP, use P, exact nonempty.intro (hP.some.comp_left f), }

lemma comp_right {A B X : M.cofibrant_objects}
  {f f' : A ⟶ B} {g : B ⟶ X} (H : right_homotopy f f') :
  right_homotopy (f ≫ g) (f' ≫ g) :=
begin
  cases H with P hP,
  rcases M.CM5b (arrow.mk P.pre.σ') with ⟨Z, i, p, fac, ⟨hi, hp⟩⟩,
  let P' := P.change_I' fac hp,
  let H := hP.some,
  let Sq := square.mk'' (initial.to _) p (initial.to _) H.h
    (by { dsimp, apply subsingleton.elim, }),
  have hSq := (M.CM4a Sq.left Sq.right A.2.some.1 hp).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  have hk : l.lift ≫ p = H.h := l.fac_right,
  let H' : P'.pre.right_homotopy f f' :=
  { h := l.lift,
    h₀ := begin
      dsimp [P', pre_path_object.d₀'],
      erw [← assoc, hk, H.h₀],
    end,
    h₁ := begin
      dsimp [P', pre_path_object.d₁'],
      erw [← assoc, hk, H.h₁],
    end, },
  cases path_object_exists X.1 with Q hQ,
  let Sq₂ := square.mk'' P'.pre.σ' Q.pre.π
    (g ≫  Q.pre.σ') (P'.pre.π ≫ (limits.prod.map g g)) _, rotate,
  { ext,
    { dsimp,
      simp only [assoc, prod.lift_fst, prod.lift_map],
      erw [Q.pre.σd₀', ← assoc, P'.pre.σd₀', id_comp, comp_id], },
    { dsimp,
      simp only [assoc, prod.lift_snd, prod.lift_map],
      erw [Q.pre.σd₁', ← assoc, P'.pre.σd₁', id_comp, comp_id], }, },
  let hSq₂ := (M.CM4b Sq₂.left Sq₂.right ⟨hi, P'.pre.Wσ'⟩ Q.fib_π).sq_has_lift,
  let l₂ := (hSq₂ Sq₂.hom).exists_lift.some,
  have eq₀ := congr_arg ((λ (f : _ ⟶ prod X.1 X.1), f ≫ limits.prod.fst)) l₂.fac_right,
  have eq₁ := congr_arg ((λ (f : _ ⟶ prod X.1 X.1), f ≫ limits.prod.snd)) l₂.fac_right,
  simp only [pre_path_object.π, prod.lift_fst, prod.lift_snd, prod.lift_map,
    square.mk''_right_hom, prod.comp_lift, square.mk''_hom_right] at eq₀ eq₁,
  let H'' : Q.pre.right_homotopy (f ≫ g) (f' ≫ g) := 
  { h := H'.h ≫ l₂.lift,
    h₀ := by rw [assoc, eq₀, ← assoc, H'.h₀],
    h₁ := by rw [assoc, eq₁, ← assoc, H'.h₁], },
  use [Q, nonempty.intro H''],
end

end right_homotopy

inductive right_ho_trans_closure {A X : M.cofibrant_objects} : (A ⟶ X) → (A ⟶ X) → Prop
| right_homotopy {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) : right_ho_trans_closure f₁ f₂
| trans {f₁ f₂ f₃ : A ⟶ X} (H₁₂ : right_ho_trans_closure f₁ f₂) (H₂₃ : right_ho_trans_closure f₂ f₃) :
  right_ho_trans_closure f₁ f₃

namespace right_ho_trans_closure

lemma is_equiv (A X : M.cofibrant_objects) : is_equiv (A ⟶ X) right_ho_trans_closure :=
{ refl := λ f, right_homotopy begin
    cases path_object_exists X.1 with P hP,
    use P,
    exact nonempty.intro (pre_path_object.right_homotopy.refl f),
  end,
  trans := λ f₁ f₂ f₃, right_ho_trans_closure.trans,
  symm := λ f g H, begin
    induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₂₁ H₃₂,
    { exact right_homotopy H₁₂.symm, },
    { exact trans H₃₂ H₂₁, }
  end, }

lemma comp_left (A B X : M.cofibrant_objects)
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_ho_trans_closure g g') :
    right_ho_trans_closure (f ≫ g) (f ≫ g') :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy (H₁₂.comp_left f), },
  { exact trans H₁₂' H₂₃', }
end

lemma comp_right (A B X : M.cofibrant_objects)
  (f f' : A ⟶ B) {g : B ⟶ X} (H : right_ho_trans_closure f f') :
    right_ho_trans_closure (f ≫ g) (f' ≫ g) :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy H₁₂.comp_right, },
  { exact trans H₁₂' H₂₃', },
end

variable (M)

@[simp]
def hom_rel : hom_rel M.cofibrant_objects := λ X Y, cofibrant_objects.right_ho_trans_closure

instance : congruence (hom_rel M) :=
{ is_equiv := right_ho_trans_closure.is_equiv,
  comp_left := right_ho_trans_closure.comp_left,
  comp_right := right_ho_trans_closure.comp_right }

end right_ho_trans_closure

variable (M)

@[derive category]
def π := quotient (right_ho_trans_closure.hom_rel M)

@[simps]
def L : M.cofibrant_objects ⥤ cofibrant_objects.π M :=
quotient.functor (right_ho_trans_closure.hom_rel M)

end cofibrant_objects

@[derive category]
def fibrant_and_cofibrant_objects := { X : M.cofibrant_objects // nonempty (is_fibrant X.1) }

namespace fibrant_and_cofibrant_objects

def mk_obj (X : M.C) [h₁ : is_cofibrant X] [h₂ : is_fibrant X] : M.fibrant_and_cofibrant_objects :=
⟨⟨X, nonempty.intro h₁⟩, nonempty.intro h₂⟩

@[derive category]
def Ho := { X : cofibrant_objects.π M // nonempty (is_fibrant X.1.1) }

variable {M}

@[simps]
def L : M.fibrant_and_cofibrant_objects ⥤ fibrant_and_cofibrant_objects.Ho M :=
begin
  let F : M.fibrant_and_cofibrant_objects ⥤ cofibrant_objects.π M :=
    induced_functor _ ⋙ cofibrant_objects.L M,
  exact
  { obj := λ X, ⟨F.obj X, X.2⟩,
    map := λ X Y f, F.map f,
    map_id' := λ X, F.map_id X,
    map_comp' := λ X Y Z f g, F.map_comp f g, }
end

def forget : M.fibrant_and_cofibrant_objects ⥤ M.C := induced_functor _

def L_map_surjective (X Y : M.fibrant_and_cofibrant_objects) :
  function.surjective (λ (f : X ⟶ Y), L.map f) :=
begin
  intro f,
  cases category_theory.quotient.functor_map_surj _ _ _ f with g hg,
  dsimp at g,
  use [g, hg],
end

def L_map_eq_iff {X Y : M.fibrant_and_cofibrant_objects} (C : cylinder X.1.1) (f g : X ⟶ Y) :
  L.map f = L.map g ↔ nonempty (C.to_precylinder.left_homotopy f g) :=
begin
  haveI := X.1.2.some,
  haveI := Y.2.some,
  split,
  { intro h,
    dsimp only [L, functor.comp_map, cofibrant_objects.L] at h,
    erw quotient.functor_map_eq_iff at h,
    dsimp at h,
    induction h with f₀ f₁ Hr f₁ f₂ f₃ H₁₂ H₂₃ H H',
    { cases Hr with P hP,
      apply nonempty.intro,
      exact @cylinder.left_homotopy_of_right_homotopy M X.1.1 Y.1.1 infer_instance C P _ _ hP.some, },
    { apply nonempty.intro,
      exact C.left_homotopy_from_other_cylinder _ _ _ (H.some.trans H'.some), }, },
  { intro h,
    apply category_theory.quotient.sound,
    let P := (path_object_exists Y.1.1).some,
    have H := P.right_homotopy_of_left_homotopy C h.some,
    exact cofibrant_objects.right_ho_trans_closure.right_homotopy ⟨P, nonempty.intro H⟩, }
end

variable (M)

def W : arrow_class (M.fibrant_and_cofibrant_objects) :=
λ f, arrow.mk (forget.map f.hom) ∈ M.W

variable {M}

namespace universal_property

@[simps]
def lift {D : Type*} [category D]
  (G : M.fibrant_and_cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) :
  fibrant_and_cofibrant_objects.Ho M ⥤ D :=
{ obj := λ X, G.obj ⟨X.1.1, X.2⟩,
  map := λ X Y, begin
    apply quot.lift, rotate,
    { exact λ f, G.map f, },
    { intros f g h,
      let X' : M.fibrant_and_cofibrant_objects := ⟨X.val.as, X.2⟩,
      haveI : is_cofibrant X'.1.1 := X'.1.2.some,
      let Y' : M.fibrant_and_cofibrant_objects := ⟨Y.val.as, Y.2⟩,
      let f' : X' ⟶ Y' := f,
      let g' : X' ⟶ Y' := g,
      have h' : L.map f' = L.map g' := quot.sound h,
      cases cylinder_exists X'.1.1 with C hC,
      rw L_map_eq_iff C at h',
      let Z' : M.fibrant_and_cofibrant_objects := ⟨⟨C.I, _⟩, _⟩, rotate,
      { refine nonempty.intro { cof := _ },
        convert M.cof_comp_stable _ _ _ (initial.to X.1.1.1) C.d₀
          X.1.1.2.some.cof C.cof_d₀, },
      { refine nonempty.intro { fib := _ },
        convert M.fib_comp_stable _ _ _ C.σ (terminal.from _)
          hC X'.2.some.fib, },
      let H := h'.some,
      let φ : Z' ⟶ Y' := H.h,
      let δ₀ : X' ⟶ Z' := C.to_precylinder.d₀,
      let δ₁ : X' ⟶ Z' := C.to_precylinder.d₁,
      let σ : Z' ⟶ X' := C.to_precylinder.σ,
      have h₀ : δ₀ ≫ φ = f := H.h₀,
      have h₁ : δ₁ ≫ φ = g := H.h₁,
      simp only [← h₀, ← h₁, G.map_comp],
      congr' 1,
      haveI : is_iso (G.map σ) := hG ⟨arrow.mk σ, C.Wσ⟩,
      simp only [← cancel_mono (G.map σ), ← G.map_comp],
      erw [C.σd₀, C.σd₁], },
  end,
  map_id' := λ X, G.map_id _,
  map_comp' := begin
    rintros X Y Z ⟨f⟩ ⟨g⟩,
    dsimp,
    let X' : M.fibrant_and_cofibrant_objects := ⟨X.val.as, X.2⟩,
    let Y' : M.fibrant_and_cofibrant_objects := ⟨Y.val.as, Y.2⟩,
    let Z' : M.fibrant_and_cofibrant_objects := ⟨Z.val.as, Z.2⟩,
    let f' : X' ⟶ Y' := f,
    let g' : Y' ⟶ Z' := g,
    exact G.map_comp f' g',
  end, }

lemma fac {D : Type*} [category D]
  (G : M.fibrant_and_cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) : L ⋙ lift G hG = G :=
begin
  apply category_theory.functor.ext,
  { rintros ⟨⟨X, h₀⟩, h₁⟩ ⟨⟨Y, h₂⟩, h₃⟩ f,
    simp only [functor.comp_map, L_map, induced_functor_map,
      cofibrant_objects.L_map, lift_map],
    erw [id_comp, comp_id], },
  { intro X,
    simp only [functor.comp_obj, lift_obj, subtype.val_eq_coe,
      L_obj_coe, induced_functor_obj, cofibrant_objects.L_obj_as,
      subtype.coe_eta], }
end

lemma uniq {E : Type*} [category E] 
  (G₁ G₂ : fibrant_and_cofibrant_objects.Ho M ⥤ E)
  (h₁₂ : L ⋙ G₁ = L ⋙ G₂) : G₁ = G₂ :=
begin
  apply category_theory.functor.ext,
  { rintros ⟨⟨X, h₀⟩, h₁⟩ ⟨⟨Y, h₂⟩, h₃⟩ f,
    let X' : M.fibrant_and_cofibrant_objects := ⟨⟨X, h₀⟩, h₁⟩,
    let Y' : M.fibrant_and_cofibrant_objects := ⟨⟨Y, h₂⟩, h₃⟩,
    cases category_theory.quotient.functor_map_surj _ _ _ f with f' hf',
    let f'' : X' ⟶ Y' := f',
    have eq : f = L.map f'' := hf'.symm,
    convert functor.congr_map_conjugate h₁₂ f'', },
  { intro X,
    convert functor.congr_obj h₁₂ ⟨X.val.as, X.2⟩,
    all_goals { ext, refl, }, }
end

lemma inverts_triv_cof {X Y : M.fibrant_and_cofibrant_objects} (f : X ⟶ Y)
  (hf : (arrow.mk f : arrow M.C) ∈ M.triv_cof) :
  (arrow.mk f).is_inverted_by L :=
begin
  sorry
end

def fixed_target {E : Type*} [category E] :
  arrow_class.is_strict_localization_fixed_target (W M) L E :=
{ inverts_W := begin
    sorry,
  end,
  lift := lift,
  fac := fac,
  uniq := uniq }

end universal_property

def is_strict_localization : arrow_class.is_strict_localization (W M) L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

end fibrant_and_cofibrant_objects

end model_category

end algebraic_topology
-- cf category_theory.full_subcategory