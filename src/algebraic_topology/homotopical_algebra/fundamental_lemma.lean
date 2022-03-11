/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cylinder
import algebraic_topology.homotopical_algebra.ks_brown_lemma

noncomputable theory

open algebraic_topology
open category_theory
open category_theory.limits
open category_theory.category

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
  haveI : is_cofibrant A.1 := A.2.some,
  rcases P.right_homotopy_with_triv_cof_σ'_of_right_homotopy hP.some with ⟨P', H', hP'⟩,
  cases path_object_exists X.1 with Q hQ,
  let Sq := square.mk'' P'.pre.σ' Q.pre.π
    (g ≫  Q.pre.σ') (P'.pre.π ≫ (limits.prod.map g g)) _, rotate,
  { ext,
    { dsimp,
      simp only [assoc, prod.lift_fst, prod.lift_map],
      erw [Q.pre.σd₀', ← assoc, P'.pre.σd₀', id_comp, comp_id], },
    { dsimp,
      simp only [assoc, prod.lift_snd, prod.lift_map],
      erw [Q.pre.σd₁', ← assoc, P'.pre.σd₁', id_comp, comp_id], }, },
  let hSq := (M.CM4b Sq.left Sq.right hP' Q.fib_π).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  have eq₀ := congr_arg ((λ (f : _ ⟶ prod X.1 X.1), f ≫ limits.prod.fst)) l.fac_right,
  have eq₁ := congr_arg ((λ (f : _ ⟶ prod X.1 X.1), f ≫ limits.prod.snd)) l.fac_right,
  simp only [pre_path_object.π, prod.lift_fst, prod.lift_snd, prod.lift_map,
    square.mk''_right_hom, prod.comp_lift, square.mk''_hom_right] at eq₀ eq₁,
  let H'' : Q.pre.right_homotopy (f ≫ g) (f' ≫ g) := 
  { h := H'.h ≫ l.lift,
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

variable {M}

def forget : M.cofibrant_objects ⥤ M.C := induced_functor _

variable (M)

def W : arrow_class (M.cofibrant_objects) :=
λ f, arrow.mk (forget.map f.hom) ∈ M.W

end cofibrant_objects

@[derive category]
def fibrant_and_cofibrant_objects := { X : M.cofibrant_objects // nonempty (is_fibrant X.1) }

namespace fibrant_and_cofibrant_objects

def mk_obj (X : M.C) [h₁ : is_cofibrant X] [h₂ : is_fibrant X] : M.fibrant_and_cofibrant_objects :=
⟨⟨X, nonempty.intro h₁⟩, nonempty.intro h₂⟩

@[derive category]
def π := { X : cofibrant_objects.π M // nonempty (is_fibrant X.1.1) }

variable {M}

@[simps]
def inclusion : M.fibrant_and_cofibrant_objects ⥤ M.cofibrant_objects := induced_functor _

@[simps]
def L : M.fibrant_and_cofibrant_objects ⥤ fibrant_and_cofibrant_objects.π M :=
begin
  let F : M.fibrant_and_cofibrant_objects ⥤ cofibrant_objects.π M :=
    inclusion ⋙ cofibrant_objects.L M,
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

def L_map_eq_iff' {X Y : M.fibrant_and_cofibrant_objects} (P : path_object Y.1.1) (f g : X ⟶ Y) :
  L.map f = L.map g ↔ nonempty (P.pre.right_homotopy f g) :=
begin
  haveI := X.1.2.some,
  haveI := Y.2.some,
  let C := (cylinder_exists X.1.1).some,
  calc L.map f = L.map g ↔ nonempty (C.to_precylinder.left_homotopy f g) : L_map_eq_iff C f g
  ... ↔ nonempty (P.pre.right_homotopy f g) : left_homotopy_iff_right_homotopy C P f g,
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
  fibrant_and_cofibrant_objects.π M ⥤ D :=
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
      cofibrant_objects.L_map, lift_map, inclusion_map],
    erw [id_comp, comp_id], },
  { intro X,
    simp only [functor.comp_obj, lift_obj, subtype.val_eq_coe,
      L_obj_coe, induced_functor_obj, cofibrant_objects.L_obj_as,
      subtype.coe_eta, inclusion_obj], }
end

lemma uniq {E : Type*} [category E] 
  (G₁ G₂ : fibrant_and_cofibrant_objects.π M ⥤ E)
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
  let f' : X.1.1 ⟶ Y.1.1 := f,
  let Sq := square.mk'' f' (terminal.from _) (𝟙 _) (terminal.from _) (subsingleton.elim _ _),
  let hSq := (M.CM4b Sq.left Sq.right hf X.2.some.fib).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  apply is_iso.mk,
  use L.map l.lift,
  split,
  { erw [← L.map_comp, arrow.mk_hom, l.fac_left, L.map_id], },
  { cases path_object_exists Y.1.1 with P hP,
    symmetry,
    rw [← L.map_comp, ← L.map_id, L_map_eq_iff' P],
    let Sq' := square.mk'' f' P.pre.π (f' ≫ P.pre.σ') (prod.lift (𝟙 _) (l.lift ≫ f')) _, swap,
    { ext,
      { simp only [pre_path_object.π, assoc, prod.lift_fst, comp_id, P.pre.σd₀'], },
      { simp only [pre_path_object.π, assoc, prod.lift_snd, comp_id, P.pre.σd₁'],
        erw [← assoc, l.fac_left, id_comp], }, },
    let hSq' := (M.CM4b Sq'.left Sq'.right hf P.fib_π).sq_has_lift,
    let l' := (hSq' Sq'.hom).exists_lift.some,
    have eq₀ := congr_arg ((λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.fst)) l'.fac_right,
    have eq₁ := congr_arg ((λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.snd)) l'.fac_right,
    simp only [pre_path_object.π, prod.lift_fst, square.mk''_right_hom, prod.comp_lift, square.mk''_hom_right] at eq₀,
    simp at eq₁,
    exact nonempty.intro
    { h := l'.lift,
      h₀ := eq₀,
      h₁ := eq₁, } },
end

lemma inverts_W : (W M).is_inverted_by L :=
begin
  rintro ⟨⟨X, Y, w⟩, hw⟩,
  haveI := X.1.2.some,
  haveI := Y.1.2.some,
  let w' : X.1.1 ⟶ Y.1.1 := w,
  have brown_fac := (exists_brown_factorisation_W_between_cofibrant_objects w' hw).some,
  let Z : M.fibrant_and_cofibrant_objects := ⟨⟨brown_fac.Z, _⟩, _⟩, rotate,
  { refine nonempty.intro ⟨_⟩,
    convert M.cof_comp_stable _ _ _ (initial.to X.1.1) brown_fac.i X.1.2.some.cof brown_fac.triv_cof_i.1, },
  { refine nonempty.intro ⟨_⟩,
    convert M.fib_comp_stable _ _ _ brown_fac.p (terminal.from Y.1.1) brown_fac.triv_fib_p.1 Y.2.some.fib, },
  let i' : X ⟶ Z := brown_fac.i,
  let p' : Z ⟶ Y := brown_fac.p,
  let s' : Y ⟶ Z := brown_fac.s,
  suffices : is_iso (L.map i' ≫ L.map p'),
  { simpa only [← L.map_comp, show i' ≫ p' = w, by exact brown_fac.fac₁.symm] using this, },
  haveI : is_iso (L.map i') := inverts_triv_cof i' brown_fac.triv_cof_i,
  haveI : is_iso (L.map s') := inverts_triv_cof s' brown_fac.triv_cof_s,
  have eq : L.map p' = inv (L.map s'),
  { apply is_iso.eq_inv_of_hom_inv_id,
    erw [← L.map_comp, brown_fac.fac₂, L.map_id], },
  haveI : is_iso (L.map p') := by { rw eq, apply_instance, },
  apply_instance,
end

def fixed_target {E : Type*} [category E] :
  arrow_class.is_strict_localization_fixed_target (W M) L E :=
{ inverts_W := inverts_W,
  lift := lift,
  fac := fac,
  uniq := uniq }

end universal_property

def is_strict_localization : arrow_class.is_strict_localization (W M) L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

end fibrant_and_cofibrant_objects

variable {M}

structure fibrant_replacement (X : M.C) :=
(Y : M.C) (hY : is_fibrant Y) (f : X ⟶ Y) (hf : arrow.mk f ∈ M.triv_cof)

namespace cofibrant_objects

namespace fibrant_replacement

def some_replacement (X : M.cofibrant_objects) :
  fibrant_replacement X.1 :=
begin
  suffices : nonempty (fibrant_replacement X.1),
  { exact this.some, },
  rcases M.CM5a (arrow.mk (terminal.from X.1)) with ⟨Y, i, p, fac, hi, hp⟩,
  refine nonempty.intro
  { Y := Y,
    hY := ⟨by convert hp⟩,
    f := i,
    hf := hi, },
end

def obj (X : M.cofibrant_objects) : M.fibrant_and_cofibrant_objects :=
begin
  refine ⟨⟨(some_replacement X).Y, nonempty.intro ⟨_⟩⟩, nonempty.intro (some_replacement X).hY⟩,
  convert M.cof_comp_stable _ _ _ (initial.to X.1)
    (some_replacement X).f X.2.some.cof (some_replacement X).hf.1,
end

def ι (X : M.cofibrant_objects) : X.1 ⟶ (obj X).1.1 :=
(some_replacement X).f

def triv_cof_ι (X : M.cofibrant_objects) : arrow.mk (ι X) ∈ M.triv_cof :=
(some_replacement X).hf

def obj_π (X : M.cofibrant_objects) : fibrant_and_cofibrant_objects.π M :=
fibrant_and_cofibrant_objects.L.obj (fibrant_replacement.obj X)

namespace map

variables {X Y : M.cofibrant_objects} (f : X ⟶ Y)

def Sq : square M.C :=
square.mk'' (ι X) (terminal.from (obj Y).1.1)
    (f ≫ ι Y) (terminal.from _) (subsingleton.elim _ _)

def Sq_lift_struct : arrow.lift_struct (Sq f).hom :=
begin
  let hSq := (M.CM4b (Sq f).left (Sq f).right (triv_cof_ι X)
    (obj Y).2.some.fib).sq_has_lift,
  exact (hSq (Sq f).hom).exists_lift.some,
end

def Sq_lift : obj X ⟶ obj Y := (Sq_lift_struct f).lift

def Sq_lift_comm : ι X ≫ Sq_lift f = f ≫ ι Y :=
(Sq_lift_struct f).fac_left

end map

def map_π {X Y : M.cofibrant_objects} (f : X ⟶ Y) :
  obj_π X ⟶ obj_π Y := (L M).map (map.Sq_lift f)

def map_π_eq {X Y : M.cofibrant_objects} (f : X ⟶ Y)
  (f' : obj X ⟶ obj Y) (comm : ι X ≫ f' = f ≫ ι Y) : map_π f = (L M).map f' :=
begin
  let P := (path_object_exists (obj Y).1.1).some,
  apply (fibrant_and_cofibrant_objects.L_map_eq_iff' P _ _).mpr,
  let Sq := square.mk'' (ι X) P.pre.π (f ≫ ι Y ≫ P.pre.σ') (prod.lift (map.Sq_lift f) f') _, swap,
  { ext,
    { simp only [pre_path_object.π, assoc, prod.lift_fst, P.pre.σd₀', comp_id, map.Sq_lift_comm], },
    { simp only [pre_path_object.π, assoc, prod.lift_snd, P.pre.σd₁', comp_id, comm], }, },
  let hSq := (M.CM4b (Sq.left) (Sq.right) (triv_cof_ι X) P.fib_π).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  have eq₀ := congr_arg ((λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.fst)) l.fac_right,
  have eq₁ := congr_arg ((λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.snd)) l.fac_right,
  simp only [pre_path_object.π, prod.lift_fst, prod.lift_snd,
    square.mk''_right_hom, prod.comp_lift, square.mk''_hom_right] at eq₀ eq₁,
  exact nonempty.intro
  { h := l.lift,
    h₀ := eq₀,
    h₁ := eq₁, },
end

variable (M)

@[derive category]
def localization := induced_category (fibrant_and_cofibrant_objects.π M) fibrant_replacement.obj_π

variable {M}

def L : M.cofibrant_objects ⥤ localization M :=
{ obj := id,
  map := λ X Y f, fibrant_replacement.map_π f,
  map_id' := λ X, begin
    erw [map_π_eq (𝟙 X) (𝟙 _) (by erw [id_comp, comp_id]), (L M).map_id],
    refl,
  end,
  map_comp' := λ X Y Z f g, begin
    erw map_π_eq (f ≫ g) (map.Sq_lift f ≫ map.Sq_lift g), swap,
    { erw [← assoc, map.Sq_lift_comm f, assoc, map.Sq_lift_comm g, assoc], },
    erw functor.map_comp,
    refl,
  end }

@[derive full, derive faithful]
def R : localization M ⥤ fibrant_and_cofibrant_objects.π M := induced_functor _

lemma compatibility_ι_L {X Y : M.cofibrant_objects} (f : obj X ⟶ obj Y) :
  L.map (ι X) ≫ L.map f = fibrant_and_cofibrant_objects.L.map f ≫ L.map (ι Y) :=
begin
  have compat : Π (Z : M.cofibrant_objects), fibrant_and_cofibrant_objects.L.map (ι (obj Z).val) = L.map (ι Z) :=
    λ Z, (map_π_eq (ι Z) (ι (obj Z).1) rfl).symm,
  have h := functor.congr_map fibrant_and_cofibrant_objects.L (map.Sq_lift_comm f),
  repeat { erw [functor.map_comp] at h, },
  simpa only [← compat] using h,
end

namespace universal_property

lemma inverts_W : (W M).is_inverted_by L := begin
  intro w,
  suffices : is_iso (fibrant_replacement.map_π w.1.hom),
  { haveI : is_iso (R.map (L.map w.1.hom)) := this,
    convert is_iso_of_reflects_iso (L.map w.1.hom) R, },
  suffices : arrow.mk (map.Sq_lift w.1.hom) ∈ fibrant_and_cofibrant_objects.W M,
  { exact fibrant_and_cofibrant_objects.universal_property.inverts_W ⟨_, this⟩, },
  apply M.CM2.of_comp_left (ι w.1.left) (map.Sq_lift w.1.hom) (triv_cof_ι w.1.left).2,
  rw map.Sq_lift_comm,
  apply M.CM2.of_comp,
  { exact w.2, },
  { exact (triv_cof_ι w.1.right).2, },
end

def G₁ {D : Type*} [category D]
  (G : M.cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) :
  M.fibrant_and_cofibrant_objects ⥤ D :=
fibrant_and_cofibrant_objects.inclusion ⋙ G

def G₁_inverts_W {D : Type*} [category D]
  (G : M.cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) :
  (fibrant_and_cofibrant_objects.W M).is_inverted_by (G₁ G hG) :=
begin
  rintro ⟨f, hf⟩,
  let f' : f.left.1 ⟶ f.right.1 := f.hom,
  exact hG ⟨f', hf⟩,
end

def G₂ {D : Type*} [category D]
  (G : M.cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) :
  fibrant_and_cofibrant_objects.π M ⥤ D :=
fibrant_and_cofibrant_objects.universal_property.lift (G₁ G hG) (G₁_inverts_W G hG)

@[simps]
def lift {D : Type*} [category D]
  (G : M.cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) :
  localization M ⥤ D :=
begin
  haveI : Π (X : localization M), is_iso (G.map (ι X)) :=
  λ X, hG ⟨arrow.mk (ι X), (triv_cof_ι X).2⟩,
  exact
  { obj := G.obj,
    map := λ X Y f, G.map (ι X) ≫ (G₂ G hG).map (fibrant_replacement.R.map f) ≫ inv (G.map (ι Y)),
    map_id' := λ X, by erw [category_theory.functor.map_id, id_comp, is_iso.hom_inv_id],
    map_comp' := λ X Y Z f g, begin
      slice_rhs 3 4 { rw is_iso.inv_hom_id, },
      slice_rhs 2 4 { simp only [id_comp, ← functor.map_comp], },
    end },
end

lemma fac {D : Type*} [category D]
  (G : M.cofibrant_objects ⥤ D)
  (hG : (W M).is_inverted_by G) : L ⋙ lift G hG = G :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    have G₁_fac := fibrant_and_cofibrant_objects.universal_property.fac (G₁ G hG) (G₁_inverts_W G hG),
    have h := functor.congr_map_conjugate G₁_fac (map.Sq_lift f),
    simp only [eq_to_hom_refl, id_comp, comp_id] at ⊢ h,
    simp only [functor.comp_map, lift_map] at ⊢ h,
    erw h,
    dsimp [G₁],
    erw [← assoc, ← G.map_comp, map.Sq_lift_comm f, G.map_comp, assoc, is_iso.hom_inv_id, comp_id], },
  { intro X,
    refl, },
end

lemma uniq' {E : Type*} [category E] 
  (G : localization M ⥤ E) :
  G = lift (L ⋙ G) ((W M).is_inverted_by_of_comp L G inverts_W) :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    simp only [eq_to_hom_refl, comp_id, id_comp],
    dsimp [lift],
    let f' := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some,
    have hf' : fibrant_and_cofibrant_objects.L.map f' = R.map f, by exact (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some_spec,
    rw [← hf'],
    dsimp [G₂, G₁],
    erw [← assoc, ← G.map_comp, compatibility_ι_L f', G.map_comp, assoc, is_iso.hom_inv_id, comp_id, hf'],
    refl, },
  { intro X,
    refl, },
end

lemma uniq {E : Type*} [category E] 
  (G₁ G₂ : localization M ⥤ E)
  (h₁₂ : L ⋙ G₁ = L ⋙ G₂) : G₁ = G₂ :=
by { rw [uniq' G₁, uniq' G₂], congr', }

def fixed_target {E : Type*} [category E] :
  arrow_class.is_strict_localization_fixed_target (W M) L E :=
{ inverts_W := inverts_W,
  lift := lift,
  fac := fac,
  uniq := uniq }

end universal_property

def is_strict_localization : arrow_class.is_strict_localization (W M) L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

def L_π : cofibrant_objects.π M ⥤ fibrant_and_cofibrant_objects.π M :=
category_theory.quotient.lift _ (L ⋙ R)
begin
  intros X Y f g h,
  induction h with f₀ f₁ h f₁ f₂ f₃ h₁₂ h₁₃ H₁₂ H₁₃,
  { cases h with P hP,
    haveI : is_cofibrant X.1 := X.2.some,
    rcases P.right_homotopy_with_triv_cof_σ'_of_right_homotopy hP.some with ⟨P', H', hP'⟩,
    simp only [functor.comp_map],
    congr' 1,
    let Z : M.cofibrant_objects := ⟨P'.pre.I', nonempty.intro { cof := _ }⟩, swap,
    { convert M.cof_comp_stable _ _ _ (initial.to _) P'.pre.σ' Y.2.some.cof hP'.1, },
    let h'' : X ⟶ Z := H'.h,
    let d₀' : Z ⟶ Y := P'.pre.d₀',
    let d₁' : Z ⟶ Y := P'.pre.d₁',
    let h₀'' : f₀ = h'' ≫ d₀' := H'.h₀.symm,
    let h₁'' : f₁ = h'' ≫ d₁' := H'.h₁.symm,
    simp only [h₀'', h₁'', L.map_comp],
    congr' 1,
    let s : Y ⟶ Z := P'.pre.σ',
    haveI : is_iso (L.map s) := universal_property.inverts_W ⟨arrow.mk s, hP'.2⟩,
    rw ← cancel_epi (L.map s),
    simp only [← L.map_comp],
    erw [P'.pre.σd₀', P'.pre.σd₁'], },
  { rw [H₁₂, H₁₃], },
end

/-def L_map_surjective (X Y : M.cofibrant_objects) [hY : is_fibrant Y.1] :
  function.surjective (λ (f : X ⟶ Y), L.map f) :=
begin
  intro f,
  let f' : obj X ⟶ obj Y := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some,
  have hf' : fibrant_and_cofibrant_objects.L.map f' = f := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some_spec,
  let g : X ⟶ (obj Y).1 := ι X ≫ f',
  let Y' : M.fibrant_and_cofibrant_objects := ⟨Y, nonempty.intro hY⟩,
  let i : Y' ⟶ obj Y := ι Y,
  let i' := fibrant_and_cofibrant_objects.L.map i,
  haveI : is_iso i' := fibrant_and_cofibrant_objects.universal_property.inverts_W ⟨arrow.mk i, (triv_cof_ι Y).2⟩,
  let s := (fibrant_and_cofibrant_objects.L_map_surjective _ _ (inv i')).some,
  let hs : fibrant_and_cofibrant_objects.L.map s = inv i' := (fibrant_and_cofibrant_objects.L_map_surjective _ _ (inv i')).some_spec,
  use ι X ≫ f' ≫ s,
  simp only [L.map_comp, ← assoc, compatibility_ι_L f', hf'],
  haveI : is_iso (L.map (ι Y)) := universal_property.inverts_W ⟨arrow.mk (ι Y), (triv_cof_ι Y).2⟩,
  rw ← cancel_mono (L.map (ι Y)),
  slice_lhs 3 4 { rw ← L.map_comp, },
  rw compatibility_ι_L,
  conv_rhs { erw ← id_comp (L.map _), },
  congr' 2,
  erw category_theory.functor.map_comp,
  convert is_iso.inv_hom_id i',
end-/

end fibrant_replacement

end cofibrant_objects

end model_category

end algebraic_topology
