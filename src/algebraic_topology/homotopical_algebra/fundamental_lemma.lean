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

namespace algebraic_topology

namespace model_category

variables (C : Type*) [category C] [M : model_category C]
include M

@[derive category]
def cofibrant_objects := { X : C // nonempty (is_cofibrant X) }

variable {C}

namespace cofibrant_objects

@[simps]
def inclusion : cofibrant_objects C ⥤ C := induced_functor _

def right_homotopy : hom_rel (cofibrant_objects C) := λ A X f₁ f₂,
∃ (P : path_object X.1), nonempty (P.pre.right_homotopy f₁ f₂)

namespace right_homotopy

def symm {A X : cofibrant_objects C} {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) :
  right_homotopy f₂ f₁ :=
by { cases H with P hP, use P.symm, exact nonempty.intro hP.some.symm, }

lemma comp_left {A B X : cofibrant_objects C}
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_homotopy g g') :
  right_homotopy (f ≫ g) (f ≫ g') :=
by { cases H with P hP, use P, exact nonempty.intro (hP.some.comp_left f), }

lemma comp_right {A B X : cofibrant_objects C}
  {f f' : A ⟶ B} {g : B ⟶ X} (H : right_homotopy f f') :
  right_homotopy (f ≫ g) (f' ≫ g) :=
begin
  cases H with P hP,
  haveI : is_cofibrant A.1 := A.2.some,
  rcases P.right_homotopy_with_triv_cof_σ'_of_right_homotopy hP.some with ⟨P', H', hP'⟩,
  cases path_object_exists X.1 with Q hQ,
  suffices H'' : Q.pre.right_homotopy (P'.pre.d₀' ≫ g) (P'.pre.d₁' ≫ g),
  { use Q,
    refine nonempty.intro
    { h := H'.h ≫ H''.h,
      h₀ := by { rw [assoc, H''.h₀, ← assoc, H'.h₀], refl, },
      h₁ := by { rw [assoc, H''.h₁, ← assoc, H'.h₁], refl, }, }, },
  apply Q.homotopy_extension _ _ P'.pre.σ' hP',
  erw [← assoc, P'.pre.σd₀', ← assoc, P'.pre.σd₁', id_comp],
  apply pre_path_object.right_homotopy.refl,
end

end right_homotopy

inductive right_ho_trans_closure {A X : cofibrant_objects C} : (A ⟶ X) → (A ⟶ X) → Prop
| right_homotopy {f₁ f₂ : A ⟶ X} (H : right_homotopy f₁ f₂) : right_ho_trans_closure f₁ f₂
| trans {f₁ f₂ f₃ : A ⟶ X} (H₁₂ : right_ho_trans_closure f₁ f₂) (H₂₃ : right_ho_trans_closure f₂ f₃) :
  right_ho_trans_closure f₁ f₃

namespace right_ho_trans_closure

lemma is_equiv (A X : cofibrant_objects C) : is_equiv (A ⟶ X) right_ho_trans_closure :=
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

lemma comp_left (A B X : cofibrant_objects C)
  (f : A ⟶ B) {g g' : B ⟶ X} (H : right_ho_trans_closure g g') :
    right_ho_trans_closure (f ≫ g) (f ≫ g') :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy (H₁₂.comp_left f), },
  { exact trans H₁₂' H₂₃', }
end

lemma comp_right (A B X : cofibrant_objects C)
  (f f' : A ⟶ B) {g : B ⟶ X} (H : right_ho_trans_closure f f') :
    right_ho_trans_closure (f ≫ g) (f' ≫ g) :=
begin
  induction H with f₁ f₂ H₁₂ f₁ f₂ f₃ H₁₂ H₂₃ H₁₂' H₂₃',
  { exact right_homotopy H₁₂.comp_right, },
  { exact trans H₁₂' H₂₃', },
end

variable (M)

@[simp]
def hom_rel : hom_rel (cofibrant_objects C) := λ X Y, cofibrant_objects.right_ho_trans_closure

instance : congruence (hom_rel M) :=
{ is_equiv := right_ho_trans_closure.is_equiv,
  comp_left := right_ho_trans_closure.comp_left,
  comp_right := right_ho_trans_closure.comp_right }

end right_ho_trans_closure

variable (C)

@[derive category]
def π := quotient (right_ho_trans_closure.hom_rel M)

variable {C}

@[simps]
def L : (cofibrant_objects C) ⥤ cofibrant_objects.π C :=
quotient.functor (right_ho_trans_closure.hom_rel M)

def L_map_eq_iff_when_target_is_fibrant {X Y : cofibrant_objects C} [hY : is_fibrant Y.1] (Cyl : cylinder X.1) (f g : X ⟶ Y) :
  L.map f = L.map g ↔ nonempty (Cyl.to_precylinder.left_homotopy f g) :=
begin
  haveI := X.2.some,
  haveI := Y.2.some,
  split,
  { intro h,
    dsimp only [L, functor.comp_map, cofibrant_objects.L] at h,
    erw quotient.functor_map_eq_iff at h,
    dsimp at h,
    induction h with f₀ f₁ Hr f₁ f₂ f₃ H₁₂ H₂₃ H H',
    { cases Hr with P hP,
      apply nonempty.intro,
      exact Cyl.left_homotopy_of_right_homotopy P hP.some, },
    { apply nonempty.intro,
      exact cylinder.left_homotopy_from_other_cylinder _ _ _ _ (H.some.trans H'.some), }, },
  { intro h,
    apply category_theory.quotient.sound,
    let P := (path_object_exists Y.1).some,
    have H := P.right_homotopy_of_left_homotopy Cyl h.some,
    exact cofibrant_objects.right_ho_trans_closure.right_homotopy ⟨P, nonempty.intro H⟩, },
end

def forget : cofibrant_objects C ⥤ C := induced_functor _

def W : arrow_class (cofibrant_objects C) :=
λ f, arrow.mk (forget.map f.hom) ∈ (model_category.W : arrow_class C)

end cofibrant_objects

variable (C)

@[derive category]
def fibrant_and_cofibrant_objects := { X : cofibrant_objects C // nonempty (is_fibrant X.1) }

variable {C}

namespace fibrant_and_cofibrant_objects

def mk_obj (X : C) [h₁ : is_cofibrant X] [h₂ : is_fibrant X] : fibrant_and_cofibrant_objects C :=
⟨⟨X, nonempty.intro h₁⟩, nonempty.intro h₂⟩

variable (C)

@[derive category]
def π := { X : cofibrant_objects.π C // nonempty (is_fibrant X.1.1) }

variable {C}

@[simps]
def inclusion : fibrant_and_cofibrant_objects C ⥤ cofibrant_objects C := induced_functor _

@[simps]
def L : fibrant_and_cofibrant_objects C ⥤ fibrant_and_cofibrant_objects.π C :=
begin
  let F : fibrant_and_cofibrant_objects C ⥤ cofibrant_objects.π C :=
    inclusion ⋙ cofibrant_objects.L,
  exact
  { obj := λ X, ⟨F.obj X, X.2⟩,
    map := λ X Y f, F.map f,
    map_id' := λ X, F.map_id X,
    map_comp' := λ X Y Z f g, F.map_comp f g, }
end

def forget : fibrant_and_cofibrant_objects C ⥤ C := induced_functor _

def L_map_surjective (X Y : fibrant_and_cofibrant_objects C) :
  function.surjective (λ (f : X ⟶ Y), L.map f) :=
begin
  intro f,
  cases category_theory.quotient.functor_map_surj _ _ _ f with g hg,
  dsimp at g,
  use [g, hg],
end

def L_map_eq_iff {X Y : fibrant_and_cofibrant_objects C} (Cyl : cylinder X.1.1) (f g : X ⟶ Y) :
  L.map f = L.map g ↔ nonempty (Cyl.to_precylinder.left_homotopy f g) :=
begin
  haveI : is_fibrant (inclusion.obj Y).1 := Y.2.some,
  exact cofibrant_objects.L_map_eq_iff_when_target_is_fibrant Cyl f g,
end

def L_map_eq_iff' {X Y : fibrant_and_cofibrant_objects C} (P : path_object Y.1.1) (f g : X ⟶ Y) :
  L.map f = L.map g ↔ nonempty (P.pre.right_homotopy f g) :=
begin
  haveI := X.1.2.some,
  haveI := Y.2.some,
  let C := (cylinder_exists X.1.1).some,
  calc L.map f = L.map g ↔ nonempty (C.to_precylinder.left_homotopy f g) : L_map_eq_iff C f g
  ... ↔ nonempty (P.pre.right_homotopy f g) : left_homotopy_iff_right_homotopy C P f g,
end

def W : arrow_class (fibrant_and_cofibrant_objects C) :=
λ f, arrow.mk (forget.map f.hom) ∈ M.W

variable {M}

namespace universal_property

@[simps]
def lift {D : Type*} [category D]
  (G : fibrant_and_cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class (fibrant_and_cofibrant_objects C)).is_inverted_by G) :
  fibrant_and_cofibrant_objects.π C ⥤ D :=
{ obj := λ X, G.obj ⟨X.1.1, X.2⟩,
  map := λ X Y, begin
    apply quot.lift, rotate,
    { exact λ f, G.map f, },
    { intros f g h,
      let X' : fibrant_and_cofibrant_objects C := ⟨X.val.as, X.2⟩,
      haveI : is_cofibrant X'.1.1 := X'.1.2.some,
      let Y' : fibrant_and_cofibrant_objects C := ⟨Y.val.as, Y.2⟩,
      let f' : X' ⟶ Y' := f,
      let g' : X' ⟶ Y' := g,
      have h' : L.map f' = L.map g' := quot.sound h,
      cases cylinder_exists X'.1.1 with Cyl hC,
      rw L_map_eq_iff Cyl at h',
      let Z' : fibrant_and_cofibrant_objects C := ⟨⟨Cyl.I, _⟩, _⟩, rotate,
      { refine nonempty.intro { cof := _ },
        convert cof_comp_stable _ _ _ (initial.to X.1.1.1) Cyl.d₀
          X.1.1.2.some.cof Cyl.cof_d₀, },
      { refine nonempty.intro { fib := _ },
        convert fib_comp_stable _ _ _ Cyl.σ (terminal.from _)
          hC X'.2.some.fib, },
      let H := h'.some,
      let φ : Z' ⟶ Y' := H.h,
      let δ₀ : X' ⟶ Z' := Cyl.to_precylinder.d₀,
      let δ₁ : X' ⟶ Z' := Cyl.to_precylinder.d₁,
      let σ : Z' ⟶ X' := Cyl.to_precylinder.σ,
      have h₀ : δ₀ ≫ φ = f := H.h₀,
      have h₁ : δ₁ ≫ φ = g := H.h₁,
      simp only [← h₀, ← h₁, G.map_comp],
      congr' 1,
      haveI : is_iso (G.map σ) := hG ⟨arrow.mk σ, Cyl.Wσ⟩,
      simp only [← cancel_mono (G.map σ), ← G.map_comp],
      erw [Cyl.σd₀, Cyl.σd₁], },
  end,
  map_id' := λ X, G.map_id _,
  map_comp' := begin
    rintros X Y Z ⟨f⟩ ⟨g⟩,
    dsimp,
    let X' : fibrant_and_cofibrant_objects C := ⟨X.val.as, X.2⟩,
    let Y' : fibrant_and_cofibrant_objects C := ⟨Y.val.as, Y.2⟩,
    let Z' : fibrant_and_cofibrant_objects C := ⟨Z.val.as, Z.2⟩,
    let f' : X' ⟶ Y' := f,
    let g' : Y' ⟶ Z' := g,
    exact G.map_comp f' g',
  end, }

lemma fac {D : Type*} [category D]
  (G : fibrant_and_cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class (fibrant_and_cofibrant_objects C)).is_inverted_by G) : L ⋙ lift G hG = G :=
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
  (G₁ G₂ : fibrant_and_cofibrant_objects.π C ⥤ E)
  (h₁₂ : L ⋙ G₁ = L ⋙ G₂) : G₁ = G₂ :=
begin
  apply category_theory.functor.ext,
  { rintros ⟨⟨X, h₀⟩, h₁⟩ ⟨⟨Y, h₂⟩, h₃⟩ f,
    let X' : fibrant_and_cofibrant_objects C := ⟨⟨X, h₀⟩, h₁⟩,
    let Y' : fibrant_and_cofibrant_objects C := ⟨⟨Y, h₂⟩, h₃⟩,
    cases category_theory.quotient.functor_map_surj _ _ _ f with f' hf',
    let f'' : X' ⟶ Y' := f',
    have eq : f = L.map f'' := hf'.symm,
    convert functor.congr_hom h₁₂ f'', },
  { intro X,
    convert functor.congr_obj h₁₂ ⟨X.val.as, X.2⟩,
    all_goals { ext, refl, }, }
end

lemma inverts_triv_cof {X Y : fibrant_and_cofibrant_objects C} (f : X ⟶ Y)
  (hf : (arrow.mk f : arrow C) ∈ (triv_cof : arrow_class C)) :
  (arrow.mk f).is_inverted_by L :=
begin
  let f' : X.1.1 ⟶ Y.1.1 := f,
  let Sq := square.mk'' f' (terminal.from _) (𝟙 _) (terminal.from _) (subsingleton.elim _ _),
  let hSq := (CM4b Sq.left Sq.right hf X.2.some.fib).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  apply is_iso.mk,
  use L.map l.lift,
  split,
  { erw [← L.map_comp, arrow.mk_hom, l.fac_left, L.map_id], },
  { cases path_object_exists Y.1.1 with P hP,
    symmetry,
    rw [← L.map_comp, ← L.map_id, L_map_eq_iff' P],
    have eq : f' ≫ P.pre.σ' ≫ P.pre.d₁' = f' ≫ (l.lift ≫ f'),
    { erw [P.pre.σd₁', comp_id, ← assoc, l.fac_left, id_comp], },
    let H := P.pre.right_homotopy_of_map_to (f' ≫ P.pre.σ'),
    erw [assoc, P.pre.σd₀', assoc, eq] at H,
    exact nonempty.intro (P.homotopy_extension _ _ f' hf H), }
end

lemma inverts_W : (W : arrow_class (fibrant_and_cofibrant_objects C)).is_inverted_by L :=
begin
  rintro ⟨⟨X, Y, w⟩, hw⟩,
  haveI := X.1.2.some,
  haveI := Y.1.2.some,
  let w' : X.1.1 ⟶ Y.1.1 := w,
  have brown_fac := (exists_brown_factorisation_W_between_cofibrant_objects w' hw).some,
  let Z : fibrant_and_cofibrant_objects C := ⟨⟨brown_fac.Z, _⟩, _⟩, rotate,
  { refine nonempty.intro ⟨_⟩,
    convert cof_comp_stable _ _ _ (initial.to X.1.1) brown_fac.i X.1.2.some.cof brown_fac.triv_cof_i.1, },
  { refine nonempty.intro ⟨_⟩,
    convert fib_comp_stable _ _ _ brown_fac.p (terminal.from Y.1.1) brown_fac.triv_fib_p.1 Y.2.some.fib, },
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
  arrow_class.is_strict_localization_fixed_target (W : arrow_class (fibrant_and_cofibrant_objects C)) L E :=
{ inverts_W := inverts_W,
  lift := lift,
  fac := fac,
  uniq := uniq }

end universal_property

def is_strict_localization : arrow_class.is_strict_localization (W : arrow_class (fibrant_and_cofibrant_objects C)) L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

end fibrant_and_cofibrant_objects

structure fibrant_replacement (X : C) :=
(Y : C) (hY : is_fibrant Y) (f : X ⟶ Y) (hf : arrow.mk f ∈ (triv_cof : arrow_class C))

namespace cofibrant_objects

namespace fibrant_replacement

def some_replacement (X : cofibrant_objects C) :
  fibrant_replacement X.1 :=
begin
  suffices : nonempty (fibrant_replacement X.1),
  { exact this.some, },
  rcases CM5a (arrow.mk (terminal.from X.1)) with ⟨Y, i, p, fac, hi, hp⟩,
  refine nonempty.intro
  { Y := Y,
    hY := ⟨by convert hp⟩,
    f := i,
    hf := hi, },
end

def obj (X : cofibrant_objects C) : fibrant_and_cofibrant_objects C :=
begin
  refine ⟨⟨(some_replacement X).Y, nonempty.intro ⟨_⟩⟩, nonempty.intro (some_replacement X).hY⟩,
  convert cof_comp_stable _ _ _ (initial.to X.1)
    (some_replacement X).f X.2.some.cof (some_replacement X).hf.1,
end

def ι' (X : cofibrant_objects C) : X ⟶ (obj X).1 :=
(some_replacement X).f

def ι (X : cofibrant_objects C) : X.1 ⟶ (obj X).1.1 := ι' X

def triv_cof_ι (X : cofibrant_objects C) : arrow.mk (ι X) ∈ triv_cof :=
(some_replacement X).hf

def obj_π (X : cofibrant_objects C) : fibrant_and_cofibrant_objects.π C :=
fibrant_and_cofibrant_objects.L.obj (fibrant_replacement.obj X)

namespace map

variables {X Y : cofibrant_objects C} (f : X ⟶ Y)

def Sq : square C :=
square.mk'' (ι X) (terminal.from (obj Y).1.1)
    (f ≫ ι Y) (terminal.from _) (subsingleton.elim _ _)

def Sq_lift_struct : arrow.lift_struct (Sq f).hom :=
begin
  let hSq := (CM4b (Sq f).left (Sq f).right (triv_cof_ι X)
    (obj Y).2.some.fib).sq_has_lift,
  exact (hSq (Sq f).hom).exists_lift.some,
end

def Sq_lift : obj X ⟶ obj Y := (Sq_lift_struct f).lift

def Sq_lift_comm : ι' X ≫ Sq_lift f = f ≫ ι' Y :=
(Sq_lift_struct f).fac_left

end map

def map_π {X Y : cofibrant_objects C} (f : X ⟶ Y) :
  obj_π X ⟶ obj_π Y := L.map (map.Sq_lift f)

def map_π_eq {X Y : cofibrant_objects C} (f : X ⟶ Y)
  (f' : obj X ⟶ obj Y) (comm : ι X ≫ f' = f ≫ ι Y) : map_π f = L.map f' :=
begin
  let P := (path_object_exists (obj Y).1.1).some,
  apply (fibrant_and_cofibrant_objects.L_map_eq_iff' P _ _).mpr,
  refine nonempty.intro (P.homotopy_extension _ _ (ι X) (triv_cof_ι X) _),
  erw [map.Sq_lift_comm, comm],
  apply pre_path_object.right_homotopy.refl,
end

variable (C)

@[derive category]
def localization := induced_category (fibrant_and_cofibrant_objects.π C) fibrant_replacement.obj_π

variable {C}

def L : cofibrant_objects C ⥤ localization C :=
{ obj := id,
  map := λ X Y f, fibrant_replacement.map_π f,
  map_id' := λ X, begin
    erw [map_π_eq (𝟙 X) (𝟙 _) (by erw [id_comp, comp_id]), L.map_id],
    refl,
  end,
  map_comp' := λ X Y Z f g, begin
    erw map_π_eq (f ≫ g) (map.Sq_lift f ≫ map.Sq_lift g), swap,
    { erw [← assoc, map.Sq_lift_comm f, assoc, map.Sq_lift_comm g, assoc], refl, },
    erw functor.map_comp,
    refl,
  end }

@[derive full, derive faithful]
def R : localization C ⥤ fibrant_and_cofibrant_objects.π C := induced_functor _

lemma compatibility_ι'_L {X Y : cofibrant_objects C} (f : obj X ⟶ obj Y) :
  L.map (ι' X) ≫ L.map f = fibrant_and_cofibrant_objects.L.map f ≫ L.map (ι' Y) :=
begin
  have compat : Π (Z : cofibrant_objects C), fibrant_and_cofibrant_objects.L.map (ι' (obj Z).val) = L.map (ι' Z) :=
    λ Z, (map_π_eq (ι' Z) (ι (obj Z).1) rfl).symm,
  have h := functor.congr_map fibrant_and_cofibrant_objects.L (map.Sq_lift_comm f),
  repeat { erw [functor.map_comp] at h, },
  simpa only [← compat] using h,
end

namespace universal_property

lemma inverts_W : (W : arrow_class (cofibrant_objects C)).is_inverted_by L := begin
  intro w,
  suffices : is_iso (fibrant_replacement.map_π w.1.hom),
  { haveI : is_iso (R.map (L.map w.1.hom)) := this,
    convert is_iso_of_reflects_iso (L.map w.1.hom) R, },
  suffices : arrow.mk (map.Sq_lift w.1.hom) ∈ fibrant_and_cofibrant_objects.W,
  { exact fibrant_and_cofibrant_objects.universal_property.inverts_W ⟨_, this⟩, },
  apply CM2.of_comp_left (ι w.1.left) (map.Sq_lift w.1.hom) (triv_cof_ι w.1.left).2,
  erw map.Sq_lift_comm,
  apply CM2.of_comp,
  { exact w.2, },
  { exact (triv_cof_ι w.1.right).2, },
end

def G₁ {D : Type*} [category D]
  (G : cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class (cofibrant_objects C)).is_inverted_by G) :
  fibrant_and_cofibrant_objects C ⥤ D :=
fibrant_and_cofibrant_objects.inclusion ⋙ G

def G₁_inverts_W {D : Type*} [category D]
  (G : cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class (cofibrant_objects C)).is_inverted_by G) :
  (fibrant_and_cofibrant_objects.W : arrow_class _).is_inverted_by (G₁ G hG) :=
begin
  rintro ⟨w, hw⟩,
  let w' : w.left.1 ⟶ w.right.1 := w.hom,
  exact hG ⟨w', hw⟩,
end

def G₂ {D : Type*} [category D]
  (G : cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class _).is_inverted_by G) :
  fibrant_and_cofibrant_objects.π C ⥤ D :=
fibrant_and_cofibrant_objects.universal_property.lift (G₁ G hG) (G₁_inverts_W G hG)

@[simps]
def lift {D : Type*} [category D]
  (G : cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class _).is_inverted_by G) :
  localization C ⥤ D :=
begin
  haveI : Π (X : localization C), is_iso (G.map (ι' X)) :=
  λ X, hG ⟨arrow.mk (ι' X), (triv_cof_ι X).2⟩,
  exact
  { obj := G.obj,
    map := λ X Y f, G.map (ι X) ≫ (G₂ G hG).map (fibrant_replacement.R.map f) ≫ inv (G.map (ι' Y)),
    map_id' := λ X, by erw [category_theory.functor.map_id, id_comp, is_iso.hom_inv_id],
    map_comp' := λ X Y Z f g, begin
      slice_rhs 3 4 { erw is_iso.inv_hom_id, },
      slice_rhs 2 4 { simp only [id_comp, ← functor.map_comp], },
    end },
end

lemma fac {D : Type*} [category D]
  (G : cofibrant_objects C ⥤ D)
  (hG : (W : arrow_class _).is_inverted_by G) : L ⋙ lift G hG = G :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    have G₁_fac := fibrant_and_cofibrant_objects.universal_property.fac (G₁ G hG) (G₁_inverts_W G hG),
    have h := functor.congr_hom G₁_fac (map.Sq_lift f),
    simp only [eq_to_hom_refl, id_comp, comp_id] at ⊢ h,
    simp only [functor.comp_map, lift_map] at ⊢ h,
    erw h,
    dsimp [G₁],
    erw [← assoc, ← G.map_comp, map.Sq_lift_comm f, G.map_comp, assoc, is_iso.hom_inv_id, comp_id], },
  { intro X,
    refl, },
end

lemma uniq' {E : Type*} [category E]
  (G : localization C ⥤ E) :
  G = lift (L ⋙ G) ((W : arrow_class _).is_inverted_by_of_comp L G inverts_W) :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    simp only [eq_to_hom_refl, comp_id, id_comp],
    dsimp [lift],
    let f' := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some,
    have hf' : fibrant_and_cofibrant_objects.L.map f' = R.map f, by exact (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some_spec,
    rw [← hf'],
    dsimp [G₂, G₁],
    erw [← assoc, ← G.map_comp, compatibility_ι'_L f', G.map_comp, assoc, is_iso.hom_inv_id, comp_id, hf'],
    refl, },
  { intro X,
    refl, },
end

lemma uniq {E : Type*} [category E]
  (G₁ G₂ : localization C ⥤ E)
  (h₁₂ : L ⋙ G₁ = L ⋙ G₂) : G₁ = G₂ :=
by { rw [uniq' G₁, uniq' G₂], congr', }

def fixed_target {E : Type*} [category E] :
  arrow_class.is_strict_localization_fixed_target (W : arrow_class (cofibrant_objects C)) L E :=
{ inverts_W := inverts_W,
  lift := lift,
  fac := fac,
  uniq := uniq }

end universal_property

def is_strict_localization : arrow_class.is_strict_localization (W : arrow_class (cofibrant_objects C)) L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

def L_π : cofibrant_objects.π C ⥤ localization C :=
category_theory.quotient.lift _ L
begin
  intros X Y f g h,
  induction h with f₀ f₁ h f₁ f₂ f₃ h₁₂ h₁₃ H₁₂ H₁₃,
  { cases h with P hP,
    haveI : is_cofibrant X.1 := X.2.some,
    rcases P.right_homotopy_with_triv_cof_σ'_of_right_homotopy hP.some with ⟨P', H', hP'⟩,
    let Z : cofibrant_objects C := ⟨P'.pre.I', nonempty.intro { cof := _ }⟩, swap,
    { convert cof_comp_stable _ _ _ (initial.to _) P'.pre.σ' Y.2.some.cof hP'.1, },
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

def L_π_inverts_W {X Y : cofibrant_objects C} (f : X ⟶ Y) (hf : arrow.mk f ∈ W) :
  is_iso (L_π.map (cofibrant_objects.L.map f)) :=
begin
  haveI : is_iso (L.map f) := universal_property.inverts_W ⟨arrow.mk f, hf⟩,
  dsimp [L_π],
  apply_instance,
end

def ι_fib_object (X : cofibrant_objects C) [hX : is_fibrant X.1] :
  (⟨X, nonempty.intro hX⟩ : fibrant_and_cofibrant_objects C) ⟶ obj X := ι X

def πι_fib_object (X : cofibrant_objects C) [hX : is_fibrant X.1] :=
  fibrant_and_cofibrant_objects.L.map (ι_fib_object X)

instance is_iso_πι_fib_object (X : cofibrant_objects C) [hX : is_fibrant X.1] :
  is_iso (πι_fib_object X) :=
fibrant_and_cofibrant_objects.universal_property.inverts_W ⟨arrow.mk (ι_fib_object X), (triv_cof_ι X).2⟩

lemma compatibility_ι_L_π {X Y : cofibrant_objects C} [hX : is_fibrant X.1] [hY : is_fibrant Y.1] (f : X ⟶ Y) :
  R.map (L_π.map (cofibrant_objects.L.map f)) =
  inv (@πι_fib_object _ _ _ X hX) ≫ (fibrant_and_cofibrant_objects.L.map (by exact f)) ≫ (@πι_fib_object _ _ _ Y hY) :=
begin
  rw [← cancel_epi (πι_fib_object X), ← assoc, ← assoc, is_iso.hom_inv_id, id_comp],
  repeat { erw ← fibrant_and_cofibrant_objects.L.map_comp, },
  congr' 1,
  exact map.Sq_lift_comm f,
end

lemma L_π_map_bijective_when_both_fibrant (X Y : cofibrant_objects.π C) [hX : is_fibrant X.1.1] [hY : is_fibrant Y.1.1] :
  function.bijective (λ (f : X ⟶ Y), L_π.map f) :=
begin
  split,
  { intros f₀ f₁ h₀₁,
    cases category_theory.quotient.functor_map_surj _ _ _ f₀ with g₀ hg₀,
    cases category_theory.quotient.functor_map_surj _ _ _ f₁ with g₁ hg₁,
    simp only at h₀₁ hg₀ hg₁,
    rw [show f₀ = cofibrant_objects.L.map g₀, by exact hg₀.symm] at h₀₁ ⊢,
    rw [show f₁ = cofibrant_objects.L.map g₁, by exact hg₁.symm] at h₀₁ ⊢,
    erw [compatibility_ι_L_π g₀, compatibility_ι_L_π g₁,
      cancel_epi (inv (πι_fib_object X.as)), cancel_mono (πι_fib_object Y.as)] at h₀₁,
    let Y' : fibrant_and_cofibrant_objects C := ⟨Y.1, nonempty.intro hY⟩,
    cases path_object_exists Y'.1.1 with P hP,
    rw fibrant_and_cofibrant_objects.L_map_eq_iff' P at h₀₁,
    cases h₀₁ with H,
    apply category_theory.quotient.sound,
    exact right_ho_trans_closure.right_homotopy ⟨P, nonempty.intro H⟩, },
  { intro g,
    let f := πι_fib_object X.as ≫ (by exact g) ≫ (inv (πι_fib_object Y.as)),
    let f' := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some,
    have hf' : fibrant_and_cofibrant_objects.L.map f' = f := (fibrant_and_cofibrant_objects.L_map_surjective _ _ f).some_spec,
    use cofibrant_objects.L.map f',
    simp only,
    erw [compatibility_ι_L_π f', hf'],
    dsimp only [f],
    simp only [assoc, is_iso.inv_hom_id, comp_id, is_iso.inv_hom_id_assoc], },
end

lemma L_π_map_bijective_when_target_is_fibrant (X Y : cofibrant_objects.π C) [hY : is_fibrant Y.1.1] :
  function.bijective (λ (f : X ⟶ Y), L_π.map f) :=
begin
  split,
  { intros f₀ f₁,
    cases category_theory.quotient.functor_map_surj _ _ _ f₀ with g₀ hg₀,
    cases category_theory.quotient.functor_map_surj _ _ _ f₁ with g₁ hg₁,
    simp only at hg₀ hg₁ ⊢,
    let Sq₀ := square.mk'' (ι X.as) (terminal.from Y.as.1) g₀ (terminal.from _) (subsingleton.elim _ _),
    let Sq₁ := square.mk'' (ι X.as) (terminal.from Y.as.1) g₁ (terminal.from _) (subsingleton.elim _ _),
    let hSq₀ := (CM4b Sq₀.left Sq₀.right (triv_cof_ι X.as) hY.fib).sq_has_lift,
    let hSq₁ := (CM4b Sq₁.left Sq₁.right (triv_cof_ι X.as) hY.fib).sq_has_lift,
    let l₀ := (hSq₀ Sq₀.hom).exists_lift.some,
    let l₁ := (hSq₁ Sq₁.hom).exists_lift.some,
    let h₀ : _ ⟶ Y.as := l₀.lift,
    let h₁ : _ ⟶ Y.as := l₁.lift,
    have eq₀' : cofibrant_objects.L.map (ι' X.as ≫ h₀) = cofibrant_objects.L.map g₀ :=
      functor.congr_map cofibrant_objects.L l₀.fac_left,
    have eq₁' : cofibrant_objects.L.map (ι' X.as ≫ h₁) = cofibrant_objects.L.map g₁ :=
      functor.congr_map cofibrant_objects.L l₁.fac_left,
    erw [← hg₀, ← eq₀', ← hg₁, ← eq₁'],
    intro H,
    repeat { erw cofibrant_objects.L.map_comp, },
    repeat { erw cofibrant_objects.L.map_comp at H, },
    repeat { erw L_π.map_comp at H, },
    congr' 1,
    haveI : is_fibrant Y.as.1 := hY,
    haveI : is_fibrant (obj_π X.as).1.as.val := (obj_π X.as).2.some,
    apply (L_π_map_bijective_when_both_fibrant (obj_π X.as).1 Y).1,
    let ιX := (cofibrant_objects.L.map (ι' X.as)),
    haveI : is_iso (L_π.map ιX) := L_π_inverts_W _ (triv_cof_ι X.as).2,
    exact (cancel_epi (L_π.map ιX)).mp H, },
  { intro g,
    haveI : is_fibrant (cofibrant_objects.L.obj (obj X.as).val).as.val := (obj X.1).2.some,
    haveI : is_iso (L_π.map (cofibrant_objects.L.map (ι' X.as))) := L_π_inverts_W _ (triv_cof_ι X.as).2,
    let g' := inv (L_π.map (cofibrant_objects.L.map (ι' X.as))) ≫ g,
    cases (L_π_map_bijective_when_both_fibrant (cofibrant_objects.L.obj (obj X.1).1) Y).2
      (inv (L_π.map (cofibrant_objects.L.map (ι' X.as))) ≫ g) with f hf,
    use cofibrant_objects.L.map (ι X.as) ≫ f,
    simp only [category_theory.functor.map_comp] at hf ⊢,
    erw [hf, ← assoc, is_iso.hom_inv_id, id_comp], },
end

end fibrant_replacement

end cofibrant_objects

structure cofibrant_replacement (X : C) :=
(Y : C) (hY : is_cofibrant Y) (f : Y ⟶ X) (hf : arrow.mk f ∈ (triv_fib : arrow_class C))

namespace cofibrant_replacement

def some_replacement (X : C) :
  cofibrant_replacement X :=
begin
  suffices : nonempty (cofibrant_replacement X),
  { exact this.some, },
  rcases CM5b (arrow.mk (initial.to X)) with ⟨Y, i, p, fac, hi, hp⟩,
  refine nonempty.intro
  { Y := Y,
    hY := ⟨by convert hi⟩,
    f := p,
    hf := hp, },
end

def obj (X : C) : cofibrant_objects C :=
⟨(some_replacement X).Y, nonempty.intro (some_replacement X).hY⟩

def p (X : C) : (obj X).1 ⟶ X :=
(some_replacement X).f

def triv_fib_p (X : C) : arrow.mk (p X) ∈ (triv_fib : arrow_class C) :=
(some_replacement X).hf

def obj_π (X : C) : cofibrant_objects.π C :=
cofibrant_objects.L.obj (obj X)

namespace map

variables {X Y : C} (f : X ⟶ Y)

def Sq : square C :=
square.mk'' (initial.to (obj X).1) (p Y) (initial.to _) (p X ≫ f)
    (subsingleton.elim _ _)

def Sq_lift_struct : arrow.lift_struct (Sq f).hom :=
begin
  let hSq := (CM4a (Sq f).left (Sq f).right (obj X).2.some.cof (triv_fib_p Y)).sq_has_lift,
  exact (hSq (Sq f).hom).exists_lift.some,
end

def Sq_lift : obj X ⟶ obj Y := (Sq_lift_struct f).lift

def Sq_lift_comm : cofibrant_objects.forget.map (Sq_lift f) ≫ p Y = p X ≫ f :=
(Sq_lift_struct f).fac_right

end map

def map_π {X Y : C} (f : X ⟶ Y) :
  obj_π X ⟶ obj_π Y := cofibrant_objects.L.map (map.Sq_lift f)

def map_π_eq {X Y : C} (f : X ⟶ Y) (f' : obj X ⟶ obj Y)
  (comm : cofibrant_objects.forget.map f' ≫ p Y = p X ≫ f) :
  map_π f = cofibrant_objects.L.map f' :=
begin
  haveI : is_cofibrant (obj X).1 := (obj X).2.some,
  let P := (path_object_exists (obj Y).1).some,
  let C := (cylinder_exists (obj X).1).some,
  apply category_theory.quotient.sound,
  refine cofibrant_objects.right_ho_trans_closure.right_homotopy ⟨P, nonempty.intro _⟩,
  apply P.right_homotopy_of_left_homotopy C,
  let Sq := square.mk'' (C.to_precylinder.ι) (p Y) (coprod.desc (map.Sq_lift f) f') (C.σ ≫ (p X) ≫ f) _, swap,
  { ext,
    { simpa only [precylinder.ι, coprod.desc_comp, coprod.inl_desc, ← assoc, C.σd₀, id_comp]
        using map.Sq_lift_comm f, },
    { simpa only [precylinder.ι, coprod.desc_comp, coprod.inr_desc, ← assoc, C.σd₁, id_comp]
        using comm, }, },
  let hSq := (CM4a (Sq.left) (Sq.right) C.cof_ι (triv_fib_p Y)).sq_has_lift,
  let l := (hSq Sq.hom).exists_lift.some,
  have eq₀ := congr_arg ((λ (f : limits.coprod _ _ ⟶ _), limits.coprod.inl ≫ f)) l.fac_left,
  have eq₁ := congr_arg ((λ (f : limits.coprod _ _ ⟶ _), limits.coprod.inr ≫ f)) l.fac_left,
  simp only [precylinder.ι, coprod.desc_comp, coprod.inl_desc, coprod.inr_desc, square.mk''_left_hom, square.mk''_hom_left] at eq₀ eq₁,
  exact
  { h := l.lift,
    h₀ := eq₀,
    h₁ := eq₁, },
end

def functor_π : C ⥤ cofibrant_objects.π C :=
{ obj := obj_π,
  map := λ X Y f, map_π f,
  map_id' := λ X, by simpa only [map_π_eq (𝟙 X) (𝟙 _) (by erw [id_comp, comp_id])],
  map_comp' :=  λ X Y Z f g, begin
    erw map_π_eq (f ≫ g) (map.Sq_lift f ≫ map.Sq_lift g), swap,
    { have foo := map.Sq_lift_comm g,
      erw [← assoc, ← map.Sq_lift_comm f, assoc, assoc, ← map.Sq_lift_comm g],
      refl, },
    erw functor.map_comp,
    refl,
  end }

variable (C)

@[derive category]
def localization := induced_category (cofibrant_objects.fibrant_replacement.localization C) obj

variable {C}

def underlying_object (X : localization C) : C := X

@[derive full, derive faithful]
def R : localization C ⥤ cofibrant_objects.fibrant_replacement.localization C := induced_functor _

def L : C ⥤ localization C :=
{ obj := id,
  map := λ X Y f, (cofibrant_objects.fibrant_replacement.L_π).map (functor_π.map f),
  map_id' := λ X, by simpa only [category_theory.functor.map_id],
  map_comp' := λ X Y Z f g, by simpa only [category_theory.functor.map_comp], }

def L' : C ⥤ cofibrant_objects.fibrant_replacement.localization C := L ⋙ R

lemma L'_eq : (L' : C ⥤ _) = functor_π ⋙ cofibrant_objects.fibrant_replacement.L_π :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    simpa only [eq_to_hom_refl, comp_id, id_comp], },
  { intro X,
    refl, },
end

namespace universal_property

lemma inverts_W : (W : arrow_class C).is_inverted_by L := begin
  rintro ⟨w, hw⟩,
  suffices : is_iso (L'.map w.hom),
  { haveI : is_iso ((induced_functor obj).map (L.map w.hom)) := this,
    exact is_iso_of_reflects_iso (L.map w.hom) (induced_functor _), },
  apply cofibrant_objects.fibrant_replacement.L_π_inverts_W,
  apply CM2.of_comp_right _ (p w.right),
  { exact (triv_fib_p w.right).2, },
  { erw map.Sq_lift_comm w.hom,
    apply CM2.of_comp,
    { exact (triv_fib_p w.left).2, },
    { convert hw,
      exact arrow.mk_eq w, }, },
end

lemma inclusion_comp_L_inverts_W : (cofibrant_objects.W : arrow_class (cofibrant_objects C)).is_inverted_by (cofibrant_objects.inclusion ⋙ L) :=
begin
  rintro ⟨w, hw⟩,
  dsimp [arrow.is_inverted_by],
  convert @inverts_W C _ _ ⟨arrow.mk w.hom, hw⟩,
end

def L_cof : cofibrant_objects.fibrant_replacement.localization C ⥤ localization C :=
cofibrant_objects.fibrant_replacement.universal_property.lift (cofibrant_objects.inclusion ⋙ L)
inclusion_comp_L_inverts_W

def L_cof_fac : cofibrant_objects.fibrant_replacement.L ⋙ (L_cof : _ ⥤ localization C) =
  cofibrant_objects.inclusion ⋙ L :=
cofibrant_objects.fibrant_replacement.universal_property.fac (cofibrant_objects.inclusion ⋙ L)
    inclusion_comp_L_inverts_W

def G₁ {D : Type*} [category D]
  (G : C ⥤ D)
  (hG : (W : arrow_class C).is_inverted_by G) :
  cofibrant_objects C ⥤ D :=
cofibrant_objects.inclusion ⋙ G

def G₁_inverts_W {D : Type*} [category D]
  (G : C ⥤ D)
  (hG : (W : arrow_class C).is_inverted_by G) :
  (cofibrant_objects.W : arrow_class (cofibrant_objects C)).is_inverted_by (G₁ G hG) :=
begin
  rintro ⟨w, hw⟩,
  let w' : w.left.1 ⟶ w.right.1 := w.hom,
  exact hG ⟨w', hw⟩,
end

def G₂ {D : Type*} [category D]
  (G : C ⥤ D)
  (hG : (W : arrow_class C).is_inverted_by G) :
  cofibrant_objects.fibrant_replacement.localization C ⥤ D :=
cofibrant_objects.fibrant_replacement.universal_property.lift (G₁ G hG) (G₁_inverts_W G hG)

@[simps]
def lift {D : Type*} [category D]
  (G : C ⥤ D)
  (hG : (W : arrow_class C).is_inverted_by G) :
  localization C ⥤ D :=
begin
  haveI : Π (X : localization C), is_iso (G.map (p X)) :=
  λ X, hG ⟨arrow.mk (p X), (triv_fib_p X).2⟩,
  exact
  { obj := G.obj,
    map := λ X Y f, inv (G.map (p X)) ≫ (G₂ G hG).map (R.map f) ≫ G.map (p Y),
    map_id' := λ X, by erw [category_theory.functor.map_id, id_comp, is_iso.inv_hom_id],
    map_comp' := λ X Y Z f g , begin
      slice_rhs 3 4 { rw is_iso.hom_inv_id, },
      slice_rhs 2 4 { simp only [id_comp, ← functor.map_comp], },
    end }
end

lemma fac {D : Type*} [category D]
  (G : C ⥤ D)
  (hG : (W : arrow_class C).is_inverted_by G) : L ⋙ lift G hG = G :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    have G₁_fac := cofibrant_objects.fibrant_replacement.universal_property.fac (G₁ G hG) (G₁_inverts_W G hG),
    have h := functor.congr_hom G₁_fac (map.Sq_lift f),
    simp only [eq_to_hom_refl, id_comp, comp_id] at ⊢ h,
    simp only [functor.comp_map, lift_map] at ⊢ h,
    erw h,
    dsimp [G₁],
    erw [← G.map_comp, map.Sq_lift_comm f, G.map_comp, ← assoc, is_iso.inv_hom_id, id_comp], },
  { intro X,
    refl, },
end

lemma compatibility_p_L {X Y : C} (f : obj X ⟶ obj Y) :
L.map (p X) ≫ cofibrant_objects.fibrant_replacement.L.map f  =
  L.map (cofibrant_objects.inclusion.map f) ≫ L.map (p Y) :=
begin
  let p' : Π (Z : C), (_ : C) ⟶ ( _ : C) := λ Z, p (obj Z).1,
  have compat : Π (Z : C), cofibrant_objects.fibrant_replacement.L.map (p' Z) = L.map (p Z) := λ Z, begin
    dsimp only [L, functor_π],
    erw (map_π_eq (p Z) (p' Z) rfl),
    refl,
  end,
  have hf := map.Sq_lift_comm (cofibrant_objects.inclusion.map f),
  have h := functor.congr_map (cofibrant_objects.fibrant_replacement.L) hf,
  repeat { erw [functor.map_comp] at h, },
  simpa only [← compat] using h.symm,
end

def p' (X : localization C) : _ ⟶ underlying_object X := p (underlying_object X)

lemma compatibility_p_L' {X Y : localization C} (f : X ⟶ Y) :
  L.map (p' X) ≫ f = L_cof.map (R.map f) ≫ L.map (p' Y) :=
begin
  rcases CM5a (arrow.mk (terminal.from (underlying_object Y))) with ⟨Z', i', q, fac, hi, hq⟩,
  let Z : localization C := Z',
  let j : Y ⟶ Z := L.map i',
  haveI : is_iso j := @inverts_W C _ _ ⟨arrow.mk i', hi.2⟩,
  simp only [← cancel_mono j, assoc],
  haveI : is_fibrant (obj_π Z').as.1 := ⟨_⟩, swap,
  { convert fib_comp_stable _ _ _ (p Z') (terminal.from _) (triv_fib_p Z').1 (by convert hq), },
  cases (cofibrant_objects.fibrant_replacement.L_π_map_bijective_when_target_is_fibrant (obj_π (underlying_object X)) (obj_π Z')).2 (f ≫ j)
    with ψ hψ,
  cases category_theory.quotient.functor_map_surj _ _ _ ψ with φ hφ',
  have hφ : cofibrant_objects.fibrant_replacement.L.map φ = f ≫ j,
  { simp only at hφ' hψ,
    rw [← hψ, ← hφ'],
    refl, },
  erw [← hφ, compatibility_p_L φ],
  rw [show j = L.map i', by refl],
  conv_rhs { erw [← L.map_comp, ← map.Sq_lift_comm, L.map_comp], },
  rw ← assoc,
  congr' 1,
  have eqφ := functor.congr_hom L_cof_fac φ,
  have eqj := functor.congr_hom L_cof_fac (map.Sq_lift i'),
  dsimp at eqφ eqj,
  erw [hφ, id_comp, comp_id] at eqφ,
  erw [id_comp, comp_id] at eqj,
  erw [← eqφ, L_cof.map_comp, ← eqj],
  congr' 1,
end

lemma uniq' {E : Type*} [category E]
  (G : localization C ⥤ E) :
  G = lift (L ⋙ G) (M.W.is_inverted_by_of_comp L G inverts_W) :=
begin
  haveI : Π (X : localization C), is_iso (L.map (p' X)) :=
    λ X , @inverts_W C _ _ ⟨arrow.mk (p X), (triv_fib_p X).2⟩,
  haveI : Π (X : localization C), is_iso ((L ⋙ G).map (p' X)) := λ X, by { dsimp, apply_instance, },
  have h := cofibrant_objects.fibrant_replacement.universal_property.uniq
    (G₂ (L ⋙ G) (M.W.is_inverted_by_of_comp L G inverts_W)) (L_cof ⋙ G) _, swap,
  { erw [← functor.assoc],
    erw cofibrant_objects.fibrant_replacement.universal_property.fac,
    erw cofibrant_objects.fibrant_replacement.universal_property.fac,
    dsimp [G₁],
    erw [functor.assoc], },
  apply category_theory.functor.ext,
  { intros X Y f,
    simp only [eq_to_hom_refl, comp_id, id_comp],
    dsimp only [lift],
    rw ← cancel_epi ((L ⋙ G).map (p' X)),
    slice_rhs 1 2 { erw is_iso.hom_inv_id, },
    erw [functor.congr_hom h (R.map f), id_comp, id_comp, comp_id],
    dsimp,
    simp only [← G.map_comp],
    congr' 1,
    apply compatibility_p_L', },
  { intro X,
    refl, },
end

lemma uniq {E : Type*} [category E]
  (G₁ G₂ : localization C ⥤ E)
  (h₁₂ : L ⋙ G₁ = L ⋙ G₂) : G₁ = G₂ :=
by { rw [uniq' G₁, uniq' G₂], congr', }

def fixed_target {E : Type*} [category E] :
  arrow_class.is_strict_localization_fixed_target (W : arrow_class C) L E :=
{ inverts_W := inverts_W,
  lift := lift,
  fac := fac,
  uniq := uniq }

@[simps]
def nat_trans_p_cof :
  L_cof ⋙ R ⟶
  𝟭 (cofibrant_objects.fibrant_replacement.localization C) :=
cofibrant_objects.fibrant_replacement.is_strict_localization.nat_trans_extension
{ app := λ X, cofibrant_objects.fibrant_replacement.L.map (p X.1),
  naturality' := λ X Y f, begin
    have hf := map.Sq_lift_comm (cofibrant_objects.inclusion.map f),
    have h := functor.congr_map cofibrant_objects.fibrant_replacement.L hf,
    repeat { erw [cofibrant_objects.fibrant_replacement.L.map_comp] at h, },
    dsimp only [functor.comp_map, functor.id],
    erw ← h,
    congr' 1,
    conv_lhs { congr, erw [← functor.comp_map], },
    erw [functor.congr_hom L_cof_fac, id_comp, comp_id],
    refl,
  end }

instance : is_iso (nat_trans_p_cof : L_cof ⋙ R ⟶
  𝟭 (cofibrant_objects.fibrant_replacement.localization C)) :=
begin
  apply nat_iso.is_iso_of_is_iso_app nat_trans_p_cof,
  intro X,
  simp only [nat_trans_p_cof_app],
  erw arrow_class.is_strict_localization.nat_trans_extension.app_eq,
  exact @cofibrant_objects.fibrant_replacement.universal_property.inverts_W C _ _
    ⟨arrow.mk (@p' C _ _ X.1), (@triv_fib_p C _ _ X.1).2⟩,
end

def nat_iso_p_cof : L_cof ⋙ R ≅
  𝟭 (cofibrant_objects.fibrant_replacement.localization C) := as_iso nat_trans_p_cof

lemma L_cof_fully_faithful (X Y : cofibrant_objects.fibrant_replacement.localization C) :
  function.bijective (λ (f : X ⟶ Y), L_cof.map f) :=
begin
  haveI : faithful (L_cof ⋙ (R : localization C ⥤ _)) := faithful.of_iso nat_iso_p_cof.symm,
  haveI : full (L_cof ⋙ (R : localization C ⥤ _)) := full.of_iso nat_iso_p_cof.symm,
  split,
  { intros f₀ f₁ eq,
    exact (L_cof ⋙ R).map_injective eq, },
  { intros g,
    use (L_cof ⋙ R).preimage (R.map g),
    simp only [functor.comp_map],
    refine R.map_injective _,
    apply (L_cof ⋙ R).image_preimage, },
end

end universal_property

def is_strict_localization : arrow_class.is_strict_localization M.W L :=
arrow_class.is_strict_localization.mk' _ _
  universal_property.fixed_target universal_property.fixed_target

lemma L_map_surjective (X Y : C) [hX : is_cofibrant X] [hY : is_fibrant Y] : function.surjective (λ (f : X ⟶ Y), L.map f) :=
begin
  intro g,
  let X' : cofibrant_objects C := ⟨X, nonempty.intro hX⟩,
  let Y' := obj Y,
  haveI : is_iso (L.map (p Y)) := universal_property.inverts_W ⟨arrow.mk (p Y), (triv_fib_p Y).2⟩,
  haveI : is_fibrant (cofibrant_objects.L.obj Y').as.1 := ⟨by convert fib_comp_stable _ _ _ (p Y) (terminal.from _) ((triv_fib_p Y).1) hY.fib⟩,
  cases (universal_property.L_cof_fully_faithful X' Y').2 (g ≫ inv (L.map (p Y))) with f₀ hf₀,
  cases (cofibrant_objects.fibrant_replacement.L_π_map_bijective_when_target_is_fibrant (cofibrant_objects.L.obj X') (cofibrant_objects.L.obj Y')).2 f₀
    with f₁ hf₁,
  cases category_theory.quotient.functor_map_surj _ _ _ f₁ with f₂ hf₂,
  use f₂ ≫ p Y,
  simp only at hf₂ hf₁ hf₀ ⊢,
  erw [← comp_id g, ← is_iso.inv_hom_id (L.map (p Y)), ← assoc, ← hf₀, ← hf₁, ← hf₂, L.map_comp],
  congr' 1,
  convert functor.congr_hom universal_property.L_cof_fac.symm f₂,
  erw [id_comp, comp_id],
  refl,
end

lemma nonempty_right_homotopy_iff_of_comp_left_triv_cof {X X' Y : C} [hX : is_cofibrant X]
  [hX' : is_cofibrant X'] [hY : is_fibrant Y] (P : path_object Y) (g : X ⟶ X') (hg : arrow.mk g ∈ (triv_cof : arrow_class C))
    (f₀ f₁ : X' ⟶ Y) :
    nonempty (P.pre.right_homotopy f₀ f₁) ↔ nonempty (P.pre.right_homotopy (g ≫ f₀) (g ≫ f₁)) :=
begin
  split,
  { intro h,
    exact nonempty.intro (h.some.comp_left g), },
  { intro h,
    exact nonempty.intro (P.homotopy_extension f₀ f₁ g hg h.some), },
end

lemma nonempty_right_homotopy_iff_of_comp_left {X X' Y : C} [hX : is_cofibrant X]
  [hX' : is_cofibrant X'] [hY : is_fibrant Y] (P : path_object Y) (w : X ⟶ X') (hw : arrow.mk w ∈ (W : arrow_class C))
    (f₀ f₁ : X' ⟶ Y) :
    nonempty (P.pre.right_homotopy f₀ f₁) ↔ nonempty (P.pre.right_homotopy (w ≫ f₀) (w ≫ f₁)) :=
begin
  split,
  { intro h,
    exact nonempty.intro (h.some.comp_left w), },
  { intro h,
    let brown_fac := (exists_brown_factorisation_W_between_cofibrant_objects w hw).some,
    haveI : is_cofibrant brown_fac.Z := ⟨by convert cof_comp_stable _ _ _ (initial.to _) (brown_fac.i) hX.cof brown_fac.triv_cof_i.1⟩,
    erw [brown_fac.fac₁, assoc, assoc] at h,
    rw ← nonempty_right_homotopy_iff_of_comp_left_triv_cof P brown_fac.i brown_fac.triv_cof_i at h,
    have h' := h.some.comp_left brown_fac.s,
    erw [← assoc, ← assoc, brown_fac.fac₂, id_comp, id_comp] at h',
    exact nonempty.intro h', },
end

lemma L_map_eq_iff' {X Y : C} [hX : is_cofibrant X] [hY : is_fibrant Y] (P : path_object Y) (f₀ f₁ : X ⟶ Y) :
  L.map f₀ = L.map f₁ ↔ nonempty (P.pre.right_homotopy f₀ f₁) :=
begin
  split,
  { intro h,
    haveI : is_cofibrant (obj X).1 := (obj X).2.some,
    rw nonempty_right_homotopy_iff_of_comp_left P (p X) (triv_fib_p X).2 f₀ f₁,
    dsimp only [L] at h,
    haveI hY' : is_fibrant (obj Y).1,
    { refine ⟨_⟩,
      convert fib_comp_stable _ _ _ (p Y) (terminal.from _) (triv_fib_p Y).1 hY.fib, },
    haveI : is_fibrant (functor_π.obj Y).as.val := hY',
    have h' := (cofibrant_objects.fibrant_replacement.L_π_map_bijective_when_target_is_fibrant _ _ ).1 h,
    dsimp [functor_π, map_π] at h',
    cases cylinder_exists (obj X).1 with C hC,
    let H := ((cofibrant_objects.L_map_eq_iff_when_target_is_fibrant C (map.Sq_lift f₀) (map.Sq_lift f₁)).mp h').some,
    let H' := H.comp_right (p Y),
    repeat { erw map.Sq_lift_comm at H', },
    exact nonempty.intro (P.right_homotopy_of_left_homotopy C H'), },
  { intro h,
    simp only [← h.some.h₀, ← h.some.h₁, L.map_comp],
    congr' 1,
    haveI : is_iso (L.map P.pre.σ') :=
      @universal_property.inverts_W C _ _ ⟨arrow.mk P.pre.σ', P.pre.Wσ'⟩,
    rw ← cancel_epi (L.map P.pre.σ'),
    simp only [← L.map_comp, P.pre.σd₀', P.pre.σd₁'], },
end

end cofibrant_replacement

namespace fundamental_lemma

lemma surjective (X Y : C) [hX : is_cofibrant X] [hY : is_fibrant Y] :
  function.surjective (λ (f : X ⟶ Y), Q.map f) :=
begin
  let F : M.W.localization ⥤ _ := arrow_class.localization.lift cofibrant_replacement.L cofibrant_replacement.is_strict_localization.inverts_W,
  haveI : is_equivalence F := cofibrant_replacement.is_strict_localization.is_equivalence,
  have hF : faithful F := infer_instance,
  intro f,
  cases cofibrant_replacement.L_map_surjective X Y (F.map f) with g hg,
  use g,
  simp only at ⊢ hg,
  apply hF.map_injective',
  rw ← hg,
  simpa only [id_comp, comp_id, eq_to_hom_refl] using functor.congr_hom (arrow_class.localization.fac cofibrant_replacement.L cofibrant_replacement.is_strict_localization.inverts_W) g,
end

lemma eq_iff' {X Y : C} [hX : is_cofibrant X] [hY : is_fibrant Y] (P : path_object Y) (f₀ f₁ : X ⟶ Y) :
  Q.map f₀ = Q.map f₁ ↔ nonempty (P.pre.right_homotopy f₀ f₁) :=
begin
  let F : M.W.localization ⥤ _ := arrow_class.localization.lift cofibrant_replacement.L cofibrant_replacement.is_strict_localization.inverts_W,
  haveI : is_equivalence F := cofibrant_replacement.is_strict_localization.is_equivalence,
  have hF : faithful F := infer_instance,
  suffices : Q.map f₀ = Q.map f₁ ↔ cofibrant_replacement.L.map f₀ = cofibrant_replacement.L.map f₁,
  { calc Q.map f₀ = Q.map f₁ ↔ cofibrant_replacement.L.map f₀ = cofibrant_replacement.L.map f₁ : this
    ... ↔ nonempty (P.pre.right_homotopy f₀ f₁) : cofibrant_replacement.L_map_eq_iff' P f₀ f₁, },
  have eq : Q ⋙ F = cofibrant_replacement.L := arrow_class.localization.fac cofibrant_replacement.L cofibrant_replacement.is_strict_localization.inverts_W,
  have eq₀ := functor.congr_hom eq f₀,
  have eq₁ := functor.congr_hom eq f₁,
  erw [id_comp, comp_id, functor.comp_map] at eq₀ eq₁,
  erw [← eq₀, ← eq₁],
  split,
  { intro h,
    rw h, },
  { intro h,
    apply hF.map_injective',
    exact h, },
end

lemma eq_iff {X Y : C} [hX : is_cofibrant X] [hY : is_fibrant Y] (Cyl : cylinder X) (f₀ f₁ : X ⟶ Y) :
  Q.map f₀ = Q.map f₁ ↔ nonempty (Cyl.to_precylinder.left_homotopy f₀ f₁) :=
begin
  cases path_object_exists Y with P hP,
  calc Q.map f₀ = Q.map f₁ ↔ nonempty (P.pre.right_homotopy f₀ f₁) : eq_iff' P f₀ f₁
  ... ↔ nonempty (Cyl.to_precylinder.left_homotopy f₀ f₁) : (left_homotopy_iff_right_homotopy Cyl P f₀ f₁).symm,
end

end fundamental_lemma

end model_category

end algebraic_topology
