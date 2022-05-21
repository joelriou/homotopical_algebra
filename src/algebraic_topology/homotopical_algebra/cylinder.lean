/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.homotopical_algebra.cofibrant
import tactic.equiv_rw

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open algebraic_topology
open opposite

variables {C : Type*} [hC : category C] [M : model_category C]
include M

namespace algebraic_topology

namespace model_category

structure precylinder (A : C) :=
(I : C) (d₀ d₁: A ⟶ I) (σ : I ⟶ A)
(σd₀ : d₀ ≫ σ = 𝟙 A) (σd₁ : d₁ ≫ σ = 𝟙 A)
(Wσ : arrow.mk σ ∈ (W : arrow_class C))

namespace precylinder

@[simp]
def ι {A : C} (P : precylinder A) := coprod.desc P.d₀ P.d₁

@[simp]
def cof_ι {A : C} (P : precylinder A) := arrow.mk P.ι ∈ (cof : arrow_class C)

@[simps]
def change_I {A : C} (P : precylinder A) {Z : C}
  {f : P.I ⟶ Z} {g : Z ⟶ A} (fac : P.σ = f ≫ g)
  (hf : arrow.mk f ∈ W) : precylinder A :=
{ I := Z,
  d₀ := P.d₀ ≫ f,
  d₁ := P.d₁ ≫ f,
  σ := g,
  σd₀ := by rw [assoc, ← fac, P.σd₀],
  σd₁ := by rw [assoc, ← fac, P.σd₁],
  Wσ := begin
    apply CM2.of_comp_left f g hf,
    convert P.Wσ,
    exact fac.symm,
  end }

end precylinder

structure cylinder (A : C) extends precylinder A :=
(cof_ι : to_precylinder.cof_ι)

lemma cylinder_exists (A : C) : ∃ (Cyl : cylinder A), arrow.mk Cyl.σ ∈ (fib : arrow_class C) :=
begin
  rcases CM5b (arrow.mk (coprod.desc (𝟙 A) (𝟙 A))) with ⟨Z, i, p, fac, ⟨hi, hp⟩⟩,
  let Cyl : cylinder A :=
  { I := Z,
    d₀ := coprod.inl ≫ i,
    d₁ := coprod.inr ≫ i,
    σ := p,
    σd₀ := by rw [assoc, ← fac, arrow.mk_hom, coprod.inl_desc],
    σd₁ := by rw [assoc, ← fac, arrow.mk_hom, coprod.inr_desc],
    Wσ := hp.2,
    cof_ι := begin
      dsimp only [precylinder.cof_ι],
      convert hi,
      ext,
      { simp only [precylinder.ι, coprod.inl_desc], },
      { simp only [precylinder.ι, coprod.inr_desc], },
     end },
  use [Cyl, hp.1],
end

def pre_path_object (A : C) := precylinder (opposite.op A)
def path_object (A : C) := cylinder (opposite.op A)

namespace pre_path_object

variables {B : C} (P : pre_path_object B)
def I' : C := opposite.unop P.I
def d₀' : P.I' ⟶ B := P.d₀.unop
def d₁' : P.I' ⟶ B := P.d₁.unop
def σ' : B ⟶ P.I' := P.σ.unop
def σd₀' : P.σ' ≫ P.d₀' = 𝟙 B := by { apply quiver.hom.op_inj, exact P.σd₀, }
def σd₁' : P.σ' ≫ P.d₁' = 𝟙 B := by { apply quiver.hom.op_inj, exact P.σd₁, }
def Wσ' : arrow.mk P.σ' ∈ W := P.Wσ
@[simp]
def π := prod.lift P.d₀' P.d₁'

def fib_π := arrow.mk P.π ∈ (fib : arrow_class C)

lemma fib_π_iff_cof_ι_op {B : C} (P : pre_path_object B) :
  P.fib_π ↔ P.cof_ι :=
cof_iff_of_arrow_iso _ _ (arrow.iso_op_prod_lift P.d₀' P.d₁')

def change_I' {B : C} (P : pre_path_object B) {Z : C}
  {f : B ⟶ Z} {g : Z ⟶ P.I'} (fac : P.σ' = f ≫ g)
  (hg : arrow.mk g ∈ W) : pre_path_object B :=
begin
  have h : P.σ = g.op ≫ f.op := by simpa only [← op_comp, ← fac],
  apply P.change_I h,
  exact (arrow_class.mem_op_iff W (arrow.mk g.op)).mp hg,
end

end pre_path_object

variable {M}

namespace precylinder

def Wd₀ {A : C} (P : precylinder A) : arrow.mk P.d₀ ∈ W :=
begin
  apply CM2.of_comp_right P.d₀ P.σ P.Wσ,
  rw P.σd₀,
  apply W_contains_iso,
  exact is_iso.of_iso (iso.refl A),
end

def Wd₁ {A : C} (P : precylinder A) : arrow.mk P.d₁ ∈ W :=
begin
  apply CM2.of_comp_right P.d₁ P.σ P.Wσ,
  rw P.σd₁,
  apply W_contains_iso,
  exact is_iso.of_iso (iso.refl A),
end

structure left_homotopy {A B : C} (P : precylinder A) (f₀ f₁ : A ⟶ B) :=
(h : P.I ⟶ B) (h₀ : P.d₀ ≫ h = f₀) (h₁ : P.d₁ ≫ h = f₁)

def symm {A : C} (P : precylinder A) : precylinder A :=
{ I := P.I,
  d₀ := P.d₁,
  d₁ := P.d₀,
  σ := P.σ,
  σd₀ := P.σd₁,
  σd₁ := P.σd₀,
  Wσ := P.Wσ, }

def arrow_iso_ι_symm {A : C} (P : precylinder A) :
  arrow.mk P.ι ≅ arrow.mk P.symm.ι :=
begin
  refine arrow.mk_iso (coprod.braiding _ _) (by refl) _,
  dsimp,
  simpa only [coprod.desc_comp, coprod.inr_desc, coprod.inl_desc, comp_id],
end

end precylinder

namespace cylinder

def symm {A : C} (Cyl : cylinder A) : cylinder A :=
{ to_precylinder := Cyl.to_precylinder.symm,
  cof_ι := (cof_iff_of_arrow_iso _ _ Cyl.to_precylinder.arrow_iso_ι_symm).mp Cyl.cof_ι, }

def cof_d₀ {A : C} [hA : is_cofibrant A] (Cyl : cylinder A) :
  arrow.mk Cyl.d₀ ∈ cof :=
begin
  have h := cof_co_bc_stable.for_coprod_inl A A hA.cof,
  convert cof_comp_stable _ _ _ _ _ h Cyl.cof_ι,
  simp only [precylinder.ι, coprod.inl_desc],
end

def cof_d₁ {A : C} [hA : is_cofibrant A] (Cyl : cylinder A) :
  arrow.mk Cyl.d₁ ∈ cof :=
begin
  have h := cof_co_bc_stable.for_coprod_inr A A hA.cof,
  convert cof_comp_stable _ _ _ _ _ h Cyl.cof_ι,
  erw coprod.inr_desc,
end

def trans {A : C} [is_cofibrant A] (Cyl : cylinder A) (Cyl' : cylinder A) : cylinder A :=
{ I := pushout Cyl.d₁ Cyl'.d₀,
  d₀ := Cyl.d₀ ≫ pushout.inl,
  d₁ := Cyl'.d₁ ≫ pushout.inr,
  σ := pushout.desc Cyl.σ Cyl'.σ (by rw [Cyl.σd₁, Cyl'.σd₀]),
  σd₀ := by { rw [category.assoc, pushout.inl_desc], exact Cyl.σd₀, },
  σd₁ := by { rw [category.assoc, pushout.inr_desc], exact Cyl'.σd₁, },
  cof_ι := begin
    dsimp only [precylinder.cof_ι],
    convert cof_comp_stable _ _ _ (coprod.map Cyl.d₀ (𝟙 A)) (coprod.desc pushout.inl (Cyl'.d₁ ≫ pushout.inr)) _ _,
    { simp only [precylinder.ι, coprod.map_desc, id_comp], },
    { rw cof_equals_llp_triv_fib,
      apply (triv_fib : arrow_class C).is_stable_by_binary_coproduct_of_llp_with (arrow.mk _) (arrow.mk _),
      { rw ← cof_equals_llp_triv_fib,
        exact Cyl.cof_d₀, },
      { apply arrow_class.contains_isomorphisms_of_llp_with,
        exact is_iso.of_iso (iso.refl A), }, },
    { let φ : _ ⟶ pushout Cyl.d₁ Cyl'.d₀ :=
        coprod.desc pushout.inl (Cyl'.d₁ ≫ pushout.inr),
      let Sq₂ := square.mk'' Cyl'.to_precylinder.ι φ (coprod.map Cyl.d₁ (𝟙 A)) pushout.inr begin
        ext,
        { simp only [precylinder.ι, coprod.map_desc, coprod.inl_desc, coprod.desc_comp, pushout.condition], },
        { simp only [precylinder.ι, coprod.map_desc, coprod.inr_desc, coprod.desc_comp, id_comp], },
      end,
      refine cof_co_bc_stable Sq₂ _ Cyl'.cof_ι,
      let hSq₁ := (coprod_inl_with_identity_is_cocartesian (arrow.mk Cyl.d₁) A).flip,
      apply Sq₂.is_cocartesian_of_top_comp _ (eq_to_iso (by tidy))  hSq₁,
      { convert pushout_square_is_cocartesian Cyl.to_precylinder.d₁ Cyl'.to_precylinder.d₀,
        dsimp [φ, arrow.binary_coproduct_cofan],
        tidy, }, }
  end,
  Wσ := begin
    apply CM2.of_comp_left (Cyl.d₀ ≫ pushout.inl ),
    { apply triv_cof_contains_W,
      apply triv_cof_comp_stable,
      { exact ⟨Cyl.cof_d₀, Cyl.to_precylinder.Wd₀⟩, },
      { apply triv_cof_co_bc_stable.for_pushout_inl,
        exact ⟨Cyl'.cof_d₀, Cyl'.to_precylinder.Wd₀⟩, } },
    { rw [assoc, pushout.inl_desc, Cyl.σd₀],
      apply W_contains_iso,
      exact is_iso.of_iso (iso.refl A), },
  end, }

end cylinder

namespace precylinder

namespace left_homotopy

def refl {A B : C} {P : precylinder A} (f : A ⟶ B) : P.left_homotopy f f :=
{ h := P.σ ≫ f,
  h₀ := by rw [← assoc, P.σd₀, id_comp],
  h₁ := by rw [← assoc, P.σd₁, id_comp], }

def symm {A B : C} (P : precylinder A) {f g : A ⟶ B} (H : P.left_homotopy f g) :
  P.symm.left_homotopy g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

def trans {A B : C} [is_cofibrant A] {P P' : cylinder A} {f₁ f₂ f₃ : A ⟶ B}
  (H₁ : P.to_precylinder.left_homotopy f₁ f₂) (H₂ : P'.to_precylinder.left_homotopy f₂ f₃) :
    (P.trans P').to_precylinder.left_homotopy f₁ f₃ :=
{ h := pushout.desc H₁.h H₂.h (by rw [H₁.h₁, H₂.h₀]),
  h₀ := by erw [category.assoc, pushout.inl_desc, H₁.h₀],
  h₁ := by erw [category.assoc, pushout.inr_desc, H₂.h₁], }

def comp_right {A B E : C} {P : precylinder A} {f f' : A ⟶ B}
  (H : P.left_homotopy f f') (g : B ⟶ E) : P.left_homotopy (f ≫ g) (f' ≫ g) :=
{ h := H.h ≫ g,
  h₀ := by rw [← assoc, H.h₀],
  h₁ := by rw [← assoc, H.h₁], }

end left_homotopy

end precylinder

namespace pre_path_object

def Wd₀ {B : C} (P : pre_path_object B) : arrow.mk P.d₀' ∈ W := P.Wd₀
def Wd₁ {B : C} (P : pre_path_object B) : arrow.mk P.d₁' ∈ W := P.Wd₁

structure right_homotopy {A B : C} (P : pre_path_object B) (f₀ f₁ : A ⟶ B) :=
(h : A ⟶ P.I') (h₀ : h ≫ P.d₀' = f₀) (h₁ : h ≫ P.d₁' = f₁)

def symm {B : C} (P : pre_path_object B) : pre_path_object B := P.symm

def right_homotopy_of_map_to {A B : C} (P : pre_path_object B) (f : A ⟶ P.I') :
  P.right_homotopy (f ≫ P.d₀') (f ≫ P.d₁') :=
{ h := f,
  h₀ := rfl,
  h₁ := rfl, }

namespace right_homotopy

def refl {A B : C} {P : pre_path_object B} (f : A ⟶ B) : P.right_homotopy f f :=
{ h := f ≫ P.σ',
  h₀ := by { rw [assoc, P.σd₀', comp_id], },
  h₁ := by { rw [assoc, P.σd₁', comp_id], }, }

def symm {A B : C} {P : pre_path_object B} {f g : A ⟶ B} (H : P.right_homotopy f g) :
  P.symm.right_homotopy g f :=
{ h := H.h,
  h₀ := H.h₁,
  h₁ := H.h₀ }

def comp_left {A B E : C} {P : pre_path_object E} {g g' : B ⟶ E}
  (H : P.right_homotopy g g') (f : A ⟶ B) : P.right_homotopy (f ≫ g) (f ≫ g') :=
{ h := f ≫ H.h,
  h₀ := by rw [assoc, H.h₀],
  h₁ := by rw [assoc, H.h₁], }

end right_homotopy

end pre_path_object

namespace path_object

abbreviation pre {B : C} (P : path_object B) : pre_path_object B := P.to_precylinder

def mk {B : C} (P : pre_path_object B) (hP : arrow.mk P.π ∈ fib) :
  path_object B :=
{ to_precylinder := P,
  cof_ι := P.fib_π_iff_cof_ι_op.mp hP, }

end path_object

lemma path_object_exists (B : C) : ∃ (P : path_object B), arrow.mk P.pre.σ' ∈ (cof : arrow_class C) :=
by { cases cylinder_exists (op B) with C hC, use [C, hC], }

namespace path_object

def symm {B : C} (P : path_object B) : path_object B := P.symm

@[protected]
def op {B : C} (P : path_object B) : cylinder _ := P

def fib_π {B : C} (P : path_object B) : arrow.mk P.pre.π ∈ fib :=
P.pre.fib_π_iff_cof_ι_op.mpr P.cof_ι

def fib_d₀' {B : C} [hB : is_fibrant B] (P : path_object B) :
  arrow.mk P.pre.d₀' ∈ fib :=
begin
  haveI : is_cofibrant (op B) := (is_fibrant_equiv_op B).to_fun hB,
  exact P.cof_d₀,
end

def fib_d₁' {B : C} [hB : is_fibrant B] (P : path_object B) :
  arrow.mk P.pre.d₁' ∈ fib :=
begin
  haveI : is_cofibrant (op B) := (is_fibrant_equiv_op B).to_fun hB,
  exact P.cof_d₁,
end

def right_homotopy_of_left_homotopy {A B : C} [is_cofibrant A] (P : path_object B) (Cyl : cylinder A)
  {f₀ f₁ : A ⟶ B} (Hl : Cyl.to_precylinder.left_homotopy f₀ f₁) : P.pre.right_homotopy f₀ f₁ :=
begin
  have foo := Hl.h,
  let sq : arrow.mk Cyl.d₀ ⟶ arrow.mk P.pre.π :=
  { left := f₀ ≫ P.pre.σ',
    right := prod.lift (Cyl.σ ≫ f₀) Hl.h,
    w' := begin
      dsimp [pre_path_object.π],
      ext,
      { erw [assoc, prod.lift_fst, assoc, P.pre.σd₀', comp_id, assoc,
          prod.lift_fst, ← assoc, Cyl.σd₀, id_comp], },
      { simp only [assoc, prod.lift_snd, P.pre.σd₁', comp_id, Hl.h₀], },
    end },
  have h := (CM4b _ _ ⟨Cyl.cof_d₀, Cyl.to_precylinder.Wd₀⟩ P.fib_π).sq_has_lift,
  let l := (h sq).exists_lift.some,
  have hr₀ := congr_arg (λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.fst) l.fac_right,
  have hr₁ := congr_arg (λ (f : _ ⟶ limits.prod _ _), f ≫ limits.prod.snd) l.fac_right,
  dsimp at hr₀ hr₁,
  simp only [prod.comp_lift, prod.lift_snd, prod.lift_fst] at hr₀ hr₁,
  exact
  { h := Cyl.d₁ ≫ l.lift,
    h₀ := by erw [assoc, hr₀, ← assoc, Cyl.σd₁, id_comp],
    h₁ := by { erw [assoc, hr₁, Hl.h₁], }, },
end

@[simps]
def change_I' {B : C} (P : path_object B) {Z : C}
  {f : B ⟶ Z} {g : Z ⟶ P.pre.I'} (fac : P.pre.σ' = f ≫ g)
  (hg : arrow.mk g ∈ (triv_fib : arrow_class C)) : path_object B :=
begin
  let Q := P.pre.change_I' fac hg.2,
  refine path_object.mk Q _,
  dsimp [pre_path_object.change_I', precylinder.change_I],
  convert fib_comp_stable _ _ _ g P.pre.π hg.1 P.fib_π,
  ext;
  { simpa only [pre_path_object.π, prod.comp_lift], },
end

lemma right_homotopy_with_triv_cof_σ'_of_right_homotopy {A B : C} [hA : is_cofibrant A] {f f' : A ⟶ B} (P : path_object B)
  (H : P.pre.right_homotopy f f') : ∃ (P' : path_object B) (H' : P'.pre.right_homotopy f f'), arrow.mk P'.pre.σ' ∈ (triv_cof : arrow_class C) :=
begin
  rcases CM5b (arrow.mk P.pre.σ') with ⟨Z, i, p, fac, ⟨hi, hp⟩⟩,
  let P' := P.change_I' fac hp,
  let Sq := square.mk'' (initial.to _) p (initial.to _) H.h
    (by { dsimp, apply subsingleton.elim, }),
  have hSq := (CM4a Sq.left Sq.right hA.1 hp).sq_has_lift,
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
  use [P', H', ⟨hi, P'.pre.Wσ'⟩],  
end

lemma homotopy_extension_exists {X X' Y : C} (P : path_object Y) (f₀ f₁ : X' ⟶ Y) (i : X ⟶ X') (hi : arrow.mk i ∈ (triv_cof : arrow_class C))
  (H : P.pre.right_homotopy (i ≫ f₀) (i ≫ f₁)) : ∃ (H' : P.pre.right_homotopy f₀ f₁), i ≫ H'.h = H.h :=
begin
  let Sq := square.mk'' i P.pre.π H.h (prod.lift f₀ f₁) _, swap,
  { ext,
    { simp only [pre_path_object.π, prod.comp_lift, prod.lift_fst, H.h₀], },
    { simp only [pre_path_object.π, prod.comp_lift, prod.lift_snd, H.h₁], }, },
  have hSq := (CM4b Sq.left Sq.right hi P.fib_π).sq_has_lift,
  have l := (hSq Sq.hom).exists_lift.some,
  have eq₀ := congr_arg ((λ (f : _ ⟶ prod Y Y), f ≫ limits.prod.fst)) l.fac_right,
  have eq₁ := congr_arg ((λ (f : _ ⟶ prod Y Y), f ≫ limits.prod.snd)) l.fac_right,
  simp only [assoc, pre_path_object.π, prod.lift_fst, prod.lift_snd, square.mk''_right_hom, square.mk''_hom_right] at eq₀ eq₁,
  use
  { h := l.lift,
    h₀ := eq₀,
    h₁ := eq₁, },
  exact l.fac_left,
end

def homotopy_extension {X X' Y : C} (P : path_object Y) (f₀ f₁ : X' ⟶ Y) (i : X ⟶ X') (hi : arrow.mk i ∈ (triv_cof : arrow_class C))
  (H : P.pre.right_homotopy (i ≫ f₀) (i ≫ f₁)) : P.pre.right_homotopy f₀ f₁ :=
(P.homotopy_extension_exists f₀ f₁ i hi H).some

lemma homotopy_extension_compatibility {X X' Y : C} (P : path_object Y) (f₀ f₁ : X' ⟶ Y) (i : X ⟶ X') (hi : arrow.mk i ∈ (triv_cof : arrow_class C))
  (H : P.pre.right_homotopy (i ≫ f₀) (i ≫ f₁)) : i ≫ (P.homotopy_extension f₀ f₁ i hi H).h = H.h :=
(P.homotopy_extension_exists f₀ f₁ i hi H).some_spec

/-- Hirschhorn 7.3.10 -/
lemma homotopy_extension_property_of_cofibrations {X Y Z : C} {P : path_object Z} [is_fibrant Z]
  {i : X ⟶ Y} {g₀ : Y ⟶ Z} {f₁ : X ⟶ Z} (H : P.pre.right_homotopy (i ≫ g₀) f₁) (hi : arrow.mk i ∈ (cof : arrow_class C)):
  ∃ (g₁ : Y ⟶ Z) (H' : P.pre.right_homotopy g₀ g₁) (fac : f₁ = i ≫ g₁), H.h = i ≫ H'.h :=
begin
  let Sq := square.mk'' i P.pre.d₀' H.h g₀ H.h₀,
  have hSq := (CM4a Sq.left Sq.right hi ⟨P.fib_d₀', P.pre.Wd₀⟩).sq_has_lift,
  have l := (hSq Sq.hom).exists_lift.some,
  use l.lift ≫ P.pre.d₁',
  use
  { h := l.lift,
    h₀ := l.fac_right,
    h₁ := rfl,},
  split,
  { erw [← H.h₁, ← assoc, l.fac_left],
    refl, },
  { exact l.fac_left.symm, },
end

end path_object

namespace precylinder

@[protected]
def op {A : C} (P : precylinder A) : pre_path_object (op A) :=
{ I := opposite.op (opposite.op P.I),
  d₀ := P.d₀.op.op,
  d₁ := P.d₁.op.op,
  σ := P.σ.op.op,
  σd₀ := by simpa only [← op_comp, P.σd₀],
  σd₁ := by simpa only [← op_comp, P.σd₁],
  Wσ := P.Wσ, }

end precylinder

namespace cylinder

@[protected]
def op {A : C} (Cyl : cylinder A) : path_object (op A) :=
{ to_precylinder := Cyl.to_precylinder.op,
  cof_ι := begin
    rw ← Cyl.to_precylinder.op.fib_π_iff_cof_ι_op,
    apply (fib_iff_of_arrow_iso _ _ (arrow.iso_prod_lift_op Cyl.to_precylinder.d₀ Cyl.to_precylinder.d₁)).mpr,
    exact Cyl.cof_ι,
  end, }

def left_homotopy_of_right_homotopy {A B : C} [hB : is_fibrant B] (Cyl : cylinder A) (P : path_object B)
  {f₀ f₁ : A ⟶ B} (Hr : P.pre.right_homotopy f₀ f₁) :
  Cyl.to_precylinder.left_homotopy f₀ f₁ :=
begin
  let C' := P.op,
  let P' := Cyl.op,
  let Hl' : C'.to_precylinder.left_homotopy f₀.op f₁.op :=
  { h := Hr.h.op,
    h₀ := quiver.hom.unop_inj Hr.h₀,
    h₁ := quiver.hom.unop_inj Hr.h₁, },
  haveI : is_cofibrant (op B),
  { equiv_rw (is_fibrant_equiv_op B).symm,
    exact hB, },
  let Hr' := P'.right_homotopy_of_left_homotopy C' Hl',
  exact
  { h := Hr'.h.unop,
    h₀ := quiver.hom.op_inj Hr'.h₀,
    h₁ := quiver.hom.op_inj Hr'.h₁, },
end

def left_homotopy_from_other_cylinder {A B : C} [hA : is_cofibrant A] [hB : is_fibrant B]
  (Cyl Cyl' : cylinder A) (f₀ f₁ : A ⟶ B) (H' : Cyl'.to_precylinder.left_homotopy f₀ f₁) :
  Cyl.to_precylinder.left_homotopy f₀ f₁ :=
begin
  apply Cyl.left_homotopy_of_right_homotopy (path_object_exists B).some,
  apply path_object.right_homotopy_of_left_homotopy _ _ H',
end

end cylinder

def left_homotopy_iff_right_homotopy {A B : C} [hA : is_cofibrant A] [hB : is_fibrant B] (Cyl : cylinder A) (P : path_object B)
  (f₀ f₁ : A ⟶ B) : nonempty (Cyl.to_precylinder.left_homotopy f₀ f₁) ↔
    nonempty (P.pre.right_homotopy f₀ f₁) :=
begin
  split,
  { intro h,
    exact nonempty.intro (P.right_homotopy_of_left_homotopy Cyl h.some), },
  { intro h,
    exact nonempty.intro (Cyl.left_homotopy_of_right_homotopy P h.some), },
end

end model_category

end algebraic_topology