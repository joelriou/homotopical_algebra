import tactic.linarith
import category_theory.shift
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import for_mathlib.category_theory.quotient_shift
import for_mathlib.algebra.homology.hom_complex
import for_mathlib.category_theory.shift_misc

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables (C : Type*) [category C] [preadditive C]

namespace cochain_complex

open homological_complex

local attribute [simp] X_iso_of_eq_hom_naturality X_iso_of_eq_inv_naturality

@[simps obj_d map_f]
def shift_functor (n : ℤ) : cochain_complex C ℤ ⥤ cochain_complex C ℤ :=
{ obj := λ K,
  { X := λ i, K.X (i+n),
    d := λ i j, cochain_complex.hom_complex.ε n • K.d _ _,
    shape' := λ i j hij, begin
      rw [K.shape, smul_zero],
      intro hij',
      apply hij,
      dsimp [complex_shape.up] at hij' ⊢,
      linarith,
    end, },
  map := λ K₁ K₂ φ,
  { f := λ i, φ.f _, }, }

variable {C}

@[simp]
lemma X_iso_of_eq_of_shift_functor (K : cochain_complex C ℤ) (n : ℤ) {i i' : ℤ} (h : i = i') :
  ((shift_functor C n).obj K).X_iso_of_eq h = K.X_iso_of_eq (by subst h) := rfl

@[simp]
def shift_functor_obj_X_iso (K : cochain_complex C ℤ) (n i m : ℤ) (hm : m = i + n) :
  ((shift_functor C n).obj K).X i ≅ K.X m :=
X_iso_of_eq K hm.symm

variable (C)

@[simp]
def shift_functor_congr {n n' : ℤ} (h : n = n') :
  shift_functor C n ≅ shift_functor C n' :=
nat_iso.of_components
  (λ K, hom.iso_of_components (λ i, K.X_iso_of_eq (by subst h))
  (λ i j hij, by { dsimp, simp [h], })) (λ K₁ K₂ φ, by { ext, dsimp, simp, })

@[simps]
def shift_functor_zero' (n : ℤ) (h : n = 0) :
  shift_functor C n ≅ 𝟭 _ :=
nat_iso.of_components (λ K, hom.iso_of_components
  (λ i, K.shift_functor_obj_X_iso _ _ _ (by linarith))
    (by { subst h, tidy, })) (by tidy)

@[simps]
def shift_functor_add' (n₁ n₂ n₁₂ : ℤ) (h : n₁₂ = n₁ + n₂) :
  shift_functor C n₁ ⋙ shift_functor C n₂ ≅ shift_functor C n₁₂ :=
nat_iso.of_components
  (λ K, hom.iso_of_components (λ i, K.X_iso_of_eq (by linarith))
  (λ i j hij, begin
    subst h,
    dsimp,
    simp only [linear.comp_smul, X_iso_of_eq_hom_comp_d, linear.smul_comp,
      d_comp_X_iso_of_eq_hom, ← mul_smul, ← cochain_complex.hom_complex.ε_add, add_comm n₁],
  end)) (by tidy)

instance : has_shift (cochain_complex C ℤ) ℤ :=
has_shift_mk _ _
{ F := shift_functor C,
  ε := (shift_functor_zero' C _ rfl).symm,
  μ := λ n₁ n₂, shift_functor_add' C n₁ n₂ _ rfl,
  associativity := λ n₁ n₂ n₃ K, by { ext i, dsimp [X_iso_of_eq], simp, }, }

variable {C}

@[simp]
lemma shift_functor_map_f' {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
  ((category_theory.shift_functor (cochain_complex C ℤ) n).map φ).f p = φ.f (p+n) := rfl

@[simp]
lemma shift_functor_obj_d' (K : cochain_complex C ℤ) (n i j : ℤ) :
  ((category_theory.shift_functor (cochain_complex C ℤ) n).obj K).d i j =
    cochain_complex.hom_complex.ε n • K.d _ _ := rfl

lemma shift_functor_add_inv_app_f (K : cochain_complex C ℤ) (a b n : ℤ) :
  ((shift_functor_add (cochain_complex C ℤ) a b).inv.app K : _ ⟶ _).f n =
    (K.X_iso_of_eq (by { dsimp, rw [add_comm a, add_assoc],})).hom := rfl

lemma shift_functor_add_hom_app_f (K : cochain_complex C ℤ) (a b n : ℤ) :
  ((shift_functor_add (cochain_complex C ℤ) a b).hom.app K : _ ⟶ _).f n =
    (K.X_iso_of_eq (by { dsimp, rw [add_comm a, add_assoc],})).inv :=
begin
  haveI : is_iso (((shift_functor_add (cochain_complex C ℤ) a b).inv.app K : _ ⟶ _).f n),
  { rw shift_functor_add_inv_app_f,
    apply_instance, },
  rw [← cancel_mono (((shift_functor_add (cochain_complex C ℤ) a b).inv.app K : _ ⟶ _).f n),
    ← homological_complex.comp_f, iso.hom_inv_id_app, homological_complex.id_f,
    shift_functor_add_inv_app_f, iso.inv_hom_id],
end

lemma shift_functor_add_comm_hom_app_f (K : cochain_complex C ℤ) (a b n : ℤ) :
  ((shift_functor_add_comm (cochain_complex C ℤ) a b).hom.app K : _ ⟶ _).f n =
    (K.X_iso_of_eq (by { dsimp, simp only [add_assoc, add_comm a], })).hom :=
begin
  dsimp only [shift_functor_add_comm, iso.trans, iso.symm],
  simpa only [nat_trans.comp_app, homological_complex.comp_f,
    shift_functor_add_hom_app_f, shift_functor_add_inv_app_f,
    homological_complex.X_iso_of_eq, eq_to_iso.inv, eq_to_iso.hom, eq_to_hom_app,
    homological_complex.eq_to_hom_f, eq_to_hom_trans],
end

variable (C)

lemma shift_functor_add'_eq (a b c : ℤ) (h : c = a + b) :
  category_theory.shift_functor_add' (cochain_complex C ℤ) a b c h =
    (shift_functor_add' C a b c h).symm :=
begin
  subst h,
  dsimp only [category_theory.shift_functor_add'],
  ext K n,
  dsimp only [iso.trans, shift_functor_add', nat_iso.of_components,
    nat_trans.comp_app, homological_complex.comp_f, hom.iso_of_components],
  simp only [eq_to_hom_app, eq_to_hom_f, shift_functor_add_hom_app_f,
    X_iso_of_eq, eq_to_iso, eq_to_hom_trans, eq_to_hom_refl, nat_trans.id_app,
    homological_complex.id_f, id_comp],
end

lemma shift_functor_add_eq (a b : ℤ) :
  category_theory.shift_functor_add (cochain_complex C ℤ) a b =
    (shift_functor_add' C a b _ rfl).symm :=
begin
  ext1,
  rw ← shift_functor_add'_eq,
  dsimp [category_theory.shift_functor_add'],
  rw id_comp,
end

lemma shift_functor_zero_eq  :
  (category_theory.shift_functor_zero (cochain_complex C ℤ) ℤ) =
    (shift_functor_zero' C 0 rfl) :=
begin
  change (category_theory.shift_functor_zero (cochain_complex C ℤ) ℤ).symm.symm =
    (shift_functor_zero' C 0 rfl).symm.symm,
  congr' 1,
  ext1,
  refl,
end

variables {C} {D : Type*} [category D] (F : C ⥤ D) [preadditive D] [functor.additive F]

def map_cochain_complex_shift_iso (n : ℤ) :
  shift_functor C n ⋙ F.map_homological_complex (complex_shape.up ℤ) ≅
    F.map_homological_complex (complex_shape.up ℤ) ⋙ shift_functor D n :=
nat_iso.of_components (λ K, hom.iso_of_components (λ i, iso.refl _)
  (λ i j hij, by { dsimp, rw [id_comp, comp_id, functor.map_zsmul], })) (by tidy)

instance map_cochain_complex_has_comm_shift :
  (functor.map_homological_complex F (complex_shape.up ℤ)).has_comm_shift ℤ :=
{ iso := λ n, map_cochain_complex_shift_iso F n,
  iso_zero := begin
    ext K i,
    rw [functor.comm_shift.unit_hom_app, comp_f,
      functor.map_homological_complex_map_f, shift_functor_zero_eq,
      shift_functor_zero_eq,
      shift_functor_zero'_hom_app_f, shift_functor_zero'_inv_app_f],
    dsimp [X_iso_of_eq],
    simpa only [eq_to_hom_map, eq_to_hom_trans],
  end,
  iso_add := λ a b, begin
    ext K i,
    simp only [functor.comm_shift.add_hom_app, comp_f, iso.symm_inv,
      functor.map_homological_complex_map_f, shift_functor_add_eq, iso.symm_hom,
        shift_functor_add'_inv_app_f, shift_functor_add'_hom_app_f,
        shift_functor_map_f'],
    dsimp [map_cochain_complex_shift_iso, iso.refl,
      X_iso_of_eq],
    erw [eq_to_hom_map, id_comp, id_comp, eq_to_hom_trans, eq_to_hom_refl],
  end, }

end cochain_complex
