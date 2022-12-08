import category_theory.shift
import algebra.homology.homological_complex
import tactic.linarith

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace homological_complex

variables (C : Type*) [category C] [has_zero_morphisms C]

section

variables {C} {ι : Type*} {c : complex_shape ι}

def X_iso_of_eq (K : homological_complex C c) {n n' : ι} (h : n = n') :
  K.X n ≅ K.X n' :=
eq_to_iso (by congr')

@[simp]
lemma X_iso_of_eq_refl (K : homological_complex C c) (n : ι) :
  K.X_iso_of_eq (rfl : n = n) = iso.refl _ :=
begin
  dsimp only [X_iso_of_eq],
  simp,
end

@[simp, reassoc]
lemma X_iso_of_eq_hom_comp_d (K : homological_complex C c) {n n' : ι} (h : n = n') (n'' : ι) :
  (K.X_iso_of_eq h).hom ≫ K.d n' n'' = K.d n n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_comp_d (K : homological_complex C c) {n n' : ι} (h : n = n') (n'' : ι) :
  (K.X_iso_of_eq h).inv ≫ K.d n n'' = K.d n' n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma d_comp_X_iso_of_eq_hom (K : homological_complex C c) (n : ι) {n' n'' : ι} (h : n' = n'') :
  K.d n n' ≫ (K.X_iso_of_eq h).hom = K.d n n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma d_comp_X_iso_of_eq_inv (K : homological_complex C c) (n : ι) {n' n'' : ι} (h : n' = n'') :
  K.d n n'' ≫ (K.X_iso_of_eq h).inv = K.d n n' :=
by { subst h, simp, }

@[reassoc]
lemma X_iso_of_eq_hom_naturality {K L : homological_complex C c} (φ : K ⟶ L) {n n' : ι}
  (h : n = n') :
  φ.f n ≫ (L.X_iso_of_eq h).hom = (K.X_iso_of_eq h).hom ≫ φ.f n' :=
by { subst h, simp, }

@[reassoc]
lemma X_iso_of_eq_inv_naturality {K L : homological_complex C c} (φ : K ⟶ L) {n n' : ι}
  (h : n = n') :
  φ.f n' ≫ (L.X_iso_of_eq h).inv = (K.X_iso_of_eq h).inv ≫ φ.f n :=
by { subst h, simp, }

@[simp, reassoc]
lemma X_iso_of_eq_hom_hom (K : homological_complex C c) {n n' n'' : ι} (h : n = n') (h' : n' = n'') :
  (K.X_iso_of_eq h).hom ≫ (K.X_iso_of_eq h').hom = (K.X_iso_of_eq (h.trans h')).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_hom_inv (K : homological_complex C c) {n n' n'' : ι} (h : n = n') (h' : n'' = n') :
  (K.X_iso_of_eq h).hom ≫ (K.X_iso_of_eq h').inv = (K.X_iso_of_eq (h.trans h'.symm)).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_hom (K : homological_complex C c) {n n' n'' : ι} (h : n' = n) (h' : n' = n'') :
  (K.X_iso_of_eq h).inv ≫ (K.X_iso_of_eq h').hom = (K.X_iso_of_eq (h.symm.trans h')).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_inv (K : homological_complex C c) {n n' n'' : ι} (h : n' = n) (h' : n'' = n') :
  (K.X_iso_of_eq h).inv ≫ (K.X_iso_of_eq h').inv = (K.X_iso_of_eq (h'.trans h)).inv :=
by { substs h h', simp, }

end

local attribute [simp] X_iso_of_eq_hom_naturality X_iso_of_eq_inv_naturality

@[simps obj_d map_f]
def shift_functor (n : ℤ) : cochain_complex C ℤ ⥤ cochain_complex C ℤ :=
{ obj := λ K,
  { X := λ i, K.X (i+n),
    d := λ i j, K.d _ _,
    shape' := λ i j hij, begin
      rw K.shape,
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
  (λ i j hij, by { dsimp, simp, })) (λ K₁ K₂ φ, by { ext, dsimp, simp, })

@[simps]
def shift_functor_zero' (n : ℤ) (h : n = 0) :
  shift_functor C n ≅ 𝟭 _ :=
nat_iso.of_components (λ K, hom.iso_of_components
  (λ i, K.shift_functor_obj_X_iso _ _ _ (by linarith)) (by tidy)) (by tidy)

@[simps]
def shift_functor_add' (n₁ n₂ n₁₂ : ℤ) (h : n₁₂ = n₁ + n₂) :
  shift_functor C n₁ ⋙ shift_functor C n₂ ≅ shift_functor C n₁₂ :=
nat_iso.of_components
  (λ K, hom.iso_of_components (λ i, K.X_iso_of_eq (by linarith)) (by tidy)) (by tidy)

instance : has_shift (cochain_complex C ℤ) ℤ :=
has_shift_mk _ _
{ F := shift_functor C,
  ε := (shift_functor_zero' C _ rfl).symm,
  μ := λ n₁ n₂, shift_functor_add' C n₁ n₂ _ rfl,
  associativity := λ n₁ n₂ n₃ K, by { ext i, dsimp [X_iso_of_eq], simp, }, }

end homological_complex
