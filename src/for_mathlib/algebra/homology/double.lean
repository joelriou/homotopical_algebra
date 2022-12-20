import tactic.linarith
import algebra.homology.single

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

namespace cochain_complex

variables {C : Type*} [category C] {a b : ℤ} (h : a+1=b)
  [has_zero_morphisms C] [has_zero_object C] {A B : C} (φ : A ⟶ B)

namespace double

include h φ
@[nolint unused_arguments]
def X (n : ℤ) : C := if n = a then A else if n = b then B else 0
omit h φ

def X_iso₁ {n : ℤ} (hn : n = a) :
  X h φ n ≅ A :=
eq_to_iso (by { subst hn, dsimp [X], simp, })

def X_iso₂ {n : ℤ} (hn : n = b) :
  X h φ n ≅ B :=
eq_to_iso (begin
  subst hn,
  simp only [X, if_neg (show ¬n=a, by linarith), eq_self_iff_true, if_true, ite_eq_right_iff],
end)

lemma X_is_zero (n : ℤ) (hn₁ : n ≠ a) (hn₂ : n ≠ b) :
  is_zero (X h φ n) :=
by simpa only [X, if_neg hn₁, if_neg hn₂] using is_zero_zero C

def d (i j : ℤ) :
  X h φ i ⟶ X h φ j :=
begin
  by_cases hi : i = a,
  { by_cases hj : j = b,
    { exact (X_iso₁ h φ hi).hom ≫ φ ≫ (X_iso₂ h φ hj).inv, },
    { exact 0, }, },
  { exact 0, },
end

lemma d_eq' {i j : ℤ} (hi : i = a) (hj : j = b) :
  double.d h φ i j = (X_iso₁ h φ hi).hom ≫ φ ≫ (X_iso₂ h φ hj).inv :=
by simp only [d, dif_pos hi, dif_pos hj]

@[simp]
lemma d_eq :
  double.d h φ a b = (X_iso₁ h φ rfl).hom ≫ φ ≫ (X_iso₂ h φ rfl).inv :=
d_eq' _ _ rfl rfl

lemma d_eq_zero₁ {i j : ℤ} (hi : i ≠ a) :
  double.d h φ i j = 0 :=
by simp only [d, dif_neg hi]

lemma d_eq_zero₂ {i j : ℤ} (hj : j ≠ b) :
  double.d h φ i j = 0 :=
begin
  by_cases hi : i = a,
  { simp only [d, dif_pos hi, dif_neg hj], },
  { simp only [d_eq_zero₁ _ _ hi], },
end

@[simp, reassoc]
lemma d_comp_d {i j k : ℤ} :
  double.d h φ i j ≫ double.d h φ j k = 0 :=
begin
  by_cases hi : i = a,
  { by_cases hj : j = b,
    { have hk : j ≠ a := by linarith,
      rw [d_eq_zero₁ _ _ hk, comp_zero], },
    { simp only [d_eq_zero₂ _ _ hj, zero_comp], }, },
  { simp only [d_eq_zero₁ _ _ hi, zero_comp], },
end

end double

@[simps]
def double : cochain_complex C ℤ :=
{ X := double.X h φ,
  d := λ i j, double.d h φ i j,
  shape' := λ i j hij, begin
    change i+1 ≠ j at hij,
    by_cases hi : i = a,
    { rw double.d_eq_zero₂,
      exact λ hj, hij (by linarith), },
    { rw double.d_eq_zero₁ _ _ hi, },
  end, }

example : ℕ := 42

namespace double

section desc

variables (K : cochain_complex C ℤ) (fa : A ⟶ K.X a) (fb : B ⟶ K.X b)
  (comm : fa ≫ K.d a b = φ ≫ fb) {c : ℤ} (hc : b+1 = c)
  (w : fb ≫ K.d b c = 0)

include fa fb

def desc.f (n : ℤ) : (double h φ).X n ⟶ K.X n :=
begin
  by_cases ha : n = a,
  { exact (double.X_iso₁ h φ ha).hom ≫ fa ≫ eq_to_hom (by rw ha), },
  { by_cases hb : n = b,
    { exact (double.X_iso₂ h φ hb).hom ≫ fb ≫ eq_to_hom (by rw hb), },
    { exact 0, }, },
end

@[simp]
lemma desc.f₁ : desc.f h φ K fa fb a = (double.X_iso₁ h φ rfl).hom ≫ fa :=
by simp only [desc.f, dif_pos rfl, eq_to_hom_refl, comp_id]

@[simp]
lemma desc.f₂ : desc.f h φ K fa fb b = (double.X_iso₂ h φ rfl).hom ≫ fb :=
by simp only [desc.f, dif_neg (show b ≠ a, by linarith), dif_pos rfl, eq_to_hom_refl, comp_id]

lemma desc.f_eq_zero (n : ℤ) (ha : n ≠ a) (hb : n ≠ b) : desc.f h φ K fa fb n = 0 :=
by simp only [desc.f, dif_neg ha, dif_neg hb]

include comm w hc

@[simps]
def desc : double h φ ⟶ K :=
{ f := desc.f h φ K fa fb,
  comm' := λ i j hij, begin
    change i+1 = j at hij,
    by_cases ha : i = a,
    { have hb : j = b := by linarith,
      substs ha hb,
      simp only [desc.f₁, assoc, double_d, d_eq, desc.f₂, iso.inv_hom_id_assoc,
        iso.cancel_iso_hom_left, comm], },
    { simp only [double_d, d_eq_zero₁ h _ ha, zero_comp],
      by_cases hb : i = b,
      { have hc : j = c := by linarith,
        substs hc hb,
        simp only [desc.f₂, assoc, w, comp_zero], },
      { rw [desc.f_eq_zero _ _ _ _ _ _ ha hb, zero_comp], }, },
  end, }

end desc

section lift

variables (K : cochain_complex C ℤ) (fa : K.X a ⟶ A) (fb : K.X b ⟶ B)
  (comm : fa ≫ φ = K.d a b ≫ fb) {c : ℤ} (hc : c+1 = a)
  (w : K.d c a ≫ fa = 0)

include fa fb

def lift.f (n : ℤ) : K.X n ⟶ (double h φ).X n :=
begin
  by_cases ha : n = a,
  { exact eq_to_hom (by rw ha) ≫ fa ≫ (double.X_iso₁ h φ ha).inv, },
  { by_cases hb : n = b,
    { exact eq_to_hom (by rw hb) ≫ fb ≫ (double.X_iso₂ h φ hb).inv, },
    { exact 0, }, },
end

@[simp]
lemma lift.f₁ : lift.f h φ K fa fb a = fa ≫ (double.X_iso₁ h φ rfl).inv :=
by simp only [lift.f, dif_pos rfl, eq_to_hom_refl, id_comp]

@[simp]
lemma lift.f₂ : lift.f h φ K fa fb b = fb ≫ (double.X_iso₂ h φ rfl).inv :=
by simp only [lift.f, dif_neg (show b ≠ a, by linarith), dif_pos rfl, eq_to_hom_refl, id_comp]

lemma lift.f_eq_zero (n : ℤ) (ha : n ≠ a) (hb : n ≠ b) : lift.f h φ K fa fb n = 0 :=
by simp only [lift.f, dif_neg ha, dif_neg hb]

include comm w hc

@[simps]
def lift : K ⟶ double h φ :=
{ f := lift.f h φ K fa fb,
  comm' := λ i j hij, begin
    change i+1 = j at hij,
    by_cases hb : j = b,
    { have ha : i = a := by linarith,
      substs ha hb,
      simp only [lift.f₁, double_d, d_eq, assoc, iso.inv_hom_id_assoc, lift.f₂,
        iso.cancel_iso_inv_right_assoc, comm], },
    { simp only [double_d, d_eq_zero₂ h _ hb, comp_zero],
      by_cases ha : j = a,
      { have hc : i = c := by linarith,
        substs hc ha,
        simp only [lift.f₁, reassoc_of w, zero_comp], },
      { rw [lift.f_eq_zero _ _ _ _ _ _ ha hb, comp_zero], }, },
  end, }

end lift

variables {h φ}

@[ext]
lemma ext {K : cochain_complex C ℤ} (f₁ f₂ : double h φ ⟶ K)
  (ha : f₁.f a = f₂.f a) (hb : f₁.f b = f₂.f b) : f₁ = f₂ :=
begin
  ext n,
  by_cases ha' : n = a,
  { subst ha',
    exact ha, },
  { by_cases hb' : n = b,
    { subst hb',
      exact hb, },
    { apply is_zero.eq_of_src,
      exact double.X_is_zero h φ _ ha' hb', }, },
end

@[ext]
lemma ext' {K : cochain_complex C ℤ} (f₁ f₂ : K ⟶ double h φ)
  (ha : f₁.f a = f₂.f a) (hb : f₁.f b = f₂.f b) : f₁ = f₂ :=
begin
  ext n,
  by_cases ha' : n = a,
  { subst ha',
    exact ha, },
  { by_cases hb' : n = b,
    { subst hb',
      exact hb, },
    { apply is_zero.eq_of_tgt,
      exact double.X_is_zero h φ _ ha' hb', }, },
end

@[simp, reassoc]
lemma w_from {K : cochain_complex C ℤ} (f : double h φ ⟶ K) (c : ℤ) :
  f.f b ≫ K.d b c = 0 :=
begin
  by_cases hc : b+1 = c,
  { rw [f.comm b c, double_d, d_eq_zero₁ h φ (show b ≠ a, by linarith), zero_comp], },
  { rw [K.shape _ _ hc, comp_zero], },
end

@[simp, reassoc]
lemma w_to {K : cochain_complex C ℤ} (f : K ⟶ double h φ) (c : ℤ) :
  K.d c a ≫ f.f a = 0 :=
begin
  by_cases hc : c+1 = a,
  { rw [← f.comm c a, double_d, d_eq_zero₂ h φ (show a ≠ b, by linarith), comp_zero], },
  { rw [K.shape _ _ hc, zero_comp], },
end

variables (h φ)

@[simps]
def ι : (homological_complex.single _ _ b).obj B ⟶ double h φ :=
double.lift h φ _ 0 (homological_complex.single_obj_X_self _ _ _ _).hom (by simp)
  (sub_add_cancel a 1) (by simp)

@[simps]
def π : double h φ ⟶ (homological_complex.single _ _ a).obj A :=
double.desc h φ _ (homological_complex.single_obj_X_self _ _ _ _).inv 0 (by simp) rfl (by simp)

@[simp, reassoc]
lemma ι_π : ι h φ ≫ π h φ = 0 :=
begin
  ext n,
  by_cases ha : n = a,
  { subst ha,
    simp only [homological_complex.comp_f, ι_f, lift.f₁, zero_comp,
      homological_complex.zero_apply], },
  { apply is_zero.eq_of_tgt,
    dsimp [homological_complex.single],
    rw [if_neg ha],
    exact is_zero_zero C, },
end

end double

end cochain_complex
