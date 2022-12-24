import for_mathlib.algebra.homology.trunc

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

namespace cochain_complex

section

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

section map

variables (φ) {A' B' : C} (φ' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B') (comm : φ ≫ β = α ≫ φ')

include comm

def map : double h φ ⟶ double h φ' :=
double.desc h φ _ (α ≫ (double.X_iso₁ h φ' rfl).inv)
  (β  ≫ (double.X_iso₂ h φ' rfl).inv) (by tidy) rfl
  (is_zero.eq_of_tgt (double.X_is_zero h φ' (b+1) (by linarith) (by linarith)) _ _)

@[simp]
lemma map_f₁ :
  (map h φ φ' α β comm).f a = (double.X_iso₁ h φ rfl).hom ≫ α ≫ (double.X_iso₁ h φ' rfl).inv :=
by simp only [map, desc_f, desc.f₁]

@[simp]
lemma map_f₂ :
  (map h φ φ' α β comm).f b = (double.X_iso₂ h φ rfl).hom ≫ β ≫ (double.X_iso₂ h φ' rfl).inv :=
by simp only [map, desc_f, desc.f₂]

end map

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

end

section preadditive

namespace double

variables {C : Type*} [category C] [preadditive C] [has_zero_object C]
  {a b : ℤ} (h : a+1=b) {A B A' B' : C} {φ : A ⟶ B} {φ' : A' ⟶ B'}

def homotopy_mk (f₁ f₂ : double h φ ⟶ double h φ') (γ : B ⟶ A')
  (hγ₁ : f₁.f a = (double h φ).d a b ≫ (X_iso₂ h φ rfl).hom ≫
    γ ≫ (X_iso₁ h φ' rfl).inv + f₂.f a)
  (hγ₂ : f₁.f b = ((X_iso₂ h φ rfl).hom ≫ γ ≫ (X_iso₁ h φ' rfl).inv) ≫
    (double h φ').d a b + f₂.f b) :
  homotopy f₁ f₂ :=
{ hom := λ i j, begin
    by_cases hb : i = b,
    { by_cases ha : j = a,
      { exact (X_iso₂ h φ hb).hom ≫ γ ≫ (X_iso₁ h φ' ha).inv, },
      { exact 0,}, },
    { exact 0, },
  end,
  zero' := λ i j (hij : j+1 ≠ i), begin
    by_cases hb : i = b,
    { rw dif_pos hb,
      by_cases ha : j = a,
      { exfalso,
        apply hij,
        rw [ha, hb, h], },
      { rw dif_neg ha, }, },
    { rw dif_neg hb, },
  end,
  comm := λ i, begin
    have h' : (complex_shape.up ℤ).rel a b := h,
    by_cases ha : i = a,
    { subst ha,
      have h'' : (complex_shape.up ℤ).rel (i-1) i := sub_add_cancel i 1,
      simp only [d_next_eq _ h', prev_d_eq _ h'', dif_pos rfl,
        dif_neg (show i ≠ b, by linarith), zero_comp, add_zero, hγ₁], },
    { by_cases hb : i = b,
      { subst hb,
        have h'' : (complex_shape.up ℤ).rel i (i+1) := rfl,
        simp only [prev_d_eq _ h', d_next_eq _ h'', dif_neg (succ_ne_self i), dif_pos rfl,
          comp_zero, zero_add, hγ₂], },
      { exact is_zero.eq_of_src (X_is_zero h φ i ha hb) _ _, }, },
  end, }

/-- should be moved -/
lemma four_cases {a b : ℤ} (h : a+1=b) (n : ℤ) :
  (n < a ∨ b < n) ∨ n = a ∨ n = b :=
begin
  by_cases h₁ : n < a,
  { exact or.inl (or.inl h₁), },
  { by_cases h₂ : b < n,
    { exact or.inl (or.inr h₂), },
    { refine or.inr _,
      simp only [not_lt] at h₁ h₂,
      cases h₁.lt_or_eq with h₃ h₃,
      { cases h₂.lt_or_eq with h₄ h₄,
        { exfalso,
          linarith, },
        { exact or.inr h₄, }, },
      { exact or.inl h₃.symm, }, }, },
end

end double

end preadditive

section abelian

variables {C : Type*} [category C] [abelian C] {a b : ℤ} (h : a+1=b) {A B E : C} (φ : A ⟶ B)
  {i : B ⟶ E} {p : E ⟶ A} (w : i ≫ p = 0)

instance double_strictly_le :
  (double h φ).is_strictly_le b :=
⟨λ n hn, double.X_is_zero h φ n (by linarith) (by linarith)⟩

instance double_strictly_ge :
  (double h φ).is_strictly_ge a :=
⟨λ n hn, double.X_is_zero h φ n (by linarith) (by linarith)⟩

include h

lemma double.is_le_iff_epi : (double h φ).is_le a ↔ epi φ :=
begin
  rw [is_le_iff_of_is_le_next (double h φ) h, ← short_complex.exact_iff_is_zero_homology,
    short_complex.exact_iff_epi],
  { have ha : a = (complex_shape.up ℤ).prev b := by { rw prev, linarith, },
    subst ha,
    change epi (double.d _ _ _ _) ↔ _,
    rw double.d_eq,
    split,
    { intro hφ,
      haveI := @epi_of_epi _ _ _ _ _ _ _ hφ,
      have eq := φ ≫= (double.X_iso₂ h φ rfl).inv_hom_id,
      rw [comp_id, ← assoc] at eq,
      rw ← eq,
      apply epi_comp, },
    { introI,
      haveI := epi_comp φ (double.X_iso₂ h φ rfl).inv,
      apply epi_comp, }, },
  { apply is_zero.eq_of_tgt,
    exact double.X_is_zero h φ _ (by { rw [next], linarith, })
      (by simpa only [next] using succ_ne_self b), },
end

instance double_le [epi φ] :
  (double h φ).is_le a :=
by { rw double.is_le_iff_epi, apply_instance, }

lemma double.is_ge_iff_mono : (double h φ).is_ge b ↔ mono φ :=
begin
  rw [is_ge_iff_of_is_ge_prev (double h φ) h, ← short_complex.exact_iff_is_zero_homology,
    short_complex.exact_iff_mono],
  { have hb : b = (complex_shape.up ℤ).next a := by rw [next, h],
    subst hb,
    change mono (double.d _ _ _ _) ↔ _,
    rw double.d_eq,
    split,
    { intro hφ,
      rw ← assoc at hφ,
      haveI := @mono_of_mono _ _ _ _ _ _ _ hφ,
      have eq := (double.X_iso₁ h φ rfl).inv_hom_id =≫ φ,
      rw [id_comp, assoc] at eq,
      rw ← eq,
      apply mono_comp, },
    { introI,
      haveI := mono_comp φ (double.X_iso₂ h φ rfl).inv,
      apply mono_comp, }, },
  { apply is_zero.eq_of_src,
    exact double.X_is_zero h φ _ (by simpa only [prev] using pred_ne_self a)
      (by { rw [prev], linarith, }), },
end

instance double_ge [mono φ] :
  (double h φ).is_ge b :=
by { rw double.is_ge_iff_mono, apply_instance, }

include w

def double.σ : (double h i) ⟶ (homological_complex.single _ (complex_shape.up ℤ) b).obj A :=
lift_single ((double.X_iso₂ h i rfl).hom ≫ p ≫
  (homological_complex.single_obj_X_self _ _ _ A).inv) _ h
begin
  dsimp,
  simp only [double.d_eq, assoc, iso.inv_hom_id_assoc, preadditive.is_iso.comp_left_eq_zero,
    reassoc_of w, zero_comp],
end

@[simp]
lemma double.σ_f₁ : (double.σ h w).f a = 0 :=
begin
  dsimp [double.σ, lift_single],
  rw dif_neg (show ¬ a=b, by linarith),
end

@[simp]
lemma double.σ_f₂ :
  (double.σ h w).f b = (double.X_iso₂ h i rfl).hom ≫ p
    ≫ (homological_complex.single_obj_X_self C (complex_shape.up ℤ) b A).inv :=
begin
  dsimp only [double.σ, lift_single],
  rw dif_pos rfl,
end

def double.σ' : (homological_complex.single _ (complex_shape.up ℤ) a).obj B ⟶
  double h p :=
begin
  refine desc_single ((homological_complex.single_obj_X_self _ _ _ B).hom ≫ i ≫
    (double.X_iso₁ h p rfl).inv) _ h _,
  { dsimp,
    simp only [double.d_eq, assoc, iso.inv_hom_id_assoc, preadditive.is_iso.comp_left_eq_zero,
      reassoc_of w, zero_comp], },
end

omit w

def double.homotopy_πσ'_σι : homotopy (double.π h i ≫ double.σ' h w)
  (-double.σ h w ≫ double.ι h p) :=
double.homotopy_mk _ _ _ (𝟙 _)
  (by { dsimp, simp [double.π, double.σ', double.ι], })
  (by { dsimp, simp [double.π, double.σ, double.ι], })

lemma double.quasi_iso_σ' (ex : (short_complex.mk _ _ w).short_exact) :
  quasi_iso (double.σ' h w) :=
begin
  have hb : b = (complex_shape.up ℤ).next a := by rw [next, h],
  subst hb,
  haveI := ex.mono_f,
  haveI := ex.epi_g,
  rw quasi_iso_iff_of_is_le_of_is_ge (double.σ' h w) a,
  apply short_complex.quasi_iso.of_kernel_fork _ _ _,
  { refine ⟨λ Z f₁ f₂ eq, is_zero.eq_of_src _ _ _⟩,
    refine double.X_is_zero h p _
      (by { rw prev, linarith, })
      (by { rw prev, linarith, }), },
  { refl, },
  { let e : parallel_pair p 0 ≅
      parallel_pair (((double h) p).sc' a).g 0 :=
      parallel_pair.ext (double.X_iso₁ h p rfl).symm
        ((double.X_iso₂ h p rfl).symm) (by tidy) (by tidy),
    equiv_rw (is_limit.postcompose_inv_equiv e _).symm,
    refine is_limit.of_iso_limit ex.exact.f_is_kernel _,
    refine fork.ext (homological_complex.single_obj_X_self _ (complex_shape.up ℤ) a B).symm _,
    dsimp only [cones.postcompose, fork.ι],
    dsimp [e, double.σ'],
    simp only [desc_single_f, assoc, iso.inv_hom_id, comp_id, eq_to_hom_trans_assoc,
      eq_to_hom_refl, id_comp], },
end

lemma double.quasi_iso_σ (ex : (short_complex.mk _ _ w).short_exact) :
  quasi_iso (double.σ h w) :=
begin
  have ha : a = (complex_shape.up ℤ).prev b := by { rw prev, linarith, },
  subst ha,
  haveI := ex.mono_f,
  haveI := ex.epi_g,
  rw quasi_iso_iff_of_is_le_of_is_ge (double.σ h w) b,
  apply short_complex.quasi_iso.of_cokernel_cofork _ _ _,
  { refine ⟨λ Z f₁ f₂ eq, is_zero.eq_of_tgt _ _ _⟩,
    refine double.X_is_zero h i _
      (by { rw [next, prev], linarith, })
      (by { rw [next], linarith, }), },
  { refl, },
  { dsimp [double.σ],
    let e : parallel_pair i 0 ≅
      parallel_pair (((double h) i).sc' b).f 0 :=
      parallel_pair.ext (double.X_iso₁ h i rfl).symm (double.X_iso₂ h i rfl).symm
        (by tidy) (by tidy),
    equiv_rw (is_colimit.precompose_hom_equiv e _).symm,
    refine is_colimit.of_iso_colimit ex.exact.g_is_cokernel _,
    refine cofork.ext (homological_complex.single_obj_X_self _ (complex_shape.up ℤ) b A).symm _,
    dsimp only [cocones.precompose, cofork.π],
    dsimp [e, double.σ],
    simp only [lift_single_f, iso.inv_hom_id_assoc], },
end

lemma double.is_iso_iff {K L : cochain_complex C ℤ} [K.is_strictly_le b] [K.is_strictly_ge a]
  [L.is_strictly_le b] [L.is_strictly_ge a] (φ : K ⟶ L) :
  is_iso φ ↔ (is_iso (φ.f a) ∧ is_iso (φ.f b)) :=
begin
  split,
  { introI,
    split; exact (infer_instance : is_iso ((homological_complex.eval _ _ _).map φ)), },
  { intro hφ,
    haveI : ∀ (n : ℤ), is_iso (φ.f n),
    { intro n,
      rcases double.four_cases h n with ⟨h' | h'⟩ | ⟨h' | h'⟩,
      { refine ⟨⟨0, (is_strictly_ge.is_zero K a _ h').eq_of_src _ _,
          (is_strictly_ge.is_zero L a _ h').eq_of_src _ _⟩⟩, },
      { refine ⟨⟨0, (is_strictly_le.is_zero K b _ h').eq_of_src _ _,
          (is_strictly_le.is_zero L b _ h').eq_of_src _ _⟩⟩, },
      all_goals { unfreezingI { subst h', }, tauto, }, },
    apply homological_complex.hom.is_iso_of_components, },
end

lemma exists_iso_double (K : cochain_complex C ℤ) [K.is_strictly_le b] [K.is_strictly_ge a] :
  ∃ (A B : C) (φ : A ⟶ B), nonempty (K ≅ double h φ) :=
begin
  let α := double.lift h (K.d a b) K (𝟙 _) (𝟙 _) (by simp) (show (a-1)+1=a, by linarith)
      ((is_strictly_ge.is_zero K a (a-1) (by linarith)).eq_of_src _ _),
  haveI : is_iso α,
  { simp only [double.is_iso_iff h α, id_comp, double.lift_f, double.lift.f₁, double.lift.f₂],
    split; apply_instance, },
  exact ⟨_, _, K.d a b, ⟨as_iso α⟩⟩,
end

variables {h φ}

lemma single_to_double {Z : C} (f : ((homological_complex.single C _ a).obj Z) ⟶ double h φ) :
  ∃ (g : Z ⟶ A) (hg : g ≫ φ = 0), f = desc_single ((homological_complex.single_obj_X_self C
    (complex_shape.up ℤ) a Z).hom ≫ g ≫ (double.X_iso₁ h φ rfl).inv) _ h
    (by simp [reassoc_of hg]) :=
⟨(homological_complex.single_obj_X_self C
  (complex_shape.up ℤ) a Z).inv ≫ f.f a ≫ (double.X_iso₁ h φ rfl).hom,
  by simpa only [preadditive.is_iso.comp_left_eq_zero, double_d, double.d_eq,
  homological_complex.single_obj_d, zero_comp,
  iso.inv_hom_id, comp_id, assoc] using f.comm a b =≫ (double.X_iso₂ h φ rfl).hom,
  from_single_ext _ _ a (by simp)⟩

lemma single_to_double' {Z : C} (f : ((homological_complex.single C _ b).obj Z) ⟶ double h φ) :
  ∃ (g : Z ⟶ B), f = desc_single ((homological_complex.single_obj_X_self C
    (complex_shape.up ℤ) b Z).hom ≫ g ≫ (double.X_iso₂ h φ rfl).inv) (b+1) rfl
    (is_zero.eq_of_tgt (double.X_is_zero h φ (b+1) (by simp only [← h, add_assoc, ne.def,
      add_right_eq_self, add_self_eq_zero, one_ne_zero, not_false_iff]) (succ_ne_self b)) _ _) :=
⟨(homological_complex.single_obj_X_self C
    (complex_shape.up ℤ) b Z).inv ≫ f.f b ≫ (double.X_iso₂ h φ rfl).hom,
    from_single_ext _ _ b (by simp)⟩

end abelian

end cochain_complex
