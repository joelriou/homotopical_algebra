import for_mathlib.algebra.homology.trunc_le

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

lemma int.three_cases (a n : ℤ) :
  (n<a ∨ a<n) ∨ n = a :=
begin
  by_cases h₁ : n < a,
  { exact or.inl (or.inl h₁), },
  { cases (not_lt.1 h₁).lt_or_eq; tauto, },
end

lemma category_theory.nat_iso.map_eq_iff {C D : Type*} [category C] [category D] {F G : C ⥤ D}
  (e : F ≅ G) {X Y : C} (f₁ f₂ : X ⟶ Y) : F.map f₁ = F.map f₂ ↔ G.map f₁ = G.map f₂ :=
begin
  suffices : ∀ ⦃F G : C ⥤ D⦄ (e : F ≅ G) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y)
    (h : F.map f₁ = F.map f₂), G.map f₁ = G.map f₂,
  { exact ⟨this e f₁ f₂, this e.symm f₁ f₂⟩, },
  intros F G e X Y f₁ f₂ eq,
  have : ∀ (f : X ⟶ Y), G.map f = e.inv.app X ≫ F.map f ≫ e.hom.app Y := λ f, by tidy,
  simp only [this, eq],
end

open category_theory category_theory.limits category_theory.category

variables {C : Type*} [category C] [abelian C]

namespace homological_complex

lemma single_obj_X_self_naturality {ι : Type*} (c : complex_shape ι) (n : ι)
  [decidable_eq ι] {A B : C} (φ : A ⟶ B) :
    ((single C c n).map φ).f n ≫ (single_obj_X_self C c n B).hom =
      (single_obj_X_self C c n A).hom ≫ φ :=
begin
  dsimp [single],
  simpa only [dif_pos rfl, assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id],
end

variable (C)

def single_homology_functor_iso {ι : Type*} (c : complex_shape ι) (n : ι)
  [decidable_eq ι] :
  homological_complex.single C c n ⋙ homology_functor C c n ≅ 𝟭 C :=
nat_iso.of_components
  (λ A, homology_single_self C c A n)
  (λ A B φ, begin
    let h₁ := short_complex.homology_data.of_zeros (((single C c n).obj A).sc' n) rfl rfl,
    let h₂ := short_complex.homology_data.of_zeros (((single C c n).obj B).sc' n) rfl rfl,
    let h : short_complex.homology_map_data ((short_complex_functor _ _ n).map
      ((single C c n).map φ)) h₁ h₂ := short_complex.homology_map_data.of_zeros _ rfl rfl rfl rfl,
    have eq := short_complex.homology_map_data.homology_map_comm h,
    dsimp only [homology_single_self, iso.trans],
    simp only [assoc],
    erw [← single_obj_X_self_naturality c n φ, reassoc_of eq],
    refl,
  end)

end homological_complex

variable {C}

namespace cochain_complex

instance is_strictly_le_trunc_ge (K : cochain_complex C ℤ) (p q : ℤ) [K.is_strictly_le q] :
  (K.trunc_ge p).is_strictly_le q :=
⟨λ i hi, begin
  rw [is_zero.iff_id_eq_zero, ← cancel_epi (trunc_ge.π_f K p i)],
  apply (is_strictly_le.is_zero K q i hi).eq_of_src,
end⟩

instance is_strictly_ge_trunc_le (K : cochain_complex C ℤ) (p q : ℤ) [K.is_strictly_ge p] :
  (K.trunc_le q).is_strictly_ge p :=
⟨λ i hi, begin
  rw [is_zero.iff_id_eq_zero, ← cancel_mono (trunc_le.ι_f K q i)],
  apply (is_strictly_ge.is_zero K p i hi).eq_of_tgt,
end⟩

lemma is_le_iff_of_is_le_next (K : cochain_complex C ℤ) {a b : ℤ} (h : a+1=b)
  [K.is_le b] : K.is_le a ↔ is_zero (K.homology b) :=
begin
  split,
  { introI,
    exact is_le.is_zero K a b (by linarith), },
  { refine λ hb, ⟨λ n hn, _⟩,
    unfreezingI { subst h, },
    rw ← int.add_one_le_iff at hn,
    cases hn.lt_or_eq,
    { exact is_le.is_zero K (a+1) n h, },
    { subst h,
      exact hb, }, },
end

lemma is_ge_iff_of_is_ge_prev (K : cochain_complex C ℤ) {a b : ℤ} (h : a+1=b)
  [K.is_ge a] : K.is_ge b ↔ is_zero (K.homology a) :=
begin
  split,
  { introI,
    exact is_ge.is_zero K b a (by linarith), },
  { refine λ ha, ⟨λ n hn, _⟩,
    subst h,
    rw [← int.add_one_le_iff, add_le_add_iff_right] at hn,
    cases hn.lt_or_eq,
    { exact is_ge.is_zero K a n h, },
    { unfreezingI { subst h, },
      exact ha, }, },
end

lemma shift_is_strict_le (K : cochain_complex C ℤ) (a b c : ℤ) (h : a = c + b)
  [K.is_strictly_le a] : (K⟦b⟧).is_strictly_le c :=
⟨λ n hn, begin
  change is_zero (K.X (n+b)),
  exact is_strictly_le.is_zero K a (n+b) (by linarith),
end⟩

lemma shift_is_strict_ge (K : cochain_complex C ℤ) (a b c : ℤ) (h : a = c + b)
  [K.is_strictly_ge a] : (K⟦b⟧).is_strictly_ge c :=
⟨λ n hn, begin
  change is_zero (K.X (n+b)),
  exact is_strictly_ge.is_zero K a (n+b) (by linarith),
end⟩

end cochain_complex

namespace derived_category

lemma orthogonality {K L : derived_category C} (φ : K ⟶ L) (p q : ℤ) (hpq : p < q)
  [K.is_le p] [L.is_ge q] : φ = 0 :=
begin
  obtain ⟨K', hK', ⟨eK⟩⟩ := exists_iso_Q_obj_of_le K p,
  obtain ⟨L', hL', ⟨eL⟩⟩ := exists_iso_Q_obj_of_ge L q,
  haveI := hK',
  have hφ : ∃ (φ' : Q.obj K' ⟶ Q.obj L'), φ = eK.hom ≫ φ' ≫ eL.inv :=
    ⟨eK.inv ≫ φ ≫ eL.hom, by simp only [assoc, iso.hom_inv_id, comp_id, iso.hom_inv_id_assoc]⟩,
  obtain ⟨φ, rfl⟩ := hφ,
  obtain ⟨M, hM, s, f, hs, eq⟩ := right_factorisation_of_is_le φ p,
  haveI := hM,
  have hf : f = 0,
  { ext n,
    by_cases p < n,
    { apply (cochain_complex.is_strictly_le.is_zero M p n h).eq_of_src, },
    { apply (cochain_complex.is_strictly_ge.is_zero L' q n (by linarith)).eq_of_tgt, }, },
  simp only [eq, preadditive.is_iso.comp_left_eq_zero, preadditive.is_iso.comp_right_eq_zero, hf,
    functor.map_zero],
end

lemma right_factorisation_of_is_strictly_le_of_is_strictly_ge {K L : cochain_complex C ℤ}
  (φ : Q.obj K ⟶ Q.obj L) (p q : ℤ) [K.is_strictly_le p]
  [K.is_strictly_ge q] [L.is_strictly_ge q] :
  ∃ (K' : cochain_complex C ℤ) (K'_le : K'.is_strictly_le p)
    (K'_ge : K'.is_strictly_ge q) (s : K' ⟶ K) (f : K' ⟶ L) (hs : quasi_iso s),
    φ = (by { haveI := hs, exact inv (Q.map s), }) ≫ Q.map f :=
begin
  obtain ⟨K', hK', s, f, hs, eq⟩ := right_factorisation_of_is_strictly_ge φ q,
  haveI := hK',
  haveI : K'.is_le p,
  { rw cochain_complex.is_le_iff_of_quasi_iso s,
    apply_instance, },
  exact ⟨(cochain_complex.trunc_le K' p), infer_instance, infer_instance,
    cochain_complex.trunc_le.ι K' p ≫ s, cochain_complex.trunc_le.ι K' p ≫ f, infer_instance,
    by simp only [eq, functor.map_comp, assoc, is_iso.eq_inv_comp, is_iso.hom_inv_id_assoc]⟩,
end

lemma left_factorisation_of_is_strictly_le_of_is_strictly_ge {K L : cochain_complex C ℤ}
  (φ : Q.obj K ⟶ Q.obj L) (p q : ℤ) [K.is_strictly_le p] [L.is_strictly_le p]
  [L.is_strictly_ge q] :
  ∃ (L' : cochain_complex C ℤ) (L'_le : L'.is_strictly_le p)
    (L'_ge : L'.is_strictly_ge q) (f : K ⟶ L') (s : L ⟶ L') (hs : quasi_iso s),
    φ = Q.map f ≫ (by { haveI := hs, exact inv (Q.map s), }) :=
begin
  obtain ⟨L', hL', f, s, hs, eq⟩ := left_factorisation_of_is_strictly_le φ p,
  haveI := hL',
  haveI : L'.is_ge q,
  { rw ← cochain_complex.is_ge_iff_of_quasi_iso s,
    apply_instance, },
  exact ⟨(cochain_complex.trunc_ge L' q), infer_instance, infer_instance,
    f ≫ cochain_complex.trunc_ge.π L' q, s ≫ cochain_complex.trunc_ge.π L' q, infer_instance,
    by simp only [eq, functor.map_comp, is_iso.inv_comp, assoc, is_iso.hom_inv_id_assoc]⟩,
end

end derived_category

namespace cochain_complex

instance single_is_strictly_le (A : C) (n : ℤ) :
  is_strictly_le ((homological_complex.single C (complex_shape.up ℤ) n).obj A) n :=
⟨λ i hi, begin
  dsimp,
  rw if_neg (show ¬ i = n, by linarith),
  exact is_zero_zero C,
end⟩

instance single_is_strictly_ge (A : C) (n : ℤ) :
  is_strictly_ge ((homological_complex.single C (complex_shape.up ℤ) n).obj A) n :=
⟨λ i hi, begin
  dsimp,
  rw if_neg (show ¬ i = n, by linarith),
  exact is_zero_zero C,
end⟩


lemma from_single_ext {K L : cochain_complex C ℤ} (f₁ f₂ : K ⟶ L) (p : ℤ)
  [K.is_strictly_le p] [K.is_strictly_ge p] (h : f₁.f p = f₂.f p) : f₁ = f₂ :=
begin
  ext i,
  by_cases hi : i < p,
  { apply (is_strictly_ge.is_zero K p i hi).eq_of_src, },
  { cases (not_lt.1 hi).lt_or_eq with hi' hi',
    { apply (is_strictly_le.is_zero K p i hi').eq_of_src, },
    { subst hi',
      exact h, }, },
end

lemma to_single_ext {K L : cochain_complex C ℤ} (f₁ f₂ : K ⟶ L) (p : ℤ)
  [L.is_strictly_le p] [L.is_strictly_ge p] (h : f₁.f p = f₂.f p) : f₁ = f₂ :=
begin
  ext i,
  by_cases hi : i < p,
  { apply (is_strictly_ge.is_zero L p i hi).eq_of_tgt, },
  { cases (not_lt.1 hi).lt_or_eq with hi' hi',
    { apply (is_strictly_le.is_zero L p i hi').eq_of_tgt, },
    { subst hi',
      exact h, }, },
end

def desc_single (K L : cochain_complex C ℤ) {p : ℤ} (f : K.X p ⟶ L.X p) (q : ℤ)
  [K.is_strictly_le p] [K.is_strictly_ge p]
  (hpq : p+1=q) (hf : f ≫ L.d p q = 0) : K ⟶ L :=
{ f := λ i, begin
    by_cases i = p,
    { unfreezingI { subst h, }, exact f, },
    { exact 0, },
  end,
  comm' := λ i j (hij : i+1 = j), begin
    by_cases i = p,
    { have hj : j = q := by linarith,
      unfreezingI { substs h hj, },
      dsimp,
      simp only [if_pos rfl, hf,
        (is_strictly_le.is_zero K i j (by linarith)).eq_of_tgt (K.d i j) 0, zero_comp], },
    { apply is_zero.eq_of_src,
      by_cases hi : i < p,
      { exact is_strictly_ge.is_zero K p i hi, },
      { apply is_strictly_le.is_zero K p i,
        cases (not_lt.1 hi).lt_or_eq with hi' hi',
        { exact hi', },
        { exfalso, exact h hi'.symm, }, }, },
  end, }

@[simp]
lemma desc_single_f (K L : cochain_complex C ℤ) {p : ℤ} (f : K.X p ⟶ L.X p) (q : ℤ)
  [K.is_strictly_le p] [K.is_strictly_ge p]
  (hpq : p+1=q) (hf : f ≫ L.d p q = 0) :
  (desc_single K L f q hpq hf).f p = f :=
begin
  dsimp [desc_single],
  rw if_pos rfl,
end

def lift_single (K L : cochain_complex C ℤ) {q : ℤ} (f : K.X q ⟶ L.X q) (p : ℤ)
  [L.is_strictly_le q] [L.is_strictly_ge q]
  (hpq : p+1=q) (hf : K.d p q ≫ f = 0) : K ⟶ L :=
{ f := λ i, begin
    by_cases i = q,
    { unfreezingI { subst h, }, exact f, },
    { exact 0, },
  end,
  comm' := λ i j (hij : i+1 = j), begin
    by_cases j = q,
    { have hi : i = p := by linarith,
      unfreezingI { substs h hi, },
      dsimp,
      simp only [if_pos rfl, hf,
        (is_strictly_ge.is_zero L j i (by linarith)).eq_of_src (L.d i j) 0, comp_zero], },
    { apply is_zero.eq_of_tgt,
      by_cases hj : j < q,
      { exact is_strictly_ge.is_zero L q j hj, },
      { apply is_strictly_le.is_zero L q j,
        cases (not_lt.1 hj).lt_or_eq with hj' hj',
        { exact hj', },
        { exfalso, exact h hj'.symm, }, }, },
  end, }

@[simp]
lemma lift_single_f (K L : cochain_complex C ℤ) {q : ℤ} (f : K.X q ⟶ L.X q) (p : ℤ)
  [L.is_strictly_le q] [L.is_strictly_ge q]
  (hpq : p+1=q) (hf : K.d p q ≫ f = 0) :
  (lift_single K L f p hpq hf).f q = f :=
by { dsimp [lift_single], rw if_pos rfl, }

def iso_single (K : cochain_complex C ℤ) (n : ℤ)
  [K.is_strictly_le n] [K.is_strictly_ge n] :
  K ≅ (homological_complex.single C _ n).obj (K.X n) :=
{ hom := desc_single K _ (homological_complex.single_obj_X_self C _ n (K.X n)).inv (n+1) rfl (by simp),
  inv := lift_single _ K (homological_complex.single_obj_X_self C _ n (K.X n)).hom (n-1) (by linarith) (by simp),
  hom_inv_id' := from_single_ext _ _ n
    (by simp only [homological_complex.id_f, homological_complex.comp_f,
      desc_single_f, lift_single_f, iso.inv_hom_id]),
  inv_hom_id' := from_single_ext _ _ n
    (by simp only [homological_complex.id_f, homological_complex.comp_f,
      desc_single_f, lift_single_f, iso.hom_inv_id]), }

lemma quasi_iso_single_map_iff_is_iso {A B : C} (φ : A ⟶ B) (n : ℤ) :
  quasi_iso ((homological_complex.single C (complex_shape.up ℤ) n).map φ) ↔ is_iso φ :=
begin
  split,
  { introI,
    exact (is_iso_map_iff_of_nat_iso (homological_complex.single_homology_functor_iso C
      (complex_shape.up ℤ) n) φ).1 (quasi_iso.is_iso _), },
  { introI,
    apply_instance, },
end

lemma is_iso_iff_quasi_iso_of_single {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ)
  [K.is_strictly_le n] [K.is_strictly_ge n] [L.is_strictly_le n] [L.is_strictly_ge n] :
  is_iso φ ↔ quasi_iso φ :=
begin
  split,
  { introI,
    apply_instance, },
  { introI,
    let e₁ := K.iso_single n,
    let e₂ := L.iso_single n,
    let φ' := e₁.inv ≫ φ ≫ e₂.hom,
    obtain ⟨α, hα⟩ := (homological_complex.single C _ n).map_surjective φ',
    haveI : is_iso φ',
    { have hφ' : quasi_iso φ' := infer_instance,
      rw [← hα, quasi_iso_single_map_iff_is_iso] at hφ',
      haveI := hφ',
      rw ← hα,
      apply_instance, },
    rw [show φ = e₁.hom ≫ φ' ≫ e₂.inv, by simp],
    apply_instance, },
end

lemma quasi_iso_iff_of_is_le_of_is_ge {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ)
  [K.is_le n] [K.is_ge n] [L.is_le n] [L.is_ge n] :
  quasi_iso φ ↔ is_iso (homology_map φ n) :=
begin
  split,
  { introI,
    apply_instance, },
  { introI,
    refine ⟨λ i, _⟩,
    rcases int.three_cases n i with ⟨ _ | _ ⟩ | _,
    { exact ⟨⟨0, (is_ge.is_zero K n i h).eq_of_src _ _, (is_ge.is_zero L n i h).eq_of_src _ _⟩⟩, },
    { exact ⟨⟨0, (is_le.is_zero K n i h).eq_of_src _ _, (is_le.is_zero L n i h).eq_of_src _ _⟩⟩, },
    { unfreezingI { subst h, },
      apply_instance, }, },
end

end cochain_complex

namespace derived_category

variable (C)

@[simps obj map]
def single_functor (n : ℤ) : C ⥤ derived_category C :=
homological_complex.single _ _ n ⋙ Q

instance single_functor_obj_is_le (A : C) (n : ℤ) : ((single_functor C n).obj A).is_le n :=
by { dsimp, apply_instance, }

instance single_functor_obj_is_ge (A : C) (n : ℤ) : ((single_functor C n).obj A).is_ge n :=
by { dsimp, apply_instance, }

instance single_functor_additive (n : ℤ) : (single_functor C n).additive :=
by { dsimp [single_functor], apply_instance, }

def single_functor_homology_iso (n : ℤ) :
  single_functor C n ⋙ homology_functor C n ≅ 𝟭 C :=
functor.associator _ _ _ ≪≫ iso_whisker_left _ (homology_functor_factors C n) ≪≫
  homological_complex.single_homology_functor_iso C _ n

variable {C}

instance faithful_single_functor (n : ℤ) : faithful (single_functor C n) :=
⟨λ A B f₁ f₂ eq, (nat_iso.map_eq_iff (single_functor_homology_iso C n) f₁ f₂).1
  (by simp only [functor.comp_map, eq])⟩

instance full_single_functor (n : ℤ) : full (single_functor C n) :=
functor.full_of_exists _ (λ A B φ, begin
  obtain ⟨K', K'_le, K'_ge, s, f, hs, eq⟩ :=
    right_factorisation_of_is_strictly_le_of_is_strictly_ge φ n n,
  haveI := hs,
  haveI : is_iso s,
  { rw cochain_complex.is_iso_iff_quasi_iso_of_single s n,
    apply_instance, },
  haveI : full (homological_complex.single C (complex_shape.up ℤ) n) := infer_instance,
  exact ⟨(homological_complex.single C _ n).preimage (inv s ≫ f),
    by simp only [eq, single_functor_map, functor.image_preimage,
      functor.map_comp, functor.map_inv]⟩,
end)

end derived_category

namespace cochain_complex

variables {D : Type*} [category D] [abelian D] [has_zero_object D]

def single_shift_iso_app (A : D) (a b c : ℤ) (h : a = c + b) :
  ((homological_complex.single D (complex_shape.up ℤ) a).obj A)⟦b⟧ ≅
    ((homological_complex.single D (complex_shape.up ℤ) c).obj A) :=
{ hom := lift_single _ _ (((shift_functor_obj_X_iso _) _ _ _ h).hom ≫
      (homological_complex.single_obj_X_self D (complex_shape.up ℤ) a A).hom ≫
      (homological_complex.single_obj_X_self D (complex_shape.up ℤ) c A).inv)
      (c-1) (sub_add_cancel c 1) (by simp),
  inv := desc_single _ _ ((homological_complex.single_obj_X_self D (complex_shape.up ℤ) c A).hom ≫
    (homological_complex.single_obj_X_self D (complex_shape.up ℤ) a A).inv ≫
    ((shift_functor_obj_X_iso _) _ _ _ h).inv) (c+1) rfl (by simp),
  hom_inv_id' := begin
    haveI := shift_is_strict_le ((homological_complex.single D
      (complex_shape.up ℤ) a).obj A) _ _ _ h,
    haveI := shift_is_strict_ge ((homological_complex.single D
      (complex_shape.up ℤ) a).obj A) _ _ _ h,
    exact to_single_ext _ _ c (by simpa),
  end,
  inv_hom_id' := to_single_ext _ _ c (by simp), }

@[simp]
lemma single_shift_iso_app_hom_f (A : D) (a b c : ℤ) (h : a = c + b) :
  (single_shift_iso_app A a b c h).hom.f c = ((shift_functor_obj_X_iso _) _ _ _ h).hom ≫
    (homological_complex.single_obj_X_self D (complex_shape.up ℤ) a A).hom ≫
    (homological_complex.single_obj_X_self D (complex_shape.up ℤ) c A).inv :=
lift_single_f _ _ _ _ _ _

@[simp]
lemma single_shift_iso_app_inv_f (A : D) (a b c : ℤ) (h : a = c + b) :
  (single_shift_iso_app A a b c h).inv.f c =
    (homological_complex.single_obj_X_self D (complex_shape.up ℤ) c A).hom ≫
    (homological_complex.single_obj_X_self D (complex_shape.up ℤ) a A).inv ≫
    ((shift_functor_obj_X_iso _) _ _ _ h).inv :=
desc_single_f _ _ _ _ _ _

variable (D)

def single_shift_iso (a b c : ℤ) (h : a = c + b):
  (homological_complex.single D (complex_shape.up ℤ) a) ⋙ category_theory.shift_functor _ b ≅
    (homological_complex.single D (complex_shape.up ℤ) c) :=
nat_iso.of_components (λ A, single_shift_iso_app A a b c h) (λ A₁ A₂ f, begin
  subst h,
  refine to_single_ext _ _ c _,
  simp only [functor.comp_map, homological_complex.comp_f, shift_functor_map_f',
    homological_complex.single_map_f_self, homological_complex.single_obj_X_self_hom,
    homological_complex.single_obj_X_self_inv, shift_functor_obj_X_iso,
    single_shift_iso_app_hom_f, homological_complex.X_iso_of_eq_refl, eq_to_hom_trans,
    assoc, eq_to_hom_trans_assoc],
  dsimp [iso.refl],
  erw [id_comp, id_comp, eq_to_hom_trans],
  refl,
end)

end cochain_complex

namespace derived_category

variable (C)

def single_functor_shift_iso (a b c : ℤ) (h : a = c + b) :
  (single_functor C a) ⋙ category_theory.shift_functor _ b ≅ (single_functor C c) :=
functor.associator _ _ _ ≪≫ iso_whisker_left _ (comm_shift_Q C b).symm ≪≫
  (functor.associator _ _ _).symm ≪≫
  iso_whisker_right (cochain_complex.single_shift_iso C _ _ _ h) Q

variable {C}

@[simp]
lemma single_functor_shift_iso_hom_app (a b c : ℤ) (h : a = c + b) (X : C) :
  (single_functor_shift_iso C a b c h).hom.app X =
    (comm_shift_Q C b).inv.app ((homological_complex.single C _ a).obj X) ≫
      Q.map ((cochain_complex.single_shift_iso C a b c h).hom.app X) :=
begin
  dsimp [single_functor_shift_iso],
  simp only [id_comp],
end

@[simp]
lemma single_functor_shift_iso_inv_app (a b c : ℤ) (h : a = c + b) (X : C) :
  (single_functor_shift_iso C a b c h).inv.app X =
    Q.map ((cochain_complex.single_shift_iso C a b c h).inv.app X) ≫
    (comm_shift_Q C b).hom.app ((homological_complex.single C _ a).obj X) :=
begin
  dsimp [single_functor_shift_iso],
  simp only [comp_id],
end

end derived_category
