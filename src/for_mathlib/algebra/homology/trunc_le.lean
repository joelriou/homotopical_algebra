import for_mathlib.algebra.homology.trunc_ge

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

variables {C : Type*} [category C] [abelian C]

namespace cochain_complex

variables (K L : cochain_complex C ℤ)

def trunc_le.X (n : ℤ) (i : ℤ) : C :=
if n < i
  then 0
  else if i = n
    then (homological_complex.short_complex_functor C (complex_shape.up ℤ) i ⋙
      short_complex.cycles_functor C).obj K
    else K.X i

lemma trunc_le.is_zero_X (n : ℤ) (i : ℤ) (hn : n < i) :
  is_zero (trunc_le.X K n i) :=
begin
  dsimp [trunc_le.X],
  simpa only [if_pos hn] using is_zero_zero C,
end

def trunc_le.X_iso_X (n : ℤ) (i : ℤ) (hn : i < n) :
  trunc_le.X K n i ≅ K.X i :=
eq_to_iso begin
  dsimp [trunc_le.X],
  rw [if_neg (show ¬n<i, by linarith), if_neg (show i ≠ n, by linarith)],
end

def trunc_le.X_iso_cycles (n : ℤ) (i : ℤ) (hn : i = n) :
  trunc_le.X K n i ≅ (K.sc' i).cycles :=
eq_to_iso begin
  dsimp [trunc_le.X],
  simpa only [if_neg (show ¬ n<i, by linarith), if_pos hn],
end

def trunc_le.d (n : ℤ) (i j : ℤ) : trunc_le.X K n i ⟶ trunc_le.X K n j :=
begin
  by_cases hij : i+1 = j,
  { by_cases hj₀ : n<j,
    { exact 0, },
    { by_cases hn : j = n,
      { exact ((K.sc' j).lift_cycles ((trunc_le.X_iso_X K n i (by linarith)).hom ≫ K.d i j)
          (by tidy)) ≫ (trunc_le.X_iso_cycles K n j hn).inv, },
      { exact (trunc_le.X_iso_X K n i (by linarith)).hom ≫ K.d i j ≫
          (trunc_le.X_iso_X K n j (by { cases (not_lt.1 hj₀).lt_or_eq; tauto, })).inv, }, }, },
  { exact 0, },
end

def trunc_le.ι_f (n i : ℤ) : trunc_le.X K n i ⟶ K.X i :=
begin
  by_cases hi : n < i,
  { exact 0, },
  { by_cases hn : i = n,
    { exact (trunc_le.X_iso_cycles K n i hn).hom ≫ (K.sc' i).cycles_i, },
    { exact (trunc_le.X_iso_X K n i (by { cases (not_lt.1 hi).lt_or_eq; tauto, })).hom, }, },
end

instance (n i : ℤ) : mono (trunc_le.ι_f K n i) :=
begin
  dsimp [trunc_le.ι_f],
  by_cases h₀ : n < i,
  { rw dif_pos h₀,
    constructor,
    intros Z f₁ f₂ eq,
    apply (trunc_le.is_zero_X K n i h₀).eq_of_tgt, },
  { rw dif_neg h₀,
    by_cases hn : i = n,
    { rw dif_pos hn,
      apply mono_comp, },
    { rw dif_neg hn,
      apply_instance, }, },
end

lemma trunc_le.is_iso_ι_f (n i : ℤ) (hi : i < n) :
  is_iso (trunc_le.ι_f K n i) :=
begin
  dsimp [trunc_le.ι_f],
  simp only [dif_neg (show ¬ n < i, by linarith),
    dif_neg (show i ≠ n, by linarith)],
  apply_instance,
end

lemma trunc_le.ι_f_eq_zero (n i : ℤ) (hi : n < i) :
  trunc_le.ι_f K n i = 0 :=
by { dsimp [trunc_le.ι_f], rw [dif_pos hi], }

lemma trunc_le.ι_f_eq_of_eq (n i : ℤ) (hn : i = n) :
  trunc_le.ι_f K n i = (trunc_le.X_iso_cycles K n i hn).hom ≫ (K.sc' i).cycles_i :=
by { dsimp [trunc_le.ι_f], rw [dif_neg (show ¬n<i, by linarith), dif_pos hn], }

lemma trunc_le.ι_f_eq_X_iso_X_inv (n i : ℤ) (hi : i < n) :
  trunc_le.ι_f K n i = (trunc_le.X_iso_X K n i hi).hom :=
by { dsimp [trunc_le.ι_f], rw [dif_neg, dif_neg]; linarith, }

lemma trunc_le.shape (n i j : ℤ) (hij : i+1 ≠ j) : trunc_le.d K n i j = 0 :=
by { dsimp only [trunc_le.d], rw dif_neg hij, }

lemma trunc_le.d_eq_zero (n : ℤ) (i j : ℤ) (hj : n ≤ i) :
  trunc_le.d K n i j = 0 :=
begin
  by_cases hij : i+1 = j,
  { dsimp [trunc_le.d],
    rw [dif_pos hij, dif_pos],
    linarith, },
  { rw trunc_le.shape K n i j hij, },
end

lemma trunc_le.d_eq_d (n : ℤ) (i j : ℤ) (hij : i + 1 = j) (hj : j < n) :
  trunc_le.d K n i j = (trunc_le.X_iso_X K n i
    (by { rw ← hij at hj, exact (lt_add_one i).trans hj, })).hom ≫ K.d i j ≫
    (trunc_le.X_iso_X K n j hj).inv :=
by { dsimp [trunc_le.d], rw [dif_pos hij, dif_neg, dif_neg]; linarith, }

lemma trunc_le.ι_comp_d_eq_zero (n : ℤ) (i j : ℤ) (hij : i + 1 = j) (hi : i = n) :
   trunc_le.ι_f K n i ≫ K.d i j = 0 :=
begin
  have hj : j = (complex_shape.up ℤ).next i := by { rw [next], linarith, },
  subst hj,
  dsimp [trunc_le.ι_f],
  erw [dif_neg (show ¬n<i, by linarith), dif_pos hi, assoc, (K.sc' i).cycles_i_g, comp_zero],
end

def trunc_le.ι_is_kernel (n i j : ℤ) (hij : i + 1 = j) (hi : i = n) :
  is_limit (kernel_fork.of_ι _ (trunc_le.ι_comp_d_eq_zero K n i j hij hi)) :=
begin
  have hij' : j = (complex_shape.up ℤ).next i := by { rw [next], linarith, },
  subst hij',
  exact is_limit.of_iso_limit (K.sc' i).cycles_is_kernel
    (iso.symm (fork.ext (trunc_le.X_iso_cycles K n i hi)
      (trunc_le.ι_f_eq_of_eq K n i hi).symm)),
end

@[simp, reassoc]
lemma trunc_le.d_comm (n i j : ℤ) :
  trunc_le.d K n i j ≫ trunc_le.ι_f K n j =
     trunc_le.ι_f K n i ≫ K.d i j :=
begin
  by_cases hij : i+1 = j,
  { by_cases hi₀ : n < i,
    { apply (trunc_le.is_zero_X K n i hi₀).eq_of_src, },
    by_cases hi : i = n,
    { simp only [trunc_le.ι_comp_d_eq_zero K n i j hij hi,
        trunc_le.d_eq_zero K n i j (by linarith), zero_comp], },
    by_cases hj : j = n,
    { dsimp [trunc_le.d, trunc_le.ι_f],
      simp only [dif_pos hij, dif_neg (show ¬ n < j, by linarith), dif_pos hj, dif_neg hi₀,
        dif_neg hi, assoc, iso.inv_hom_id_assoc, short_complex.lift_cycles_i], },
    { have hj' : j < n,
      { subst hij,
        cases (not_lt.1 hi₀).lt_or_eq,
        { rw lt_iff_le_and_ne,
          split,
          { linarith, },
          { exact hj, }, },
        { exfalso, exact hi h, }, },
      simp only [trunc_le.d_eq_d K n i j hij hj', trunc_le.ι_f_eq_X_iso_X_inv K n j hj', assoc,
        iso.inv_hom_id, comp_id, trunc_le.ι_f_eq_X_iso_X_inv K n i (by linarith)], }, },
  { rw [trunc_le.shape K n i j hij, K.shape i j hij, zero_comp, comp_zero], },
end

@[simp, reassoc]
lemma trunc_le.d_comp_d (n i j k : ℤ) : trunc_le.d K n i j ≫ trunc_le.d K n j k = 0 :=
by simp only [← cancel_mono (trunc_le.ι_f K n k), assoc, trunc_le.d_comm,
    trunc_le.d_comm_assoc, K.d_comp_d, zero_comp, comp_zero]

@[simps]
def trunc_le (n : ℤ) : cochain_complex C ℤ :=
{ X := trunc_le.X K n,
  d := trunc_le.d K n,
  shape' := trunc_le.shape K n,
  d_comp_d' := λ i j k hij hjk, trunc_le.d_comp_d K n i j k, }

@[simps]
def trunc_le.ι (n : ℤ) : K.trunc_le n ⟶ K :=
{ f := trunc_le.ι_f K n,
  comm' := λ i j hij, (trunc_le.d_comm K n i j).symm, }

variables {K L}

def trunc_le.map_f (φ : K ⟶ L) (n i : ℤ) :
  (K.trunc_le n).X i ⟶ (L.trunc_le n).X i :=
begin
  by_cases hi : i < n,
  { exact (trunc_le.X_iso_X K n i hi).hom ≫ φ.f i ≫
    (trunc_le.X_iso_X L n i hi).inv, },
  { by_cases hn : i = n,
    { exact (trunc_le.X_iso_cycles K n i hn).hom ≫
        (homological_complex.short_complex_functor C (complex_shape.up ℤ) i ⋙
        short_complex.cycles_functor C).map φ≫ (trunc_le.X_iso_cycles L n i hn).inv, },
    { exact 0, }, },
end

lemma trunc_le.map_f_eq_f (φ : K ⟶ L) (n i : ℤ) (hi : i < n) :
  trunc_le.map_f φ n i = (trunc_le.X_iso_X K n i hi).hom ≫ φ.f i ≫
    (trunc_le.X_iso_X L n i hi).inv :=
begin
  dsimp only [trunc_le.map_f],
  simp only [dif_pos hi],
end

@[simp, reassoc]
lemma trunc_le.map_f_comm_ι_f (φ : K ⟶ L) (n i : ℤ) :
  trunc_le.map_f φ n i ≫ trunc_le.ι_f L n i =
    trunc_le.ι_f K n i ≫ φ.f i :=
begin
  by_cases hi : i < n,
  { simp only [trunc_le.ι_f_eq_X_iso_X_inv _ n i hi, trunc_le.map_f_eq_f φ n i hi, assoc,
      iso.inv_hom_id, comp_id], },
  { by_cases hn : i = n,
    { dsimp [trunc_le.map_f, trunc_ge.π_f],
      simp only [dif_neg hi, dif_pos hn, assoc, iso.inv_hom_id_assoc,
        trunc_le.ι_f_eq_of_eq _ n i hn],
      erw (short_complex.cycles_i_nat_trans C).naturality
        ((homological_complex.short_complex_functor C (complex_shape.up ℤ) i).map φ),
      refl,   },
    { refine (trunc_le.is_zero_X K n i _).eq_of_src _ _,
      cases (not_lt.1 hi).lt_or_eq,
      { exact h, },
      { exfalso, exact hn h.symm, }, }, },
end

@[reassoc]
lemma trunc_le.map_comm_f (φ : K ⟶ L) (n i j : ℤ) :
  trunc_le.map_f φ n i ≫ trunc_le.d L n i j =
    trunc_le.d K n i j ≫ trunc_le.map_f φ n j :=
by simp only [← cancel_mono (trunc_le.ι_f L n j), assoc, trunc_le.d_comm,
    trunc_le.map_f_comm_ι_f_assoc, homological_complex.hom.comm, trunc_le.map_f_comm_ι_f,
    trunc_le.d_comm_assoc]

@[simp]
lemma trunc_le.map_id_f (K : cochain_complex C ℤ) (n i : ℤ) :
  trunc_le.map_f (𝟙 K) n i = 𝟙 _ :=
by simp only [← cancel_mono (trunc_le.ι_f K n i),
  trunc_le.map_f_comm_ι_f, homological_complex.id_f, comp_id, id_comp]

@[simp]
lemma trunc_le.map_comp_f {K L M : cochain_complex C ℤ}
  (φ : K ⟶ L) (φ' : L ⟶ M) (n i : ℤ) :
  trunc_le.map_f (φ ≫ φ') n i =
    trunc_le.map_f φ n i ≫ trunc_le.map_f φ' n i :=
by simp only [← cancel_mono (trunc_le.ι_f M n i),
  trunc_le.map_f_comm_ι_f, homological_complex.comp_f, assoc, trunc_le.map_f_comm_ι_f_assoc]

variable (C)

@[simps]
def trunc_le_functor (n : ℤ) :
  cochain_complex C ℤ ⥤ cochain_complex C ℤ :=
{ obj := λ K, K.trunc_le n,
  map := λ K L φ,
  { f := λ i, trunc_le.map_f φ n i,
    comm' := λ i j hij, trunc_le.map_comm_f φ n i j, }, }

@[simps]
def trunc_le.nat_trans_ι (n : ℤ) :
  trunc_le_functor C n ⟶ 𝟭 _ :=
{ app := λ K, trunc_le.ι K n,
  naturality' := λ K L φ, begin
    ext i
    dsimp,
    simp only [functor.id_map, homological_complex.comp_f, trunc_le_functor_map_f],
    dsimp,
    simp only [trunc_le.map_f_comm_ι_f],
  end, }

variables {C} (K)

lemma trunc_le.is_zero_homology (n i : ℤ) (hi : n < i) :
  is_zero ((homology_functor C _ i).obj (K.trunc_le n)) :=
begin
  dsimp [homology_functor],
  rw ← short_complex.exact_iff_is_zero_homology,
  exact short_complex.exact.of_is_zero_X₂ _ (trunc_le.is_zero_X K n i hi),
end

lemma trunc_le.is_iso_homology_map_ι (n i : ℤ) (hi : i ≤ n) :
  is_iso ((homology_functor C _ i).map (trunc_le.ι K n)) :=
begin
  let φ := (homological_complex.short_complex_functor C (complex_shape.up ℤ) i).map
    (trunc_le.ι K n),
  haveI : is_iso φ.τ₁ := trunc_le.is_iso_ι_f K n _ (by { rw [prev], linarith, }),
  cases hi.lt_or_eq,
  { haveI : mono φ.τ₃ := by { dsimp, apply_instance, },
    haveI : is_iso φ.τ₂ := trunc_le.is_iso_ι_f K n i h,
    exact short_complex.quasi_iso.of_epi_of_is_iso_of_mono φ, },
  { sorry, --exact short_complex.quasi_iso.of_cokernel_cofork φ
    --  ((trunc_le.is_zero_X K n _ (by { rw [prev], linarith, })).eq_of_src _ _)
    --  (trunc_le.π_is_cokernel K n _ i (by { rw [prev], linarith, }) h.symm), },
  },
end

variables {K L}

lemma trunc_le.map_homology_iso (φ : K ⟶ L) (n i : ℤ) [is_iso (homology_map φ i)] :
  is_iso (homology_map ((trunc_le_functor C n).map φ) i) :=
begin
  by_cases hi : i ≤ n,
  { have eq := (homology_functor C _ i).congr_map ((trunc_le.nat_trans_ι C n).naturality φ),
    simp only [functor.map_comp, functor.id_map, trunc_le.nat_trans_ι_app] at eq,
    change homology_map _ i ≫ homology_map (trunc_le.ι L n) i =
      homology_map (trunc_le.ι K n) i ≫ homology_map φ i at eq,
    haveI : ∀ (M : cochain_complex C ℤ), is_iso (homology_map (trunc_le.ι M n) i) :=
      λ M, trunc_le.is_iso_homology_map_ι M n i hi,
    simp only [← cancel_mono (inv (homology_map (trunc_le.ι L n) i)),
      assoc, is_iso.hom_inv_id, comp_id] at eq,
    rw eq,
    apply_instance, },
  { simp only [not_le] at hi,
    exact ⟨⟨0, (trunc_le.is_zero_homology K n i hi).eq_of_src _ _,
       (trunc_le.is_zero_homology L n i hi).eq_of_src _ _⟩⟩, },
end

instance trunc_le.map_quasi_iso (φ : K ⟶ L) (n : ℤ) [quasi_iso φ] :
  quasi_iso ((trunc_le_functor _ n).map φ) :=
⟨λ i, trunc_le.map_homology_iso φ n i⟩

variable (C)

lemma trunc_le_functor_comp_Q_inverts_quasi_isomorphisms (n : ℤ) :
  (quasi_isomorphisms _ _).is_inverted_by
    (cochain_complex.trunc_le_functor C n ⋙ derived_category.Q) :=
λ K L φ hφ, begin
  haveI : quasi_iso φ := by simpa only [← mem_quasi_isomorphisms_iff] using hφ,
  dsimp,
  apply_instance,
end

variable {C}

class is_strictly_le (K : cochain_complex C ℤ) (n : ℤ) : Prop :=
(is_zero' : ∀ (i : ℤ) (hi : n < i), is_zero (K.X i))

lemma is_strictly_le.is_zero (K : cochain_complex C ℤ) (n i : ℤ) [K.is_strictly_le n]
  (hi : n < i) : is_zero (K.X i) :=
is_strictly_le.is_zero' i hi

lemma is_strictly_le_of_le (K : cochain_complex C ℤ) (n m : ℤ) (hnm : n ≤ m)
  [K.is_strictly_le n] :
  K.is_strictly_le m :=
⟨λ i hi, is_strictly_le.is_zero K n i (by linarith)⟩

lemma is_strictly_le.of_iso {K L : cochain_complex C ℤ} (e : K ≅ L) (n : ℤ)
  [K.is_strictly_le n] : L.is_strictly_le n :=
⟨λ i hi, is_zero.of_iso (is_strictly_le.is_zero K n i hi)
  ((homological_complex.eval _ _ i).map_iso e.symm)⟩

lemma is_strictly_le.iff_of_iso {K L : cochain_complex C ℤ} (e : K ≅ L) (n : ℤ) :
  K.is_strictly_le n ↔ L.is_strictly_le n :=
begin
  split,
  { introI,
    exact is_strictly_le.of_iso e n, },
  { introI,
    exact is_strictly_le.of_iso e.symm n, },
end

class is_le (K : cochain_complex C ℤ) (n : ℤ) : Prop :=
(is_zero' : ∀ (i : ℤ) (hi : n < i), is_zero (K.homology i))

lemma is_le.is_zero (K : cochain_complex C ℤ) (n i : ℤ) [K.is_le n] (hi : n < i) :
  is_zero (K.homology i) :=
is_le.is_zero' i hi

lemma is_le_of_le (K : cochain_complex C ℤ) (n m : ℤ) (hnm : n ≤ m) [K.is_le n] : K.is_le m :=
⟨λ i hi, is_le.is_zero K n i (by linarith)⟩

lemma is_le.of_iso {K L : cochain_complex C ℤ} (e : K ≅ L) (n : ℤ) [K.is_le n] : L.is_le n :=
⟨λ i hi, is_zero.of_iso (is_le.is_zero K n i hi) ((homology_functor _ _ i).map_iso e.symm)⟩

lemma is_le.iff_of_iso {K L : cochain_complex C ℤ} (e : K ≅ L) (n : ℤ) :
  K.is_le n ↔ L.is_le n :=
begin
  split,
  { introI,
    exact is_le.of_iso e n, },
  { introI,
    exact is_le.of_iso e.symm n, },
end

@[priority 100]
instance is_le_of_is_strictly_le (K : cochain_complex C ℤ) (n : ℤ)
  [K.is_strictly_le n] : K.is_le n :=
⟨λ i hi, begin
  rw ← short_complex.exact_iff_is_zero_homology,
  exact short_complex.exact.of_is_zero_X₂ _ (is_strictly_le.is_zero K n i hi),
end⟩

instance trunc_le_is_strictly_le (K : cochain_complex C ℤ) (n : ℤ) :
  (K.trunc_le n).is_strictly_le n :=
⟨trunc_le.is_zero_X K n⟩

instance trunc_le_is_strictly_le' (K : cochain_complex C ℤ) (n : ℤ) :
  ((trunc_le_functor C n).obj K).is_strictly_le n :=
(infer_instance : (K.trunc_le n).is_strictly_le n)

lemma trunc_le.is_iso_ι_f_iff_d_eq_zero (K : cochain_complex C ℤ) (n i j : ℤ)
  (hij : i+1 = j) (hi : i = n) :
  is_iso ((trunc_le.ι K n).f i) ↔ K.d i j = 0 :=
begin
  split,
  { intro h,
    haveI : is_iso (trunc_le.ι_f K n i) := h,
    simp only [← cancel_epi (trunc_le.ι_f K n i),
      trunc_le.ι_comp_d_eq_zero K n i j hij hi, comp_zero], },
  { exact kernel_fork.is_limit.is_iso_ι_of_zero _ (trunc_le.ι_is_kernel K n i j hij hi), },
end

instance (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_le n] :
  is_iso (trunc_le.ι K n) :=
begin
  haveI : ∀ (i : ℤ), is_iso ((trunc_le.ι K n).f i),
  { intro i,
    by_cases hi : i < n,
    { exact trunc_le.is_iso_ι_f K n i hi, },
    { cases (not_lt.1 hi).lt_or_eq,
      { refine ⟨⟨0, _, (is_strictly_le.is_zero K n i h).eq_of_tgt _ _⟩⟩,
        rw ← cancel_mono (trunc_le.ι_f K n i),
        apply (is_strictly_le.is_zero K n i h).eq_of_tgt, },
      { rw trunc_le.is_iso_ι_f_iff_d_eq_zero K n i (i+1) (by linarith) h.symm,
        apply (is_strictly_le.is_zero K n (i+1) (by linarith)).eq_of_tgt, }, }, },
  apply homological_complex.hom.is_iso_of_components,
end

end cochain_complex

namespace derived_category

variable (C)

def trunc_le_functor (n : ℤ) : derived_category C ⥤ derived_category C :=
localization.lift _ (cochain_complex.trunc_le_functor_comp_Q_inverts_quasi_isomorphisms C n) Q

instance (n : ℤ) : localization.lifting Q (quasi_isomorphisms _ _)
  (cochain_complex.trunc_le_functor C n ⋙ derived_category.Q) (trunc_le_functor C n) :=
localization.lifting_lift _ _ _

def trunc_le_functor_iso (n : ℤ) :
  Q ⋙ trunc_le_functor C n ≅ (cochain_complex.trunc_le_functor C n ⋙ derived_category.Q) :=
localization.lifting.iso _ (quasi_isomorphisms _ _) _ _

def trunc_le_nat_trans_ι (n : ℤ) : trunc_le_functor C n ⟶ 𝟭 (derived_category C) :=
localization.lift_nat_trans Q (quasi_isomorphisms _ _)
  (cochain_complex.trunc_le_functor C n ⋙ derived_category.Q) Q _ _
  (whisker_right (cochain_complex.trunc_le.nat_trans_ι C n) Q)

@[simp]
lemma trunc_le_nat_trans_ι_app (K : cochain_complex C ℤ) (n : ℤ) :
  (trunc_le_nat_trans_ι C n).app (Q.obj K) =
    (trunc_le_functor_iso C n).hom.app K ≫ Q.map (cochain_complex.trunc_le.ι K n) :=
begin
  dsimp only [trunc_le_nat_trans_ι, trunc_le_functor_iso],
  simp only [localization.lift_nat_trans_app, whisker_right_app,
    cochain_complex.trunc_le.nat_trans_ι_app,
    localization.lifting.id_iso, functor.right_unitor_inv_app, comp_id],
end

variable {C}

class is_le (K : derived_category C) (n : ℤ) : Prop :=
(is_zero' : ∀ (i : ℤ) (hi : n < i), is_zero (K.homology i))

lemma is_le.is_zero (K : derived_category C) (n i : ℤ) [K.is_le n]
  (hi : n < i) : is_zero (K.homology i) :=
is_le.is_zero' i hi

lemma is_le_of_le (K : derived_category C) (n m : ℤ) (hnm : n ≤ m) [K.is_le n] : K.is_le m :=
⟨λ i hi, is_le.is_zero K n i (by linarith)⟩

lemma is_le.of_iso {K L : derived_category C} (e : K ≅ L) (n : ℤ) [K.is_le n] : L.is_le n :=
⟨λ i hi, is_zero.of_iso (is_le.is_zero K n i hi) ((homology_functor _ i).map_iso e.symm)⟩

lemma is_le.iff_of_iso {K L : derived_category C} (e : K ≅ L) (n : ℤ) :
  K.is_le n ↔ L.is_le n :=
begin
  split,
  { introI,
    exact is_le.of_iso e n, },
  { introI,
    exact is_le.of_iso e.symm n, },
end

variable (C)

def Q_comp_trunc_le_functor_comp_homology_functor_iso (n i : ℤ) :
  Q ⋙ trunc_le_functor C n ⋙ homology_functor C i ≅
    cochain_complex.trunc_le_functor C n ⋙ _root_.homology_functor _ _ i :=
(functor.associator _ _ _).symm ≪≫
  iso_whisker_right (trunc_le_functor_iso C n) (homology_functor C i) ≪≫
  functor.associator _ _ _ ≪≫ iso_whisker_left _ (homology_functor_factors C i)

variable {C}

lemma is_zero_homology_trunc_le_of_lt (K : derived_category C) (n i : ℤ) (hi : n < i) :
  is_zero (((trunc_le_functor C n).obj K).homology i) :=
is_zero.of_iso (cochain_complex.is_le.is_zero _ n i hi)
  (((trunc_le_functor C n ⋙ homology_functor C i).map_iso (Q.obj_obj_preimage_iso K)).symm ≪≫
    ((Q_comp_trunc_le_functor_comp_homology_functor_iso C n i).app _))

lemma is_iso_homology_map_trunc_le_nat_trans_ι_of_le (K : derived_category C) (n i : ℤ)
  (hi : i ≤ n) :
  is_iso ((homology_functor C i).map ((trunc_le_nat_trans_ι C n).app K)) :=
begin
  erw ← (Q.obj_obj_preimage_iso K).is_iso_app_iff
    (whisker_right (trunc_le_nat_trans_ι C n) (homology_functor C i)),
  dsimp,
  erw [trunc_le_nat_trans_ι_app, functor.map_comp],
  haveI : ∀ (L : cochain_complex C ℤ), is_iso ((homology_functor C i).map (Q.map
    (cochain_complex.trunc_le.ι L n))),
  { intro L,
    erw nat_iso.is_iso_map_iff (homology_functor_factors C i),
    exact cochain_complex.trunc_le.is_iso_homology_map_ι L n i hi, },
  apply_instance,
end

lemma is_iso_trunc_le_nat_trans_ι_app_iff (K : derived_category C) (n : ℤ) :
  is_iso ((trunc_le_nat_trans_ι C n).app K) ↔ K.is_le n :=
begin
  rw is_iso_iff_is_iso_homology,
  split,
  { introI hK,
    exact ⟨λ i hi, is_zero.of_iso (is_zero_homology_trunc_le_of_lt K n i hi)
      (as_iso ((homology_functor C i).map ((trunc_le_nat_trans_ι C n).app K))).symm⟩, },
  { introI,
    intro i,
    by_cases hi : i ≤ n,
    { exact is_iso_homology_map_trunc_le_nat_trans_ι_of_le K n i hi, },
    { simp only [not_le] at hi,
      exact ⟨⟨0, (is_zero_homology_trunc_le_of_lt K n i hi).eq_of_src _ _,
        (is_le.is_zero K n i hi).eq_of_src _ _⟩⟩, }, },
end

instance is_iso_trunc_le_nat_trans_ι_of_le (K : derived_category C) (n : ℤ) [K.is_le n] :
  is_iso ((trunc_le_nat_trans_ι C n).app K) :=
by { rw is_iso_trunc_le_nat_trans_ι_app_iff, apply_instance, }

end derived_category

namespace cochain_complex

lemma is_le_iff_Q_obj_is_le (K : cochain_complex C ℤ) (n : ℤ) :
  K.is_le n ↔ (derived_category.Q.obj K).is_le n :=
begin
  split,
  { introI,
    exact ⟨λ i hi, by simpa only [← is_zero_homology_iff_is_zero_homology_Q_obj]
      using is_le.is_zero K n i hi⟩, },
  { introI,
    exact ⟨λ i hi, by simpa only [is_zero_homology_iff_is_zero_homology_Q_obj]
      using derived_category.is_le.is_zero (derived_category.Q.obj _) n i hi⟩, },
end

lemma is_le_iff_of_quasi_iso {K L : cochain_complex C ℤ} (φ : K ⟶ L) [quasi_iso φ] (n : ℤ) :
  K.is_le n ↔ L.is_le n :=
begin
  simp only [is_le_iff_Q_obj_is_le],
  exact derived_category.is_le.iff_of_iso (as_iso (derived_category.Q.map φ)) n,
end

lemma quasi_iso_trunc_le_ι_iff (K : cochain_complex C ℤ) (n : ℤ) :
  quasi_iso (trunc_le.ι K n) ↔ K.is_le n :=
begin
  rw [is_le_iff_Q_obj_is_le, ← derived_category.is_iso_Q_map_iff,
    ← derived_category.is_iso_trunc_le_nat_trans_ι_app_iff,
    derived_category.trunc_le_nat_trans_ι_app],
  split,
  { introI,
    apply_instance, },
  { apply is_iso.of_is_iso_comp_left, },
end

end cochain_complex

namespace derived_category

lemma right_factorisation_of_is_le {K L : cochain_complex C ℤ} (φ : Q.obj K ⟶ Q.obj L) (n : ℤ)
  [K.is_le n] :
  ∃ (K' : cochain_complex C ℤ) (hK' : K'.is_strictly_le n) (s : K' ⟶ K) (f : K' ⟶ L) (hs : quasi_iso s),
    φ = (by { haveI := hs, exact inv (Q.map s), }) ≫ Q.map f :=
begin
  obtain ⟨K', s, f, hs, eq⟩ := right_factorisation φ,
  haveI := hs,
  haveI : quasi_iso ((cochain_complex.trunc_le.nat_trans_ι C n).app K'),
  { erw cochain_complex.quasi_iso_trunc_le_ι_iff,
    dsimp,
    rw cochain_complex.is_le_iff_of_quasi_iso s,
    apply_instance, },
  exact ⟨_, infer_instance,
    (cochain_complex.trunc_le.nat_trans_ι _ n).app K' ≫ s,
    (cochain_complex.trunc_le.nat_trans_ι _ n).app K' ≫ f, infer_instance,
    by simp only [eq, functor.map_comp, is_iso.eq_inv_comp, assoc, is_iso.hom_inv_id_assoc]⟩,
end

lemma left_factorisation_of_is_strictly_le {K L : cochain_complex C ℤ} (φ : Q.obj K ⟶ Q.obj L)
  (n : ℤ) [K.is_strictly_le n] [L.is_strictly_le n] :
  ∃ (L' : cochain_complex C ℤ) (hL' : L'.is_le n) (f : K ⟶ L') (s : L ⟶ L') (hs : quasi_iso s),
    φ = Q.map f ≫ (by { haveI := hs, exact inv (Q.map s), }) :=
begin
  obtain ⟨L', f, s, hs, eq⟩ := left_factorisation φ,
  haveI := hs,
  haveI : quasi_iso (cochain_complex.trunc_le.ι L' n),
  { rw [cochain_complex.quasi_iso_trunc_le_ι_iff, ← cochain_complex.is_le_iff_of_quasi_iso s],
    apply_instance, },
  refine ⟨_, infer_instance,
    category_theory.inv (cochain_complex.trunc_le.ι K n) ≫
      (cochain_complex.trunc_le_functor C n).map f,
    category_theory.inv (cochain_complex.trunc_le.ι L n) ≫
    (cochain_complex.trunc_le_functor C n).map s, infer_instance, _⟩,
  have comms := Q.congr_map ((cochain_complex.trunc_le.nat_trans_ι C n).naturality s),
  have commf := Q.congr_map ((cochain_complex.trunc_le.nat_trans_ι C n).naturality f),
  dsimp at comms commf,
  simp only [Q.map_comp, ← cancel_mono (inv (Q.map ((cochain_complex.trunc_le.ι L' n)))),
    assoc, is_iso.hom_inv_id, comp_id] at comms commf,
  simp only [comms, commf, eq, functor.map_comp, functor.map_inv, is_iso.inv_hom_id_assoc,
    is_iso.inv_comp, is_iso.inv_inv, assoc],
end

end derived_category
