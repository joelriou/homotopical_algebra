import for_mathlib.algebra.homology.derived_category

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

variables {C : Type*} [category C] [abelian C]

namespace category_theory.short_complex
/-- should be moved... -/

lemma exact.of_is_zero_X₂ {C : Type*} [category C] [has_zero_morphisms C]
  (S : short_complex C) (h : is_zero S.X₂) : S.exact :=
begin
  rw (homology_data.of_zeros S (h.eq_of_tgt _ _) (h.eq_of_src _ _)).exact_iff,
  exact h,
end

lemma quasi_iso.of_cokernel_cofork {C : Type*} [category C] [has_zero_morphisms C]
  {S₁ S₂ : short_complex C} (φ : S₁ ⟶ S₂) [S₁.has_homology] [S₂.has_homology]
  [mono φ.τ₃] (hf₂ : S₂.f = 0) (hτ₂ : is_colimit (cokernel_cofork.of_π φ.τ₂
    (show S₁.f ≫ φ.τ₂ = 0, by rw [← φ.comm₁₂, hf₂, comp_zero]))) :
  short_complex.quasi_iso φ :=
begin
  have w : S₁.f ≫ φ.τ₂ = 0 := by rw [← φ.comm₁₂, hf₂, comp_zero],
  let h₁ := S₁.some_right_homology_data,
  let e : S₂.X₂ ≅ h₁.Q := is_colimit.cocone_point_unique_up_to_iso hτ₂ h₁.hp,
  have he : φ.τ₂ ≫ e.hom = h₁.p :=
    is_colimit.comp_cocone_point_unique_up_to_iso_hom hτ₂ h₁.hp walking_parallel_pair.one,
  have wp : S₂.f ≫ e.hom = 0 := by simp only [hf₂, zero_comp],
  let hp : is_colimit (cokernel_cofork.of_π e.hom wp) :=
    cokernel_cofork.is_colimit.of_π _ _ (λ A x hx, e.inv ≫ x)
      (λ A x hx, e.hom_inv_id_assoc _) (λ A x hx b hb, by simp only [←hb, iso.inv_hom_id_assoc]),
  have comm : e.inv ≫ S₂.g = h₁.g' ≫ φ.τ₃,
  { rw [← cancel_epi h₁.p, h₁.p_g'_assoc, ← φ.comm₂₃, ← he, assoc, e.hom_inv_id_assoc], },
  have wι : h₁.ι ≫ e.inv ≫ S₂.g = 0 :=
    by simp only [comm, right_homology_data.ι_g'_assoc, zero_comp],
  have hι : is_limit (kernel_fork.of_ι h₁.ι wι) := kernel_fork.is_limit.of_ι _ _
      (λ A x hx, h₁.hι.lift (kernel_fork.of_ι _
        (show x ≫ h₁.g' = 0, by rw [← cancel_mono φ.τ₃, assoc, ← comm, hx, zero_comp])))
      (λ A x hx, fork.is_limit.lift_ι' _ _)
      (λ A x hx b hb, by { erw [← cancel_mono h₁.ι, hb, fork.is_limit.lift_ι'], refl, }),
  let h₂ : S₂.right_homology_data :=
  { Q := h₁.Q,
    H := h₁.H,
    p := e.hom,
    wp := wp,
    hp := hp,
    ι := h₁.ι,
    wι := wι,
    hι := hι, },
  let hφ : right_homology_map_data φ h₁ h₂ :=
  { φQ := 𝟙 _,
    φH := 𝟙 _,
    commp' := begin
      dsimp [h₂],
      simp only [comp_id, he],
    end, },
  rw hφ.quasi_iso_iff,
  dsimp,
  apply_instance,
end

end category_theory.short_complex

open category_theory category_theory.limits category_theory.category

namespace cochain_complex

variables (K L : cochain_complex C ℤ)

def trunc_ge.X (n : ℤ) (i : ℤ) : C :=
if i < n
  then 0
  else if i = n
    then (homological_complex.short_complex_functor C (complex_shape.up ℤ) i ⋙
      short_complex.cycles_co_functor C).obj K
    else K.X i

lemma trunc_ge.is_zero_X (n : ℤ) (i : ℤ) (hn : i < n) :
  is_zero (trunc_ge.X K n i) :=
begin
  dsimp [trunc_ge.X],
  simpa only [if_pos hn] using is_zero_zero C,
end

def trunc_ge.X_iso_X (n : ℤ) (i : ℤ) (hn : n < i) :
  trunc_ge.X K n i ≅ K.X i :=
eq_to_iso begin
  dsimp [trunc_ge.X],
  rw [if_neg (show ¬i<n, by linarith), if_neg (show i ≠ n, by linarith)],
end

def trunc_ge.X_iso_cycles_co (n : ℤ) (i : ℤ) (hn : i = n) :
  trunc_ge.X K n i ≅ (K.sc' i).cycles_co :=
eq_to_iso begin
  dsimp [trunc_ge.X],
  simpa only [if_neg (show ¬ i<n, by linarith), if_pos hn],
end

def trunc_ge.d (n : ℤ) (i j : ℤ) : trunc_ge.X K n i ⟶ trunc_ge.X K n j :=
begin
  by_cases hij : i+1 = j,
  { by_cases hi₀ : i<n,
    { exact 0, },
    { by_cases hn : i = n,
      { refine (trunc_ge.X_iso_cycles_co K n i hn).hom ≫
          short_complex.desc_cycles_co _ (K.d i j ≫ (trunc_ge.X_iso_X K n j (by linarith)).inv) _,
        have hj : j = (complex_shape.up ℤ).next i,
        { rw [next],
          linarith, },
        subst hj,
        erw [reassoc_of ((homological_complex.sc' K i).zero), zero_comp], },
      { exact (trunc_ge.X_iso_X K n i (by { cases (not_lt.1 hi₀).lt_or_eq; tauto, })).hom ≫
          K.d i j ≫ (trunc_ge.X_iso_X K n j (by linarith)).inv, }, }, },
  { exact 0, },
end

def trunc_ge.π_f (n i : ℤ) : K.X i ⟶ trunc_ge.X K n i :=
begin
  by_cases hi : i < n,
  { exact 0, },
  { by_cases hn : i = n,
    { exact (K.sc' i).p_cycles_co ≫ (trunc_ge.X_iso_cycles_co K n i hn).inv, },
    { exact (trunc_ge.X_iso_X K n i (by { cases (not_lt.1 hi).lt_or_eq; tauto, })).inv, }, },
end

instance (n i : ℤ) : epi (trunc_ge.π_f K n i) :=
begin
  dsimp [trunc_ge.π_f],
  by_cases h₀ : i < n,
  { rw dif_pos h₀,
    constructor,
    intros Z f₁ f₂ eq,
    apply (trunc_ge.is_zero_X K n i h₀).eq_of_src, },
  { rw dif_neg h₀,
    by_cases hn : i = n,
    { rw dif_pos hn,
      apply epi_comp, },
    { rw dif_neg hn,
      apply_instance, }, },
end

lemma trunc_ge.is_iso_π_f (n i : ℤ) (hi : n < i) :
  is_iso (trunc_ge.π_f K n i) :=
begin
  dsimp [trunc_ge.π_f],
  simp only [dif_neg (show ¬ i < n, by linarith),
    dif_neg (show i ≠ n, by linarith)],
  apply_instance,
end

lemma trunc_ge.π_f_eq_zero (n i : ℤ) (hi : i < n) :
  trunc_ge.π_f K n i = 0 :=
by { dsimp [trunc_ge.π_f], rw [dif_pos hi], }

lemma trunc_ge.π_f_eq_of_eq (n i : ℤ) (hn : i = n) :
  trunc_ge.π_f K n i = (K.sc' i).p_cycles_co ≫ (trunc_ge.X_iso_cycles_co K n i hn).inv :=
by { dsimp [trunc_ge.π_f], rw [dif_neg (show ¬i<n, by linarith), dif_pos hn], }

lemma trunc_ge.π_f_eq_X_iso_X_inv (n i : ℤ) (hi : n < i) :
  trunc_ge.π_f K n i = (trunc_ge.X_iso_X K n i hi).inv :=
by { dsimp [trunc_ge.π_f], rw [dif_neg, dif_neg]; linarith, }

lemma trunc_ge.shape (n i j : ℤ) (hij : i+1 ≠ j) : trunc_ge.d K n i j = 0 :=
by { dsimp only [trunc_ge.d], rw dif_neg hij, }

lemma trunc_ge.d_eq_zero (n : ℤ) (i j : ℤ) (hj : j ≤ n) :
  trunc_ge.d K n i j = 0 :=
begin
  by_cases hij : i+1 = j,
  { dsimp [trunc_ge.d],
    rw [dif_pos hij, dif_pos],
    linarith, },
  { rw trunc_ge.shape K n i j hij, },
end

lemma trunc_ge.d_eq_d (n : ℤ) (i j : ℤ) (hij : i + 1 = j) (hi : n < i) :
  trunc_ge.d K n i j = (trunc_ge.X_iso_X K n i hi).hom ≫ K.d i j ≫
    (trunc_ge.X_iso_X K n j (by simpa only [← hij] using hi.trans (lt_add_one i))).inv :=
by { dsimp [trunc_ge.d], rw [dif_pos hij, dif_neg, dif_neg]; linarith, }

lemma trunc_ge.d_comp_π_eq_zero (n : ℤ) (i j : ℤ) (hij : i + 1 = j) (hj : j = n) :
  K.d i j ≫ trunc_ge.π_f K n j = 0 :=
begin
  have hi : i = (complex_shape.up ℤ).prev j := by { rw [prev], linarith, },
  subst hi,
  dsimp [trunc_ge.π_f],
  erw [dif_neg (show ¬j<n, by linarith), dif_pos hj, ← assoc,
    (homological_complex.sc' K j).f_cycles_co_p, zero_comp],
end

def trunc_ge.π_is_cokernel (n i j : ℤ) (hij : i + 1 = j) (hj : j = n) :
  is_colimit (cokernel_cofork.of_π _ (trunc_ge.d_comp_π_eq_zero K n i j hij hj)) :=
begin
  have hij' : i = (complex_shape.up ℤ).prev j := by { rw [prev], linarith, },
  subst hij',
  exact is_colimit.of_iso_colimit (homological_complex.sc' K j).cycles_co_is_cokernel
    (cofork.ext (trunc_ge.X_iso_cycles_co K n j hj).symm (trunc_ge.π_f_eq_of_eq K n j hj).symm),
end

@[simp, reassoc]
lemma trunc_ge.d_comm (n i j : ℤ) :
  trunc_ge.π_f K n i ≫ trunc_ge.d K n i j =
    K.d i j ≫ trunc_ge.π_f K n j :=
begin
  by_cases hij : i+1 = j,
  { by_cases hj₀ : j < n,
    { apply (trunc_ge.is_zero_X K n j hj₀).eq_of_tgt, },
    by_cases hj : j = n,
    { simp only [trunc_ge.d_comp_π_eq_zero K n i j hij hj,
        trunc_ge.d_eq_zero K n i j (by linarith), comp_zero], },
    by_cases hi : i = n,
    { dsimp [trunc_ge.d, trunc_ge.π_f],
      simp only [dif_pos hij, dif_neg (show ¬ i < n, by linarith), dif_pos hi, dif_neg hj₀,
        trunc_ge.π_f_eq_X_iso_X_inv K n j (by linarith), assoc, iso.inv_hom_id_assoc,
        dif_neg hj, short_complex.p_desc_cycles_co], },
    { have hi' : n < i,
      { subst hij,
        cases (not_lt.1 hj₀).lt_or_eq,
        { rw int.lt_add_one_iff at h,
          cases h.lt_or_eq with h' h',
          { exact h', },
          { exfalso, exact hi h'.symm, }, },
        { exfalso, exact hj h.symm, }, },
      simp only [trunc_ge.d_eq_d K n i j hij hi', trunc_ge.π_f_eq_X_iso_X_inv K n i hi',
        trunc_ge.π_f_eq_X_iso_X_inv K n j (by linarith), iso.inv_hom_id_assoc], }, },
  { rw [trunc_ge.shape K n i j hij, K.shape i j hij, zero_comp, comp_zero], },
end

@[simp, reassoc]
lemma trunc_ge.d_comp_d (n i j k : ℤ) : trunc_ge.d K n i j ≫ trunc_ge.d K n j k = 0 :=
by simp only [← cancel_epi (trunc_ge.π_f K n i), trunc_ge.d_comm_assoc,
  trunc_ge.d_comm, homological_complex.d_comp_d_assoc, zero_comp, comp_zero]

@[simps]
def trunc_ge (n : ℤ) : cochain_complex C ℤ :=
{ X := trunc_ge.X K n,
  d := trunc_ge.d K n,
  shape' := trunc_ge.shape K n,
  d_comp_d' := λ i j k hij hjk, trunc_ge.d_comp_d K n i j k, }

@[simps]
def trunc_ge.π (n : ℤ) : K ⟶ K.trunc_ge n :=
{ f := trunc_ge.π_f K n,
  comm' := λ i j hij, trunc_ge.d_comm K n i j, }

variables {K L}

def trunc_ge.map_f (φ : K ⟶ L) (n i : ℤ) :
  (K.trunc_ge n).X i ⟶ (L.trunc_ge n).X i :=
begin
  by_cases hi : n < i,
  { exact (trunc_ge.X_iso_X K n i hi).hom ≫ φ.f i ≫
    (trunc_ge.X_iso_X L n i hi).inv, },
  { by_cases hn : i = n,
    { exact (trunc_ge.X_iso_cycles_co K n i hn).hom ≫ (homological_complex.short_complex_functor C (complex_shape.up ℤ) i ⋙
        short_complex.cycles_co_functor C).map φ ≫ (trunc_ge.X_iso_cycles_co L n i hn).inv, },
    { exact 0, }, },
end

lemma trunc_ge.map_f_eq_f (φ : K ⟶ L) (n i : ℤ) (hi : n < i) :
  trunc_ge.map_f φ n i = (trunc_ge.X_iso_X K n i hi).hom ≫ φ.f i ≫
    (trunc_ge.X_iso_X L n i hi).inv :=
begin
  dsimp only [trunc_ge.map_f],
  simp only [dif_pos hi],
end

@[simp, reassoc]
lemma trunc_ge.π_f_comm_map_f (φ : K ⟶ L) (n i : ℤ) :
  trunc_ge.π_f K n i ≫ trunc_ge.map_f φ n i =
    φ.f i ≫ trunc_ge.π_f L n i :=
begin
  by_cases hi : n < i,
  { simp only [trunc_ge.π_f_eq_X_iso_X_inv _ n i hi,
      trunc_ge.map_f_eq_f φ n i hi, iso.inv_hom_id_assoc], },
  { by_cases hn : i = n,
    { dsimp [trunc_ge.map_f, trunc_ge.π_f],
      simp only [dif_neg hi, dif_pos hn, dif_neg (show ¬ i < n, by linarith), assoc,
        iso.inv_hom_id_assoc],
      exact ((short_complex.p_cycles_co_nat_trans C).naturality_assoc
        ((homological_complex.short_complex_functor C (complex_shape.up ℤ) i).map φ) _).symm, },
    { refine (trunc_ge.is_zero_X L n i _).eq_of_tgt _ _,
      cases (not_lt.1 hi).lt_or_eq,
      { exact h, },
      { exfalso, exact hn h, }, }, },
end

@[reassoc]
lemma trunc_ge.map_comm_f (φ : K ⟶ L) (n i j : ℤ) :
  trunc_ge.map_f φ n i ≫ trunc_ge.d L n i j =
    trunc_ge.d K n i j ≫ trunc_ge.map_f φ n j :=
by simp only [← cancel_epi (trunc_ge.π_f K n i), trunc_ge.π_f_comm_map_f_assoc,
  trunc_ge.d_comm, homological_complex.hom.comm_assoc,
  trunc_ge.d_comm_assoc, trunc_ge.π_f_comm_map_f]

@[simp]
lemma trunc_ge.map_id_f (K : cochain_complex C ℤ) (n i : ℤ) :
  trunc_ge.map_f (𝟙 K) n i = 𝟙 _ :=
begin
  simp only [← cancel_epi (trunc_ge.π_f K n i), trunc_ge.π_f_comm_map_f,
    homological_complex.id_f, id_comp],
  erw comp_id,
end

@[simp]
lemma trunc_ge.map_comp_f {K L M : cochain_complex C ℤ}
  (φ : K ⟶ L) (φ' : L ⟶ M) (n i : ℤ) :
  trunc_ge.map_f (φ ≫ φ') n i =
    trunc_ge.map_f φ n i ≫ trunc_ge.map_f φ' n i :=
by simp only [← cancel_epi (trunc_ge.π_f K n i), trunc_ge.π_f_comm_map_f,
    homological_complex.comp_f, assoc, trunc_ge.π_f_comm_map_f_assoc]

variable (C)

@[simps]
def trunc_ge_functor (n : ℤ) :
  cochain_complex C ℤ ⥤ cochain_complex C ℤ :=
{ obj := λ K, K.trunc_ge n,
  map := λ K L φ,
  { f := λ i, trunc_ge.map_f φ n i,
    comm' := λ i j hij, trunc_ge.map_comm_f φ n i j, }, }

@[simps]
def trunc_ge.nat_trans_π (n : ℤ) :
  𝟭 _ ⟶ trunc_ge_functor C n :=
{ app := λ K, trunc_ge.π K n,
  naturality' := λ K L φ, begin
    ext i
    dsimp,
    simp only [functor.id_map, homological_complex.comp_f, trunc_ge_functor_map_f],
    dsimp,
    simp only [trunc_ge.π_f_comm_map_f],
  end, }

variables {C} (K)

lemma trunc_ge.is_zero_homology (n i : ℤ) (hi : i < n) :
  is_zero ((homology_functor C _ i).obj (K.trunc_ge n)) :=
begin
  dsimp [homology_functor],
  rw ← short_complex.exact_iff_is_zero_homology,
  exact short_complex.exact.of_is_zero_X₂ _ (trunc_ge.is_zero_X K n i hi),
end

lemma trunc_ge.is_iso_homology_map_π (n i : ℤ) (hi : n ≤ i) :
  is_iso ((homology_functor C _ i).map (trunc_ge.π K n)) :=
begin
  let φ := (homological_complex.short_complex_functor C (complex_shape.up ℤ) i).map
    (trunc_ge.π K n),
  haveI : is_iso φ.τ₃ := trunc_ge.is_iso_π_f K n _ (by { rw [next], linarith, }),
  cases hi.lt_or_eq,
  { haveI : epi φ.τ₁ := by { dsimp, apply_instance, },
    haveI : is_iso φ.τ₂ := trunc_ge.is_iso_π_f K n i h,
    exact short_complex.quasi_iso.of_epi_of_is_iso_of_mono φ, },
  { exact short_complex.quasi_iso.of_cokernel_cofork φ
      ((trunc_ge.is_zero_X K n _ (by { rw [prev], linarith, })).eq_of_src _ _)
      (trunc_ge.π_is_cokernel K n _ i (by { rw [prev], linarith, }) h.symm), },
end

variables {K L}

lemma trunc_ge.map_homology_iso (φ : K ⟶ L) (n i : ℤ) [is_iso (homology_map φ i)] :
  is_iso (homology_map ((trunc_ge_functor C n).map φ) i) :=
begin
  by_cases hi : n ≤ i,
  { have eq := (homology_functor C _ i).congr_map ((trunc_ge.nat_trans_π C n).naturality φ),
    simp only [functor.map_comp, functor.id_map, trunc_ge.nat_trans_π_app] at eq,
    change homology_map φ i ≫ homology_map (trunc_ge.π L n) i =
      homology_map (trunc_ge.π K n) i ≫ homology_map _ i at eq,
    haveI : ∀ (M : cochain_complex C ℤ), is_iso (homology_map (trunc_ge.π M n) i) :=
      λ M, trunc_ge.is_iso_homology_map_π M n i hi,
    simp only [← cancel_epi (inv (homology_map (trunc_ge.π K n) i)),
      is_iso.inv_hom_id_assoc] at eq,
    rw ← eq,
    apply_instance, },
  { simp only [not_le] at hi,
    exact ⟨⟨0, (trunc_ge.is_zero_homology K n i hi).eq_of_src _ _,
       (trunc_ge.is_zero_homology L n i hi).eq_of_src _ _⟩⟩, },
end

instance trunc_ge.map_quasi_iso (φ : K ⟶ L) (n : ℤ) [quasi_iso φ] :
  quasi_iso ((trunc_ge_functor _ n).map φ) :=
⟨λ i, trunc_ge.map_homology_iso φ n i⟩

variable (C)

lemma trunc_ge_functor_comp_Q_inverts_quasi_isomorphisms (n : ℤ) :
  (quasi_isomorphisms _ _).is_inverted_by
    (cochain_complex.trunc_ge_functor C n ⋙ derived_category.Q) :=
λ K L φ hφ, begin
  haveI : quasi_iso φ := by simpa only [← mem_quasi_isomorphisms_iff] using hφ,
  dsimp,
  apply_instance,
end

end cochain_complex

namespace derived_category

variable (C)

def trunc_ge_functor (n : ℤ) : derived_category C ⥤ derived_category C :=
localization.lift _ (cochain_complex.trunc_ge_functor_comp_Q_inverts_quasi_isomorphisms C n) Q

instance (n : ℤ) : localization.lifting Q (quasi_isomorphisms _ _)
  (cochain_complex.trunc_ge_functor C n ⋙ derived_category.Q) (trunc_ge_functor C n) :=
localization.lifting_lift _ _ _

def trunc_ge_functor_iso (n : ℤ) :
  Q ⋙ trunc_ge_functor C n ≅ (cochain_complex.trunc_ge_functor C n ⋙ derived_category.Q) :=
localization.lifting.iso _ (quasi_isomorphisms _ _) _ _

end derived_category
