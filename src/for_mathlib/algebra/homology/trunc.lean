import for_mathlib.algebra.homology.derived_category

noncomputable theory

open category_theory category_theory.limits category_theory.category
open_locale zero_object

variables {C : Type*} [category C] [abelian C]

namespace category_theory.short_complex

lemma exact.of_is_zero_X₂ {C : Type*} [category C] [has_zero_morphisms C]
  (S : short_complex C) (h : is_zero S.X₂) : S.exact :=
begin
  rw (homology_data.of_zeros S (h.eq_of_tgt _ _) (h.eq_of_src _ _)).exact_iff,
  exact h,
end

end category_theory.short_complex

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

example : ℕ := 42

variables {C} (K)

lemma trunc_ge.is_zero_homology (n i : ℤ) (hi : i < n) :
  is_zero ((homology_functor C _ i).obj (K.trunc_ge n)) :=
begin
  dsimp [homology_functor],
  rw ← short_complex.exact_iff_is_zero_homology,
  exact category_theory.short_complex.exact.of_is_zero_X₂ _ (trunc_ge.is_zero_X K n i hi),
end

lemma trunc_ge.is_iso_homology_map_π (n i : ℤ) (hi : n ≤ i) :
  is_iso ((homology_functor C _ i).map (trunc_ge.π K n)) :=
begin
  by_cases hn : i = n,
  { sorry, },
  { by_cases hn : i = n+1,
    { sorry, },
    { let f := (homological_complex.short_complex_functor C
        (complex_shape.up ℤ) i).map (trunc_ge.π K n),
      haveI : is_iso f := begin
        /- short_complex.is_iso_of_is_iso_of_is_iso_of_is_iso
          more generally short_complex.quasi_iso_of_epi_of_is_iso_of_mono ? -/
        sorry,
      end,
      exact short_complex.quasi_iso_of_iso f, }, },
end

end cochain_complex
