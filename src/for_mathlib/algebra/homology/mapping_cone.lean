import for_mathlib.algebra.homology.twist_cocycle
import algebra.homology.quasi_iso
import algebra.homology.short_complex.pseudoelements
import for_mathlib.algebra.homology.hom_complex_shift
import category_theory.triangulated.triangulated
import for_mathlib.algebra.homology.homological_complex_limits

noncomputable theory
open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated

@[simp]
lemma category_theory.limits.biprod.is_zero_iff {C : Type*} [category C]
  [has_zero_morphisms C] (A B : C)
  [has_binary_biproduct A B] : is_zero (biprod A B) ↔ is_zero A ∧ is_zero B :=
begin
  split,
  { intro h,
    simp only [is_zero.iff_id_eq_zero],
    split,
    { rw ← cancel_mono (biprod.inl : _ ⟶ A ⊞ B),
      apply h.eq_of_tgt, },
    { rw ← cancel_mono (biprod.inr : _ ⟶ A ⊞ B),
      apply h.eq_of_tgt, }, },
  { rintro ⟨h₁, h₂⟩,
    rw is_zero.iff_id_eq_zero,
    ext1,
    { apply h₁.eq_of_src, },
    { apply h₂.eq_of_src, }, },
end

namespace cochain_complex

variables {C : Type*} [category C]

section preadditive

variables [preadditive C]
  {F G : cochain_complex C ℤ} [∀ p, has_binary_biproduct (F.X (p+1-(0 : ℤ))) (G.X p)]
  (φ : F ⟶ G)

open hom_complex

def mapping_cone : cochain_complex C ℤ :=
twist (cocycle.of_hom φ)

namespace mapping_cone

lemma X_is_zero_iff (n : ℤ) :
  is_zero ((mapping_cone φ).X n) ↔ is_zero (F.X (n+1)) ∧ is_zero (G.X n) :=
begin
  dsimp [mapping_cone],
  simp only [tsub_zero, category_theory.limits.biprod.is_zero_iff, and.congr_left_iff],
  intro h,
  congr',
end

def inl : cochain F (mapping_cone φ) (-1) :=
twist.inl (cocycle.of_hom φ) (neg_add_self 1)

def inr : G ⟶ mapping_cone φ :=
twist.inr (cocycle.of_hom φ)

def fst : cocycle (mapping_cone φ) F 1 :=
  twist.fst (cocycle.of_hom φ) (zero_add 1)

def snd : cochain (mapping_cone φ) G 0 :=
  twist.snd (cocycle.of_hom φ)

@[simp, reassoc]
lemma inl_fst (p q : ℤ) (hpq : p = q+1) :
  (inl φ).v p q (by rw [hpq, int.add_neg_one, add_tsub_cancel_right]) ≫
     (fst φ : cochain (mapping_cone φ) F 1).v q p hpq = 𝟙 _ :=
by simpa only [cochain.comp_v _ _ (neg_add_self 1).symm p q p (by linarith) hpq,
  cochain.of_hom_v, homological_complex.id_f]
  using cochain.congr_v (twist.inl_comp_fst _ (neg_add_self 1) (zero_add 1)) p p  (by linarith)

@[simp, reassoc]
lemma inl_snd (p q : ℤ) (hpq : q = p+(-1)) :
  (inl φ).v p q hpq ≫ (snd φ).v q q (add_zero q).symm = 0 :=
by simpa only [cochain.comp_zero_cochain] using
  cochain.congr_v (twist.inl_comp_snd (cocycle.of_hom φ) (neg_add_self 1)) p q hpq

@[simp]
lemma inl_comp_fst :
  (inl φ).comp (fst φ : cochain (mapping_cone φ) F 1)
    (neg_add_self 1).symm = cochain.of_hom (𝟙 _) :=
begin
  ext p,
  simp only [cochain.comp_v _ _ (neg_add_self 1).symm p (p-1) p (by linarith) (by linarith),
    inl_fst, cochain.of_hom_v, homological_complex.id_f],
end

@[simp]
lemma inl_comp_snd :
  (inl φ).comp (snd φ) (add_zero _).symm = 0 :=
by tidy

@[simp, reassoc]
lemma inr_snd (p : ℤ) :
  (inr φ).f p ≫ (snd φ).v p p (add_zero p).symm = 𝟙 _ :=
by simpa only [cochain.comp_v _ _ (add_zero 0).symm p p p (by linarith) (by linarith),
  cochain.of_hom_v, homological_complex.id_f]
  using cochain.congr_v (twist.inr_comp_snd (cocycle.of_hom φ)) p p (add_zero p).symm

@[simp, reassoc]
lemma inr_fst (p q : ℤ) (hpq : q = p+1) :
  (inr φ).f p ≫ (fst φ : cochain (mapping_cone φ) F 1).v p q hpq = 0 :=
by simpa only [cochain.zero_cochain_comp, cochain.of_hom_v, cochain.zero_v]
  using cochain.congr_v (twist.inr_comp_fst (cocycle.of_hom φ) (zero_add 1)) p q hpq

@[simp]
lemma inr_comp_fst :
  (cochain.of_hom (inr φ)).comp
    (fst φ : cochain (mapping_cone φ) F 1) (zero_add 1).symm = 0 :=
by tidy

@[simp]
lemma inr_comp_snd :
  (cochain.of_hom (inr φ)).comp
    (snd φ : cochain (mapping_cone φ) G 0) (zero_add 0).symm = cochain.of_hom (𝟙 _) :=
by tidy

@[simps]
def δ_as_cocycle : cocycle (mapping_cone φ) F 1 :=
-fst φ

def δ : mapping_cone φ ⟶ F⟦(1 : ℤ)⟧ :=
cocycle.hom_of
  (cocycle.right_shift (δ_as_cocycle φ) 1 0 (zero_add 1).symm)

@[simp, priority 1100]
lemma inr_δ : inr φ ≫ δ φ = 0 :=
begin
  ext n,
  dsimp only [δ],
  simp only [homological_complex.comp_f, cocycle.hom_of_f, cochain.neg_v,
    cocycle.right_shift_coe, δ_as_cocycle_coe, homological_complex.zero_f_apply,
    hom_complex.cochain.right_shift_v _ 1 0 (zero_add 1).symm n n (by linarith) _ rfl,
    preadditive.neg_comp, preadditive.comp_neg, inr_fst_assoc, zero_comp, neg_zero],
end

@[simp]
lemma inl_δ :
  (inl φ).comp (cochain.of_hom (δ φ)) (add_zero _).symm =
  -(cochain.of_hom (𝟙 F)).right_shift _ _ (add_neg_self 1).symm :=
begin
  /- TODO deduplicate the proof of this and the lemma above -/
  ext p q hpq,
  simp only [cochain.comp_zero_cochain, cochain.of_hom_v, δ,
    cocycle.hom_of_f, cocycle.right_shift_coe, δ_as_cocycle_coe,
    hom_complex.cochain.right_shift_v _ 1 0 (zero_add 1).symm q q (by linarith) p (by linarith),
    hom_complex.cochain.right_shift_v _ 1 (-1) (add_neg_self 1).symm p q hpq p (by linarith),
    cochain.neg_v, preadditive.comp_neg, preadditive.neg_comp, cochain.neg_v,
    inl_fst_assoc, homological_complex.id_f, id_comp],
end

lemma ext_to {A : C} {n : ℤ} (f₁ f₂ : A ⟶ (mapping_cone φ).X n) (n' : ℤ) (hn' : n' = n+1)
  (h₁ : f₁ ≫ (fst φ : cochain (mapping_cone φ) F 1).v n n' hn' = f₂ ≫ (fst φ).1.v n n' hn')
  (h₂ : f₁ ≫ (snd φ).v n n (add_zero n).symm =
    f₂ ≫ (snd φ).v n n (add_zero n).symm) : f₁ = f₂ :=
begin
  have h' : n' = n+1-0 := by linarith,
  subst h',
  ext,
  { dsimp [fst, twist.fst] at h₁,
    simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id] using h₁, },
  { dsimp [snd, twist.snd] at h₂,
    simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id] using h₂, },
end

@[simp]
lemma δ_inl :
  hom_complex.δ (-1) 0 (inl φ) = cochain.of_hom (φ ≫ inr φ) :=
begin
  dsimp only [inl],
  simpa only [twist.δ_inl (cocycle.of_hom φ) (neg_add_self 1), cochain.of_hom_comp],
end

@[simp]
lemma δ_snd :
  hom_complex.δ 0 1 (snd φ) = -(fst φ : cochain (mapping_cone φ) F 1).comp
    (cochain.of_hom φ) (add_zero 1).symm :=
twist.δ_snd (cocycle.of_hom φ) (zero_add 1)

lemma of_d_eq : cochain.of_d (mapping_cone φ) =
  -((fst φ : cochain (mapping_cone φ) F 1).comp (cochain.of_d F)
    (show (2 : ℤ) = 1+1, by refl)).comp (inl φ) (show (1 : ℤ) = 2 + (-1), by refl) +
  ((fst φ : cochain (mapping_cone φ) F 1).comp (cochain.of_hom φ) (add_zero 1).symm).comp
      (cochain.of_hom (inr φ)) (add_zero 1).symm +
  ((snd φ).comp (cochain.of_d G) (zero_add 1).symm).comp
    (cochain.of_hom (inr φ)) (add_zero 1).symm :=
begin
  dsimp only [mapping_cone],
  simpa only [twist.of_d_eq (cocycle.of_hom φ) 1 2 (-1) rfl rfl rfl, zero_add, ε_1,
    neg_smul, one_smul],
end

@[reassoc]
lemma inl_d (n₁ n₂ n₃ : ℤ) (h₁₂ : n₁ = n₂ + (-1)) (h₂₃ : n₂ = n₃ + (-1)) :
  (inl φ).v n₂ n₁ h₁₂ ≫ (mapping_cone φ).d n₁ n₂ =
    φ.f n₂ ≫ (inr φ).f n₂ - F.d n₂ n₃ ≫ (inl φ).v _ _ h₂₃ :=
begin
  simp only [← hom_complex.cochain.of_d_v (mapping_cone φ) n₁ n₂ (by linarith), of_d_eq,
    add_zero, cochain.comp_assoc_of_third_is_zero_cochain, cochain.add_v, cochain.neg_v,
    cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_cochain_comp,
    preadditive.comp_add, preadditive.comp_neg, inl_fst_assoc,
    inl_snd_assoc, zero_comp],
  erw cochain.comp_v _ _ (show (1 : ℤ) = 2 + (-1), by linarith) n₁ n₃ n₂ (by linarith) (by linarith),
  erw cochain.comp_v _ _ (show (2 : ℤ) = 1 + 1, by linarith) n₁ n₂ n₃ (by linarith) (by linarith),
  simp only [cochain.of_d_v, assoc, inl_fst_assoc, neg_add_eq_sub],
end

@[simp, reassoc]
lemma inr_d (n n' : ℤ) :
  (inr φ).f n ≫ (mapping_cone φ).d n n' =
    G.d n n' ≫ (inr φ).f n' :=
begin
  by_cases h : n+1 = n',
  { rw [← hom_complex.cochain.of_d_v (mapping_cone φ) _ _ h.symm, of_d_eq φ],
    simp only [cochain.comp_assoc_of_third_is_zero_cochain, cochain.add_v, cochain.neg_v,
      cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_cochain_comp, cochain.of_d_v,
      preadditive.comp_add, preadditive.comp_neg, inr_fst_assoc, zero_comp,
      inr_snd_assoc, add_left_eq_self, neg_eq_zero],
    erw cochain.comp_v _ _ (show (1 : ℤ)= 2 + (-1), by linarith) n (n+2) n' rfl (by linarith),
    erw cochain.comp_v _ _ (show (2 : ℤ) = 1 + 1, by linarith) n (n+1) (n+2) rfl (by linarith),
    simp only [assoc, inr_fst_assoc, zero_comp], },
  { simp only [G.shape _ _ h, (mapping_cone φ).shape _ _ h, comp_zero, zero_comp], },
end

lemma id (p q : ℤ) (hpq : q = p+1) :
  (fst φ : cochain (mapping_cone φ) F 1).v p q hpq ≫
    (inl φ).v q p (by rw [hpq, int.add_neg_one, add_tsub_cancel_right]) +
  (snd φ).v p p (add_zero p).symm ≫ (inr φ).f p = 𝟙 _ :=
begin
  have hq' : q = p+1-0 := by linarith,
  subst hq',
  dsimp [fst, snd, twist.fst, twist.snd, inl, inr, twist.inl, twist.inr],
  simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id, id_comp, biprod.total],
end

variable {φ}

lemma to_decomposition {A : C} {n : ℤ} (f : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  ∃ (x : A ⟶ F.X n') (y : A ⟶ G.X n), f = x ≫
    (inl φ : cochain F (mapping_cone φ) (-1)).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right])
      + y ≫ (inr φ).f n :=
begin
  refine ⟨f ≫ (fst φ : cochain (mapping_cone φ) F 1).v _ _ (by linarith), f ≫ (snd φ).v n n (by linarith), _⟩,
  have h := f ≫= id φ n n' h,
  rw comp_id at h,
  nth_rewrite 0 ← h,
  simp,
end

lemma to_ext_iff {A : C} {n : ℤ} (f g : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  f = g ↔ f ≫ (fst φ : cochain (mapping_cone φ) F 1).v _ _ h =
    g ≫ (fst φ : cochain (mapping_cone φ) F 1).v _ _ h ∧
    f ≫ (snd φ).v n n (add_zero n).symm =
      g ≫ (snd φ).v n n (add_zero n).symm :=
begin
  split,
  { intro h,
    rw h,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    rw [← cancel_mono (𝟙 ((mapping_cone φ).X n))],
    simp only [← id _ _ _ h, preadditive.comp_add, reassoc_of h₁, reassoc_of h₂], },
end

lemma from_ext_iff {A : C} {n : ℤ} (f g : (mapping_cone φ).X n ⟶ A)
  (n' : ℤ) (h : n' = n+1) :
  f = g ↔ (inl φ).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right]) ≫ f =
    (inl φ).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right]) ≫ g ∧
    (inr φ).f n ≫ f = (inr φ).f n ≫ g :=
begin
  split,
  { intro h,
    rw h,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    rw [← cancel_epi (𝟙 ((mapping_cone φ).X n))],
    simp only [← id _ _ _ h, preadditive.add_comp, assoc, h₁, h₂], },
end

lemma cochain_ext {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain (mapping_cone φ) K m) (hm' : m = m'+1) :
  y₁ = y₂ ↔ (inl φ).comp y₁ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) =
    (inl φ).comp y₂ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) ∧
    (cochain.of_hom (inr φ)).comp y₁ (zero_add m).symm =
      (cochain.of_hom (inr φ)).comp y₂ (zero_add m).symm :=
hom_complex.twist.cochain_ext _ _ _ _ _

lemma cochain_ext' {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain K (mapping_cone φ) m) (hm' : m' = m+1) :
  y₁ = y₂ ↔ y₁.comp (fst φ : cochain (mapping_cone φ) F 1) hm' =
    y₂.comp (fst φ : cochain (mapping_cone φ) F 1) hm' ∧
    y₁.comp (snd φ) (add_zero m).symm =
      y₂.comp (snd φ) (add_zero m).symm :=
hom_complex.twist.cochain_ext' _ _ _ _ _

@[reassoc]
lemma d_fst (n₁ n₂ n₃ : ℤ) (h₁₂ : n₂ = n₁ + 1) (h₂₃ : n₃ = n₂ + 1) :
  (mapping_cone φ).d n₁ n₂ ≫ (fst φ : cochain (mapping_cone φ) F 1).v n₂ n₃ h₂₃ =
  -(fst φ : cochain (mapping_cone φ) F 1).v n₁ n₂ h₁₂ ≫ F.d n₂ n₃ :=
begin
  rw from_ext_iff _ _ _ h₁₂,
  split,
  { simp only [inl_fst_assoc, preadditive.sub_comp, assoc, inr_fst,
      inl_d_assoc φ n₁ n₂ n₃ (by linarith) (by linarith), comp_zero, comp_id,
      inl_fst, zero_sub, preadditive.comp_neg, inl_fst_assoc], },
  { simp only [inr_d_assoc, inr_fst, comp_zero, preadditive.comp_neg,
      inr_fst_assoc, zero_comp, neg_zero], },
end

@[reassoc]
lemma d_snd (n₁ n₂ : ℤ) (h₁₂ : n₂ = n₁ + 1) :
  (mapping_cone φ).d n₁ n₂ ≫ (snd φ).v n₂ n₂ (add_zero n₂).symm =
    (fst φ : cochain (mapping_cone φ) F 1).v n₁ n₂ h₁₂ ≫ φ.f n₂ +
    (snd φ).v n₁ n₁ (add_zero n₁).symm ≫ G.d n₁ n₂ :=
begin
  rw from_ext_iff _ _ _ h₁₂,
  split,
  { simp only [add_zero, preadditive.comp_add, inl_fst_assoc, comp_id, comp_zero,
      inl_snd_assoc, zero_comp, preadditive.sub_comp, assoc, sub_zero,
      inl_d_assoc φ n₁ n₂ (n₂+1) (by linarith) (by linarith),
      inr_snd, inl_snd], },
  { simp only [inr_d_assoc, inr_snd, comp_id, preadditive.comp_add,
      inr_fst_assoc, zero_comp, inr_snd_assoc, zero_add], },
end

variable (φ)

@[simp]
def ι' := (homotopy_category.quotient _ _).map (inr φ)

def δ' : (homotopy_category.quotient _ _).obj (mapping_cone φ) ⟶
  ((homotopy_category.quotient _ _).obj F)⟦(1 : ℤ)⟧ :=
(homotopy_category.quotient _ _).map (δ φ)

def desc_cochain {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cochain G K n)
  (h : m+1=n) :
  cochain (mapping_cone φ) K n :=
twist.desc_cochain _ α β (by linarith)

@[simp]
lemma inl_desc_cochain {K : cochain_complex C ℤ} {n m : ℤ}
  (α : cochain F K m) (β : cochain G K n) (h : m+1=n) :
  (inl φ).comp (desc_cochain φ α β h)
    (show m = -1+n, by rw [← h, neg_add_cancel_comm_assoc]) = α :=
hom_complex.twist.inl_comp_desc_cochain _ _ _ _ _

@[simp, reassoc]
lemma inl_desc_cochain_v {K : cochain_complex C ℤ} {n m : ℤ}
  (α : cochain F K m) (β : cochain G K n) (h : m+1=n) (p q : ℤ) (hpq : q = p + (-1))
  (p' : ℤ) (hp' : p' = q + n) :
  (inl φ).v p q hpq ≫ (desc_cochain φ α β h).v q p' hp' =
  α.v p p' (by simp only [hp', hpq, ← h, int.add_neg_one, sub_add_add_cancel]) :=
by rw [← cochain.congr_v (inl_desc_cochain φ α β h) p p' (by linarith),
    cochain.comp_v _ _ _ p q p']

@[simp]
lemma inr_desc_cochain {K : cochain_complex C ℤ} {n m : ℤ}
  (α : cochain F K m) (β : cochain G K n) (h : m+1=n) :
  (cochain.of_hom (inr φ)).comp
    (desc_cochain φ α β h) (zero_add n).symm = β  :=
hom_complex.twist.inr_comp_desc_cochain _ _ _ _

@[simp, reassoc]
lemma inr_desc_cochain_v {K : cochain_complex C ℤ} {n m : ℤ}
  (α : cochain F K m) (β : cochain G K n) (h : m+1=n) (p q : ℤ) (hpq : q = p + n):
  (inr φ).f p ≫ (desc_cochain φ α β h).v p q hpq = β.v p q hpq  :=
by rw [← cochain.congr_v (inr_desc_cochain φ α β h) p q hpq,
  cochain.comp_v _ _ _ _ _ q (add_zero p).symm hpq, cochain.of_hom_v]

lemma δ_desc_cochain {K : cochain_complex C ℤ} {n m n' : ℤ} (α : cochain F K m) (β : cochain G K n)
  (h : m+1=n) (hn' : n+1 = n') : hom_complex.δ n n' (desc_cochain φ α β h) =
  (fst φ : cochain (mapping_cone φ) F 1).comp (hom_complex.δ m n α +
    ε (n+1) • (cochain.of_hom φ).comp β (zero_add n).symm) (by rw [← hn', add_comm]) +
    (snd φ).comp (hom_complex.δ n n' β) (zero_add n').symm :=
twist.δ_desc_cochain (cocycle.of_hom φ) α β (by linarith) (zero_add 1) h n' hn'

def desc_cocycle {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cocycle G K n)
  (h : m+1=n) (eq : hom_complex.δ m n α = ε n • (cochain.of_hom φ).comp β.1 (zero_add n).symm) :
  cocycle (mapping_cone φ) K n :=
twist.desc_cocycle _ α β (by linarith) _ eq

@[simp]
lemma desc_cocycle_coe {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cocycle G K n)
  (h : m+1=n) (eq : hom_complex.δ m n α = ε n • (cochain.of_hom φ).comp β.1 (zero_add n).symm) :
(desc_cocycle φ α β h eq : cochain (mapping_cone φ) K n) =
  desc_cochain φ α β h := rfl

def desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  mapping_cone φ ⟶ K :=
cocycle.hom_of (desc_cocycle φ α (cocycle.of_hom β) (neg_add_self 1)
  (by simp only [eq, ε_0, cochain.of_hom_comp, subtype.val_eq_coe, cocycle.of_hom_coe, one_zsmul]))

@[simp, reassoc]
lemma inr_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  inr φ ≫ desc φ α β eq = β :=
hom_complex.twist.inr_comp_desc _ _ _ (by linarith) (by simp [eq])

@[simp]
lemma inl_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  (inl φ).comp (cochain.of_hom (desc φ α β eq)) (add_zero _).symm = α :=
begin
  conv_rhs { rw ← hom_complex.twist.inl_comp_desc_cochain (cocycle.of_hom φ) α (cochain.of_hom β)
    (by linarith) (neg_add_self 1), },
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma inl_desc_v {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (p q : ℤ) (hpq : q = p + (-1)) :
  (inl φ).v p q hpq ≫ (desc φ α β eq).f q = α.v p q hpq :=
by simpa only [cochain.comp_zero_cochain, cochain.of_hom_v]
  using cochain.congr_v (inl_desc φ α β eq) p q hpq

@[simp, reassoc]
lemma inr_desc_f {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : hom_complex.δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (n : ℤ):
  (inr φ).f n ≫ (desc φ α β eq).f n = β.f n :=
homological_complex.congr_hom (inr_desc φ α β eq) n

def desc_homotopy {K : cochain_complex C ℤ} (f₁ f₂ : mapping_cone φ ⟶ K)
  (γ₁ : cochain F K (-2)) (γ₂ : cochain G K (-1))
  (h₁ : (inl φ).comp (cochain.of_hom f₁) (add_zero (-1)).symm =
    hom_complex.δ (-2) (-1) γ₁ + (cochain.of_hom φ).comp γ₂ (zero_add _).symm +
    (inl φ).comp (cochain.of_hom f₂) (add_zero (-1)).symm)
  (h₂ : cochain.of_hom (inr φ ≫ f₁) =
    hom_complex.δ (-1) 0 γ₂ + cochain.of_hom (inr φ ≫ f₂)) :
  homotopy f₁ f₂ :=
(equiv_homotopy _ _).symm
begin
  refine ⟨desc_cochain _ γ₁ γ₂ (by linarith), _⟩,
  rw [δ_desc_cochain φ γ₁ γ₂ (by linarith) (neg_add_self 1),
    cochain_ext _ _ (show (0 : ℤ) = -1 +1 , by linarith)],
  split,
  { rw [cochain.comp_add, h₁],
    nth_rewrite 0 cochain.comp_add,
    simp only [← cochain.comp_assoc_of_second_is_zero_cochain, inl_comp_snd,
      add_left_neg, ε_0, one_zsmul, cochain.zero_comp, add_zero,
      ← cochain.comp_assoc _ _ _ (neg_add_self 1).symm (add_neg_self 1).symm
        (show (-1 : ℤ) = (-1) +1 + (-1), by linarith),
      inl_comp_fst, cochain.id_comp], },
  { rw [cochain.comp_add, ← cochain.of_hom_comp, ← cochain.of_hom_comp, h₂],
    nth_rewrite 0 cochain.comp_add,
    simp only [← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      inr_comp_fst, cochain.zero_comp, zero_add, inr_comp_snd,
      cochain.id_comp], },
end

def lift_cochain {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) :
  cochain K (mapping_cone φ) n :=
twist.lift_cochain _ α β (by linarith)

lemma δ_lift_cochain {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) (m' : ℤ) (hm' : m = m'+(-1)) :
  hom_complex.δ n m (lift_cochain φ α β h) =
    -(hom_complex.δ m m' α).comp (inl φ) hm' +
    (hom_complex.δ n m β + α.comp (cochain.of_hom φ) (add_zero m).symm).comp
      (cochain.of_hom (inr φ)) (add_zero m).symm :=
begin
  erw [twist.δ_lift_cochain (cocycle.of_hom φ) α β (by linarith)
    (neg_add_self 1) (show m+1=m', by linarith) m h],
  simpa only [ε_neg, ε_1, neg_smul, one_smul],
end

def lift_cocycle {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cocycle K F m) (β : cochain K G n) (h : n+1=m)
  (hαβ : hom_complex.δ n m β + (α : cochain K F m).comp (cochain.of_hom φ) (add_zero m).symm = 0) :
  cocycle K (mapping_cone φ) n :=
twist.lift_cocycle _ α β (by linarith) (neg_add_self 1) _ h hαβ

def lift {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
   K ⟶ mapping_cone φ :=
cocycle.hom_of (lift_cocycle φ α β (zero_add 1) hαβ)

lemma lift_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) (n n' : ℤ)
    (hn' : n' = n+1) :
    (lift φ α β hαβ).f n = (α : cochain K F 1).v n n' hn' ≫
      (inl φ).v n' n (by rw [hn', int.add_neg_one, add_tsub_cancel_right]) +
    β.v n n (add_zero n).symm ≫ (inr φ).f n :=
by simpa only [lift, cocycle.hom_of_f, lift_cocycle,
  twist.lift_cocycle, cocycle.mk_coe,
  twist.lift_cochain_v (cocycle.of_hom φ) (α : cochain K F 1) β (add_comm 0 1)
  (neg_add_self 1) n n (by linarith) n' hn']

lemma lift_fst {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (lift φ α β hαβ)).comp
    (fst φ : cochain (mapping_cone φ) F 1) (zero_add 1).symm =
      (α : cochain K F 1) :=
begin
  rw ← hom_complex.twist.lift_cochain_comp_fst (cocycle.of_hom φ)
    (α : cochain K F 1) β (by linarith) (zero_add 1),
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma lift_fst_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (n n' : ℤ) (hnn' : n' = n+1) :
    (lift φ α β hαβ).f n ≫
      (fst φ : cochain (mapping_cone φ) F 1).v n n' hnn' =
      (α : cochain K F 1).v n n' hnn' :=
by simp only [← cochain.congr_v (lift_fst φ α β hαβ) n n' hnn',
  cochain.zero_cochain_comp, cochain.of_hom_v]

lemma lift_snd {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (lift φ α β hαβ)).comp
    (snd φ) (add_zero 0).symm = β :=
begin
  conv_rhs { rw ← hom_complex.twist.lift_cochain_comp_snd (cocycle.of_hom φ)
    (α : cochain K F 1) β (by linarith), },
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma lift_snd_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) (n : ℤ) :
  (lift φ α β hαβ).f n ≫ (snd φ).v n n (add_zero n).symm =
    β.v n n (add_zero n).symm :=
by simp only [← cochain.congr_v (lift_snd φ α β hαβ) n n (by linarith),
  cochain.comp_zero_cochain, cochain.of_hom_v]

lemma lift_desc_f {K L : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : hom_complex.δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (α' : cochain F L (-1)) (β' : G ⟶ L) (eq : hom_complex.δ (-1) 0 α' = cochain.of_hom (φ ≫ β'))
  (n n' : ℤ) (hnn' : n' = n+1) :
  (lift φ α β hαβ).f n ≫ (desc φ α' β' eq).f n =
    (α : cochain K F 1).v n n' hnn' ≫ α'.v n' n (by { rw [hnn', int.add_neg_one, add_tsub_cancel_right], }) +
      β.v n n (add_zero n).symm ≫ β'.f n :=
begin
  dsimp only [lift, lift_cocycle,
    desc, desc_cocycle, twist.lift_cocycle,
    twist.desc_cocycle],
  simp only [cocycle.hom_of_f, cocycle.mk_coe, cocycle.of_hom_coe,
    twist.lift_cochain_eq _ _ _ _ (neg_add_self 1), cochain.add_v,
    ← cochain.comp_v _ _ (zero_add 0).symm n n n (by linarith) (by linarith),
    hom_complex.cochain.comp_assoc_of_second_is_zero_cochain,
    hom_complex.cochain.comp_assoc_of_third_is_zero_cochain,
    preadditive.add_comp,
    hom_complex.twist.inl_comp_desc_cochain,
    hom_complex.twist.inr_comp_desc_cochain],
  simp only [cochain.comp_v _ _ (add_neg_self 1).symm n n' n (hnn') (by linarith),
    hom_complex.cochain.comp_zero_cochain, cochain.of_hom_v],
end

def lift_homotopy {K : cochain_complex C ℤ} (f₁ f₂ : K ⟶ mapping_cone φ)
  (γ₁ : cochain K F 0) (γ₂ : cochain K G (-1))
  (h₁ : (cochain.of_hom f₁).comp (fst φ :
    cochain (mapping_cone φ) F 1) (zero_add 1).symm = -hom_complex.δ 0 1 γ₁ +
      (cochain.of_hom f₂).comp (fst φ : cochain (mapping_cone φ) F 1) (zero_add 1).symm)
  (h₂ : (cochain.of_hom f₁).comp (snd φ) (add_zero 0).symm =
    hom_complex.δ (-1) 0 γ₂ + γ₁.comp (cochain.of_hom φ) (zero_add 0).symm +
    (cochain.of_hom f₂).comp (snd φ) (add_zero 0).symm) :
  homotopy f₁ f₂ :=
(equiv_homotopy _ _).symm
begin
  refine ⟨lift_cochain φ γ₁ γ₂ (neg_add_self 1), _⟩,
  simp only [δ_lift_cochain φ _ _ _ 1 (show (0 : ℤ) = 1 +(-1), by linarith),
    cochain_ext' _ _ (zero_add 1).symm],
  split,
  { simp only [add_zero, cochain.add_comp, cochain.neg_comp,
      cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst,
      cochain.comp_zero,
      cochain.comp_assoc _ _ _ (add_neg_self 1).symm (neg_add_self 1).symm
      (show (1 : ℤ) = 1+(-1)+1, by linarith),
      inl_comp_fst, cochain.comp_id, h₁], },
  { simp only [zero_add, neg_zero, cochain.add_comp, cochain.comp_assoc_of_third_is_zero_cochain,
      cochain.neg_comp, inl_comp_snd, cochain.comp_zero, inr_comp_snd, cochain.comp_id, h₂], },
end

section

variables {K₁ K₂ L₁ L₂ : cochain_complex C ℤ}
  [∀ p, has_binary_biproduct (K₁.X (p+1-(0 : ℤ))) (L₁.X p)]
  [∀ p, has_binary_biproduct (K₂.X (p+1-(0 : ℤ))) (L₂.X p)]
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (τ₁ : K₁ ⟶ K₂) (τ₂ : L₁ ⟶ L₂) (comm : f₁ ≫ τ₂ = τ₁ ≫ f₂)

include comm

def map : mapping_cone f₁ ⟶ mapping_cone f₂ :=
desc f₁ ((cochain.of_hom τ₁).comp (inl f₂) (zero_add _).symm)
  (τ₂ ≫ inr f₂)
begin
  rw [δ_comp_of_first_is_zero_cochain _ _ _ (neg_add_self 1), δ_inl,
    cocycle.δ_cochain_of_hom, cochain.zero_comp, smul_zero, add_zero, cochain.of_hom_comp f₂,
    ← assoc f₁, ← cochain.of_hom_comp, ← cochain.of_hom_comp, ← assoc, comm],
end

lemma inr_comp_map :
  inr f₁ ≫ map _ _ _ _ comm =
    τ₂ ≫ inr f₂ :=
begin
  apply hom_complex.cochain.of_hom_injective,
  rw cochain_ext' _ _ (zero_add 1).symm,
  dsimp only [map],
  split,
  { simp only [inr_desc, cochain.of_hom_comp,
      cochain.comp_assoc_of_second_is_zero_cochain, inr_comp_fst,
      inr_fst], },
  { simp only [inr_desc, cochain.of_hom_comp, inr_snd,
      cochain.comp_assoc_of_third_is_zero_cochain, inr_comp_snd], },
end

lemma map_comp_δ :
  map _ _ _ _ comm ≫ δ f₂ =
  δ f₁ ≫ τ₁⟦1⟧' :=
begin
  apply hom_complex.cochain.of_hom_injective,
  rw cochain_ext _ _(neg_add_self 1).symm,
  dsimp only [map],
  split,
  { simp only [cochain.of_hom_comp, ← hom_complex.cochain.comp_assoc_of_second_is_zero_cochain,
      inl_desc, hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      inl_δ, cochain.comp_neg, cochain.of_hom_comp],
    ext p q hpq,
    have hp : p = q+1 := by linarith,
    subst hp,
    simp only [cochain.neg_v, cochain.zero_cochain_comp, cochain.of_hom_v,
      cochain.neg_comp, cochain.comp_zero_cochain, shift_functor_map_f', neg_inj],
    erw cochain.right_shift_v (cochain.of_hom _) 1 (-1)
      (by linarith) (q+1) q (by linarith) (q+1) (by linarith),
    erw cochain.right_shift_v (cochain.of_hom _) 1 (-1)
      (by linarith) (q+1) q (by linarith) (q+1) (by linarith),
    simp only [shift_functor_obj_X_iso, cochain.of_hom_v, homological_complex.id_f,
      homological_complex.X_iso_of_eq_refl, id_comp],
    dsimp [iso.refl],
    rw [comp_id, id_comp], },
  { rw [cochain.of_hom_comp, ← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      ← cochain.of_hom_comp, inr_desc, ← cochain.of_hom_comp, assoc,
      inr_δ, comp_zero, cochain.of_hom_zero, ← cochain.of_hom_comp, ← assoc,
      inr_δ, zero_comp, cochain.of_hom_zero], },
end

end

end mapping_cone

end preadditive

section abelian

open hom_complex

variables [abelian C] {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

include ex

lemma degreewise_exact (n : ℤ) :
  (S.map (homological_complex.eval C (complex_shape.up ℤ) n)).short_exact :=
ex.map_of_exact (homological_complex.eval C (complex_shape.up ℤ) n)

def from_mapping_cone_of_ses : mapping_cone S.f ⟶ S.X₃ :=
mapping_cone.desc S.f 0 S.g (by simp)

@[simp, reassoc]
lemma inr_from_mapping_cone_of_ses (n : ℤ) :
  (mapping_cone.inr S.f).f n ≫ (from_mapping_cone_of_ses ex).f n = S.g.f n :=
begin
  dsimp only [from_mapping_cone_of_ses],
  simp only [mapping_cone.inr_desc_f],
end

@[simp, reassoc]
lemma inl_from_mapping_cone_of_ses (p q : ℤ) (hpq : q = p + (-1)) :
  (mapping_cone.inl S.f).v p q hpq ≫ (from_mapping_cone_of_ses ex).f q = 0 :=
begin
  dsimp only [from_mapping_cone_of_ses],
  simp only [mapping_cone.inl_desc_v, cochain.zero_v],
end

@[simp, reassoc]
lemma inr_mapping_cone_comp_from_mapping_cone_of_ses :
  mapping_cone.inr S.f ≫ from_mapping_cone_of_ses ex = S.g :=
begin
  ext n : 2,
  simp only [homological_complex.comp_f, inr_from_mapping_cone_of_ses],
end

instance from_mapping_cone_of_ses_quasi_iso : quasi_iso (from_mapping_cone_of_ses ex) :=
⟨λ n, begin
  rw is_iso_homology_map_iff_short_complex_quasi_iso'
    (from_mapping_cone_of_ses ex) (show (n-1)+1=n, by linarith) rfl,
  change is_iso _,
  haveI : ∀ (n : ℤ), mono (S.f.f n) :=
    λ n, (ex.map_of_exact (homological_complex.eval _ _ n)).mono_f,
  rw is_iso_iff_mono_and_epi,
  split,
  { rw short_complex.mono_homology_map_iff,
    dsimp,
    intros A x₂ hxy z hz,
    obtain ⟨x, y, rfl⟩ := mapping_cone.to_decomposition x₂ _ rfl,
    simp only [preadditive.add_comp, assoc, mapping_cone.inr_d, preadditive.comp_sub,
      mapping_cone.inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith)] at hxy,
    obtain ⟨hx, hy⟩ := (mapping_cone.to_ext_iff _ _ _ rfl).mp hxy,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone.inr_fst,
      comp_zero, mapping_cone.inl_fst, comp_id, zero_sub, add_zero, zero_comp, neg_eq_zero] at hx,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone.inr_snd, comp_id,
      mapping_cone.inl_snd, comp_zero, sub_zero, zero_comp, ← eq_neg_iff_add_eq_zero] at hy,
    clear hxy,
    simp only [preadditive.add_comp, assoc, inr_from_mapping_cone_of_ses,
      inl_from_mapping_cone_of_ses, comp_zero, zero_add] at hz,
    haveI : epi (S.g.f (n-1)) := (ex.map_of_exact (homological_complex.eval _ _ _)).epi_g,
    obtain ⟨A', π, hπ, z', hz'⟩ := abelian.pseudo_surjective_of_epi' (S.g.f (n-1)) z,
    have ex' := (ex.map_of_exact (homological_complex.eval _ _ n)),
    haveI := ex'.mono_f,
    let w : A' ⟶ S.X₁.X n := ex'.exact.lift (π ≫ y - z' ≫ S.X₂.d _ _) begin
      dsimp,
      simp only [preadditive.sub_comp, assoc, hz, reassoc_of hz',
        homological_complex.hom.comm, sub_self],
    end,
    have hw : w ≫ S.f.f n = _ := ex'.exact.lift_f _ _,
    refine ⟨A', π, hπ, w ≫ (mapping_cone.inl S.f).v n (n-1) (show n-1 = n+(-1), by refl) + z' ≫ (mapping_cone.inr S.f).f (n-1),
      (mapping_cone.to_ext_iff _ _ _ rfl).mpr ⟨_, _⟩⟩,
    { simp only [assoc, preadditive.add_comp, mapping_cone.inr_fst, comp_zero, add_zero,
        mapping_cone.inl_fst, comp_id, mapping_cone.inr_d_assoc,
        mapping_cone.inl_d_assoc S.f (n-1) n (n+1) (by refl) (by linarith),
        preadditive.sub_comp, preadditive.comp_sub, ← cancel_mono (S.f.f (n+1)), zero_comp],
      simp only [← S.f.comm, reassoc_of hw, preadditive.sub_comp, assoc, homological_complex.d_comp_d,
        comp_zero, sub_zero, zero_sub, hy, preadditive.comp_neg], },
    { simp only [assoc, preadditive.comp_add, preadditive.add_comp, mapping_cone.inl_snd, comp_zero,
        zero_add, mapping_cone.inr_snd, comp_id, mapping_cone.inr_d_assoc, preadditive.comp_sub,
        preadditive.sub_comp, hw,
        mapping_cone.inl_d S.f (n-1) n (n+1) (show n-1 = n+(-1), by refl) (by linarith)],
        abel, }, },
  { rw short_complex.epi_homology_map_iff,
    dsimp,
    intros A z hz,
    haveI : epi (S.g.f n) := (ex.map_of_exact (homological_complex.eval _ _ _)).epi_g,
    obtain ⟨A', π, hπ, y, hy⟩ := abelian.pseudo_surjective_of_epi' (S.g.f n) z,
    have ex' := (ex.map_of_exact (homological_complex.eval _ _ (n+1))),
    haveI := ex'.mono_f,
    let x : A' ⟶ S.X₁.X (n+1) := ex'.exact.lift (y ≫ S.X₂.d _ _) begin
      dsimp,
      simp only [assoc, ← S.g.comm, ← reassoc_of hy, hz, comp_zero],
    end,
    have hx : x ≫ S.f.f (n+1) = _ := ex'.exact.lift_f _ _,
    have hdx : x ≫ S.X₁.d (n+1) (n+1+1) = 0,
    { simp only [← cancel_mono (S.f.f (n+1+1)), assoc, zero_comp, ← S.f.comm, reassoc_of hx,
        homological_complex.d_comp_d, comp_zero], },
    refine ⟨A', π, hπ, y ≫ (mapping_cone.inr S.f).f n -
      x ≫ (mapping_cone.inl S.f).v (n+1) n (show n = (n+1)+(-1), by linarith), _, _⟩,
    { simp only [preadditive.sub_comp, assoc, mapping_cone.inr_d, ← reassoc_of hx,
        mapping_cone.inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith), preadditive.comp_sub,
        reassoc_of hdx, zero_comp, sub_zero, sub_self], },
    { exact ⟨0, by simp only [hy, preadditive.sub_comp, assoc, inr_from_mapping_cone_of_ses,
        inl_from_mapping_cone_of_ses, comp_zero, sub_zero, zero_comp, add_zero]⟩, }, },
end⟩

end abelian

end cochain_complex
