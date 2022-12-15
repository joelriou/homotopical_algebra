import for_mathlib.algebra.homology.twist_cocycle
import algebra.homology.quasi_iso
import algebra.homology.short_complex.pseudoelements
import for_mathlib.algebra.homology.hom_complex_shift
import category_theory.triangulated.triangulated

noncomputable theory
open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated

namespace cochain_complex

variables {C : Type*} [category C]

section preadditive

variables [preadditive C]
  {F G : cochain_complex C ℤ} [∀ p, has_binary_biproduct (F.X (p+1-(0 : ℤ))) (G.X p)]
  (φ : F ⟶ G)

open hom_complex

def mapping_cone : cochain_complex C ℤ :=
twist (cocycle.of_hom φ)

def mapping_cone_inl : cochain F (mapping_cone φ) (-1) :=
twist.inl (cocycle.of_hom φ) (neg_add_self 1)

def mapping_cone_inr : G ⟶ mapping_cone φ :=
twist.inr (cocycle.of_hom φ)

def mapping_cone_fst : cocycle (mapping_cone φ) F 1 :=
  twist.fst (cocycle.of_hom φ) (zero_add 1)

def mapping_cone_snd : cochain (mapping_cone φ) G 0 :=
  twist.snd (cocycle.of_hom φ)

@[simp, reassoc]
lemma mapping_cone_inl_fst (p q : ℤ) (hpq : p = q+1) :
  (mapping_cone_inl φ).v p q (by rw [hpq, int.add_neg_one, add_tsub_cancel_right]) ≫
     (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v q p hpq = 𝟙 _ :=
by simpa only [cochain.comp_v _ _ (neg_add_self 1).symm p q p (by linarith) hpq,
  cochain.of_hom_v, homological_complex.id_f]
  using cochain.congr_v (twist.inl_comp_fst _ (neg_add_self 1) (zero_add 1)) p p  (by linarith)

@[simp, reassoc]
lemma mapping_cone_inl_snd (p q : ℤ) (hpq : q = p+(-1)) :
  (mapping_cone_inl φ).v p q hpq ≫ (mapping_cone_snd φ).v q q (add_zero q).symm = 0 :=
by simpa only [cochain.comp_zero_cochain] using
  cochain.congr_v (twist.inl_comp_snd (cocycle.of_hom φ) (neg_add_self 1)) p q hpq

@[simp]
lemma mapping_cone_inl_comp_fst :
  (mapping_cone_inl φ).comp (mapping_cone_fst φ : cochain (mapping_cone φ) F 1)
    (neg_add_self 1).symm = cochain.of_hom (𝟙 _) :=
begin
  ext p,
  simp only [cochain.comp_v _ _ (neg_add_self 1).symm p (p-1) p (by linarith) (by linarith),
    mapping_cone_inl_fst, cochain.of_hom_v, homological_complex.id_f],
end

@[simp]
lemma mapping_cone_inl_comp_snd :
  (mapping_cone_inl φ).comp (mapping_cone_snd φ) (add_zero _).symm = 0 :=
by tidy

@[simp, reassoc]
lemma mapping_cone_inr_snd (p : ℤ) :
  (mapping_cone_inr φ).f p ≫ (mapping_cone_snd φ).v p p (add_zero p).symm = 𝟙 _ :=
by simpa only [cochain.comp_v _ _ (add_zero 0).symm p p p (by linarith) (by linarith),
  cochain.of_hom_v, homological_complex.id_f]
  using cochain.congr_v (twist.inr_comp_snd (cocycle.of_hom φ)) p p (add_zero p).symm

@[simp, reassoc]
lemma mapping_cone_inr_fst (p q : ℤ) (hpq : q = p+1) :
  (mapping_cone_inr φ).f p ≫ (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v p q hpq = 0 :=
by simpa only [cochain.zero_cochain_comp, cochain.of_hom_v, cochain.zero_v]
  using cochain.congr_v (twist.inr_comp_fst (cocycle.of_hom φ) (zero_add 1)) p q hpq

@[simp]
lemma mapping_cone_inr_comp_fst :
  (cochain.of_hom (mapping_cone_inr φ)).comp
    (mapping_cone_fst φ : cochain (mapping_cone φ) F 1) (zero_add 1).symm = 0 :=
by tidy

@[simp]
lemma mapping_cone_inr_comp_snd :
  (cochain.of_hom (mapping_cone_inr φ)).comp
    (mapping_cone_snd φ : cochain (mapping_cone φ) G 0) (zero_add 0).symm = cochain.of_hom (𝟙 _) :=
by tidy

def ι_mapping_cone : G ⟶ mapping_cone φ :=
mapping_cone_inr φ

@[simps]
def mapping_cone_δ_as_cocycle : cocycle (mapping_cone φ) F 1 :=
-mapping_cone_fst φ

def mapping_cone_δ : mapping_cone φ ⟶ F⟦(1 : ℤ)⟧ :=
cocycle.hom_of
  (cocycle.right_shift (mapping_cone_δ_as_cocycle φ) 1 0 (zero_add 1).symm)

@[simp, priority 1100]
lemma mapping_cone_ι_δ : ι_mapping_cone φ ≫ mapping_cone_δ φ = 0 :=
begin
  ext n,
  dsimp only [ι_mapping_cone, mapping_cone_δ],
  simp only [homological_complex.comp_f, cocycle.hom_of_f,
    cocycle.right_shift_coe, mapping_cone_δ_as_cocycle_coe,
    homological_complex.zero_f_apply, mapping_cone_inr_fst_assoc,
    hom_complex.cochain.right_shift_v _ 1 0 (zero_add 1).symm n n (by linarith) _ rfl,
    preadditive.neg_comp, preadditive.comp_neg, cochain.neg_v, zero_comp, neg_zero],
end

lemma ext_to {A : C} {n : ℤ} (f₁ f₂ : A ⟶ (mapping_cone φ).X n) (n' : ℤ) (hn' : n' = n+1)
  (h₁ : f₁ ≫ (mapping_cone_fst φ).1.v n n' hn' = f₂ ≫ (mapping_cone_fst φ).1.v n n' hn')
  (h₂ : f₁ ≫ (mapping_cone_snd φ).v n n (add_zero n).symm =
    f₂ ≫ (mapping_cone_snd φ).v n n (add_zero n).symm) : f₁ = f₂ :=
begin
  have h' : n' = n+1-0 := by linarith,
  subst h',
  ext,
  { dsimp [mapping_cone_fst, twist.fst] at h₁,
    simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id] using h₁, },
  { dsimp [mapping_cone_snd, twist.snd] at h₂,
    simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id] using h₂, },
end

@[simp]
lemma mapping_cone_δ_inl :
  δ (-1) 0 (mapping_cone_inl φ) = cochain.of_hom (φ ≫ mapping_cone_inr φ) :=
begin
  dsimp only [mapping_cone_inl],
  simpa only [twist.δ_inl (cocycle.of_hom φ) (neg_add_self 1), cochain.of_hom_comp],
end

@[simp]
lemma mapping_cone_δ_snd :
  δ 0 1 (mapping_cone_snd φ) = -(mapping_cone_fst φ).1.comp (cochain.of_hom φ) (add_zero 1).symm :=
twist.δ_snd (cocycle.of_hom φ) (zero_add 1)

lemma mapping_cone_of_d_eq : cochain.of_d (mapping_cone φ) =
  -((mapping_cone_fst φ : cochain (mapping_cone φ) F 1).comp (cochain.of_d F)
    (show (2 : ℤ) = 1+1, by refl)).comp (mapping_cone_inl φ) (show (1 : ℤ) = 2 + (-1), by refl) +
  ((mapping_cone_fst φ : cochain (mapping_cone φ) F 1).comp (cochain.of_hom φ) (add_zero 1).symm).comp
      (cochain.of_hom (mapping_cone_inr φ)) (add_zero 1).symm +
  ((mapping_cone_snd φ).comp (cochain.of_d G) (zero_add 1).symm).comp
    (cochain.of_hom (mapping_cone_inr φ)) (add_zero 1).symm :=
begin
  dsimp only [mapping_cone],
  simpa only [twist.of_d_eq (cocycle.of_hom φ) 1 2 (-1) rfl rfl rfl, zero_add, ε_1,
    neg_smul, one_smul],
end

@[reassoc]
lemma mapping_cone_inl_d (n₁ n₂ n₃ : ℤ) (h₁₂ : n₁ = n₂ + (-1)) (h₂₃ : n₂ = n₃ + (-1)) :
  (mapping_cone_inl φ).v n₂ n₁ h₁₂ ≫ (mapping_cone φ).d n₁ n₂ =
    φ.f n₂ ≫ (mapping_cone_inr φ).f n₂ - F.d n₂ n₃ ≫ (mapping_cone_inl φ).v _ _ h₂₃ :=
begin
  simp only [← hom_complex.cochain.of_d_v (mapping_cone φ) n₁ n₂ (by linarith), mapping_cone_of_d_eq,
    add_zero, cochain.comp_assoc_of_third_is_zero_cochain, cochain.add_v, cochain.neg_v,
    cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_cochain_comp,
    preadditive.comp_add, preadditive.comp_neg, mapping_cone_inl_fst_assoc,
    mapping_cone_inl_snd_assoc, zero_comp],
  erw cochain.comp_v _ _ (show (1 : ℤ) = 2 + (-1), by linarith) n₁ n₃ n₂ (by linarith) (by linarith),
  erw cochain.comp_v _ _ (show (2 : ℤ) = 1 + 1, by linarith) n₁ n₂ n₃ (by linarith) (by linarith),
  simp only [cochain.of_d_v, assoc, mapping_cone_inl_fst_assoc, neg_add_eq_sub],
end

@[simp, reassoc]
lemma mapping_cone_inr_d (n n' : ℤ) :
  (mapping_cone_inr φ).f n ≫ (mapping_cone φ).d n n' =
    G.d n n' ≫ (mapping_cone_inr φ).f n' :=
begin
  by_cases h : n+1 = n',
  { rw [← hom_complex.cochain.of_d_v (mapping_cone φ) _ _ h.symm, mapping_cone_of_d_eq φ],
    simp only [cochain.comp_assoc_of_third_is_zero_cochain, cochain.add_v, cochain.neg_v,
      cochain.comp_zero_cochain, cochain.of_hom_v, cochain.zero_cochain_comp, cochain.of_d_v,
      preadditive.comp_add, preadditive.comp_neg, mapping_cone_inr_fst_assoc, zero_comp,
      mapping_cone_inr_snd_assoc, add_left_eq_self, neg_eq_zero],
    erw cochain.comp_v _ _ (show (1 : ℤ)= 2 + (-1), by linarith) n (n+2) n' rfl (by linarith),
    erw cochain.comp_v _ _ (show (2 : ℤ) = 1 + 1, by linarith) n (n+1) (n+2) rfl (by linarith),
    simp only [assoc, mapping_cone_inr_fst_assoc, zero_comp], },
  { simp only [G.shape _ _ h, (mapping_cone φ).shape _ _ h, comp_zero, zero_comp], },
end

lemma mapping_cone_id (p q : ℤ) (hpq : q = p+1) :
  (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v p q hpq ≫
    (mapping_cone_inl φ).v q p (by rw [hpq, int.add_neg_one, add_tsub_cancel_right]) +
  (mapping_cone_snd φ).v p p (add_zero p).symm ≫ (mapping_cone_inr φ).f p = 𝟙 _ :=
begin
  have hq' : q = p+1-0 := by linarith,
  subst hq',
  dsimp [mapping_cone_fst, mapping_cone_snd, twist.fst, twist.snd, mapping_cone_inl,
    mapping_cone_inr, twist.inl, twist.inr],
  simpa only [cochain.of_hom_v, homological_complex.id_f, comp_id, id_comp, biprod.total],
end

variable {φ}

lemma to_mapping_cone_decomposition {A : C} {n : ℤ} (f : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  ∃ (x : A ⟶ F.X n') (y : A ⟶ G.X n), f = x ≫
    (mapping_cone_inl φ : cochain F (mapping_cone φ) (-1)).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right])
      + y ≫ (mapping_cone_inr φ).f n :=
begin
  refine ⟨f ≫ (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v _ _ (by linarith), f ≫ (mapping_cone_snd φ).v n n (by linarith), _⟩,
  have h := f ≫= mapping_cone_id φ n n' h,
  rw comp_id at h,
  nth_rewrite 0 ← h,
  simp,
end

lemma to_mapping_cone_ext_iff {A : C} {n : ℤ} (f g : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  f = g ↔ f ≫ (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v _ _ h =
    g ≫ (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v _ _ h ∧
    f ≫ (mapping_cone_snd φ).v n n (add_zero n).symm =
      g ≫ (mapping_cone_snd φ).v n n (add_zero n).symm :=
begin
  split,
  { intro h,
    rw h,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    rw [← cancel_mono (𝟙 ((mapping_cone φ).X n))],
    simp only [← mapping_cone_id _ _ _ h, preadditive.comp_add, reassoc_of h₁, reassoc_of h₂], },
end

lemma from_mapping_cone_ext_iff {A : C} {n : ℤ} (f g : (mapping_cone φ).X n ⟶ A)
  (n' : ℤ) (h : n' = n+1) :
  f = g ↔ (mapping_cone_inl φ).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right]) ≫ f =
    (mapping_cone_inl φ).v n' n (by rw [h, int.add_neg_one, add_tsub_cancel_right]) ≫ g ∧
    (mapping_cone_inr φ).f n ≫ f = (mapping_cone_inr φ).f n ≫ g :=
begin
  split,
  { intro h,
    rw h,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    rw [← cancel_epi (𝟙 ((mapping_cone φ).X n))],
    simp only [← mapping_cone_id _ _ _ h, preadditive.add_comp, assoc, h₁, h₂], },
end

lemma mapping_cone_cochain_ext {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain (mapping_cone φ) K m) (hm' : m = m'+1) :
  y₁ = y₂ ↔ (mapping_cone_inl φ).comp y₁ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) =
    (mapping_cone_inl φ).comp y₂ (show m' = -1+m, by rw [hm', neg_add_cancel_comm_assoc]) ∧
    (cochain.of_hom (mapping_cone_inr φ)).comp y₁ (zero_add m).symm =
      (cochain.of_hom (mapping_cone_inr φ)).comp y₂ (zero_add m).symm :=
hom_complex.twist.cochain_ext _ _ _ _ _

lemma mapping_cone_cochain_ext' {K : cochain_complex C ℤ} {m m' : ℤ}
  (y₁ y₂ : cochain K (mapping_cone φ) m) (hm' : m' = m+1) :
  y₁ = y₂ ↔ y₁.comp (mapping_cone_fst φ : cochain (mapping_cone φ) F 1) hm' =
    y₂.comp (mapping_cone_fst φ : cochain (mapping_cone φ) F 1) hm' ∧
    y₁.comp (mapping_cone_snd φ) (add_zero m).symm =
      y₂.comp (mapping_cone_snd φ) (add_zero m).symm :=
hom_complex.twist.cochain_ext' _ _ _ _ _

variable (φ)

@[simp]
def ι_mapping_cone' := (homotopy_category.quotient _ _).map (ι_mapping_cone φ)

def mapping_cone_δ' : (homotopy_category.quotient _ _).obj (mapping_cone φ) ⟶
  ((homotopy_category.quotient _ _).obj F)⟦(1 : ℤ)⟧ :=
(homotopy_category.quotient _ _).map (mapping_cone_δ φ)

def mapping_cone.desc_cochain {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cochain G K n)
  (h : m+1=n) :
  cochain (mapping_cone φ) K n :=
twist.desc_cochain _ α β (by linarith)

lemma mapping_cone.δ_desc_cochain {K : cochain_complex C ℤ} {n m n' : ℤ} (α : cochain F K m) (β : cochain G K n)
  (h : m+1=n) (hn' : n+1 = n') : δ n n' (mapping_cone.desc_cochain φ α β h) =
  (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).comp (δ m n α +
    ε (n+1) • (cochain.of_hom φ).comp β (zero_add n).symm) (by rw [← hn', add_comm]) +
    (mapping_cone_snd φ).comp (δ n n' β) (zero_add n').symm :=
twist.δ_desc_cochain (cocycle.of_hom φ) α β (by linarith) (zero_add 1) h n' hn'

def mapping_cone.desc_cocycle {K : cochain_complex C ℤ} {n m : ℤ} (α : cochain F K m) (β : cocycle G K n)
  (h : m+1=n) (eq : δ m n α = ε n • (cochain.of_hom φ).comp β.1 (zero_add n).symm) :
  cocycle (mapping_cone φ) K n :=
twist.desc_cocycle _ α β (by linarith) _ eq

def mapping_cone.desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  mapping_cone φ ⟶ K :=
cocycle.hom_of (mapping_cone.desc_cocycle φ α (cocycle.of_hom β) (neg_add_self 1)
  (by simp only [eq, ε_0, cochain.of_hom_comp, subtype.val_eq_coe, cocycle.of_hom_coe, one_zsmul]))

@[simp, reassoc]
lemma mapping_cone.ι_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  ι_mapping_cone φ ≫ mapping_cone.desc φ α β eq = β :=
hom_complex.twist.inr_comp_desc _ _ _ (by linarith) (by simp [eq])

@[simp]
lemma mapping_cone.inl_desc {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = cochain.of_hom (φ ≫ β)) :
  (mapping_cone_inl φ).comp (cochain.of_hom (mapping_cone.desc φ α β eq)) (add_zero _).symm = α :=
begin
  conv_rhs { rw ← hom_complex.twist.inl_comp_desc_cochain (cocycle.of_hom φ) α (cochain.of_hom β)
    (by linarith) (neg_add_self 1), },
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma mapping_cone.inl_desc_v {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (p q : ℤ) (hpq : q = p + (-1)) :
  (mapping_cone_inl φ).v p q hpq ≫ (mapping_cone.desc φ α β eq).f q = α.v p q hpq :=
by simpa only [cochain.comp_zero_cochain, cochain.of_hom_v]
  using cochain.congr_v (mapping_cone.inl_desc φ α β eq) p q hpq

@[simp, reassoc]
lemma mapping_cone.inr_desc_f {K : cochain_complex C ℤ} (α : cochain F K (-1)) (β : G ⟶ K)
  (eq : δ (-1) 0 α = cochain.of_hom (φ ≫ β)) (n : ℤ):
  (mapping_cone_inr φ).f n ≫ (mapping_cone.desc φ α β eq).f n = β.f n :=
homological_complex.congr_hom (mapping_cone.ι_desc φ α β eq) n

def mapping_cone.desc_homotopy {K : cochain_complex C ℤ} (f₁ f₂ : mapping_cone φ ⟶ K)
  (γ₁ : cochain F K (-2)) (γ₂ : cochain G K (-1))
  (h₁ : (mapping_cone_inl φ).comp (cochain.of_hom f₁) (add_zero (-1)).symm =
    δ (-2) (-1) γ₁ + (cochain.of_hom φ).comp γ₂ (zero_add _).symm +
    (mapping_cone_inl φ).comp (cochain.of_hom f₂) (add_zero (-1)).symm)
  (h₂ : cochain.of_hom (mapping_cone_inr φ ≫ f₁) =
    δ (-1) 0 γ₂ + cochain.of_hom (mapping_cone_inr φ ≫ f₂)) :
  homotopy f₁ f₂ :=
(equiv_homotopy _ _).symm
begin
  refine ⟨mapping_cone.desc_cochain _ γ₁ γ₂ (by linarith), _⟩,
  rw [mapping_cone.δ_desc_cochain φ γ₁ γ₂ (by linarith) (neg_add_self 1),
    mapping_cone_cochain_ext _ _ (show (0 : ℤ) = -1 +1 , by linarith)],
  split,
  { rw [cochain.comp_add, h₁],
    nth_rewrite 0 cochain.comp_add,
    simp only [← cochain.comp_assoc_of_second_is_zero_cochain, mapping_cone_inl_comp_snd,
      add_left_neg, ε_0, one_zsmul, cochain.zero_comp, add_zero,
      ← cochain.comp_assoc _ _ _ (neg_add_self 1).symm (add_neg_self 1).symm
        (show (-1 : ℤ) = (-1) +1 + (-1), by linarith),
      mapping_cone_inl_comp_fst, cochain.id_comp], },
  { rw [cochain.comp_add, ← cochain.of_hom_comp, ← cochain.of_hom_comp, h₂],
    nth_rewrite 0 cochain.comp_add,
    simp only [← hom_complex.cochain.comp_assoc_of_first_is_zero_cochain,
      mapping_cone_inr_comp_fst, cochain.zero_comp, zero_add, mapping_cone_inr_comp_snd,
      cochain.id_comp], },
end

def mapping_cone.lift_cochain {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cochain K F m) (β : cochain K G n) (h : n+1=m) :
  cochain K (mapping_cone φ) n :=
twist.lift_cochain _ α β (by linarith)

def mapping_cone.lift_cocycle {K : cochain_complex C ℤ}
  {n m : ℤ} (α : cocycle K F m) (β : cochain K G n) (h : n+1=m)
  (hαβ : δ n m β + (α : cochain K F m).comp (cochain.of_hom φ) (add_zero m).symm = 0) :
  cocycle K (mapping_cone φ) n :=
twist.lift_cocycle _ α β (by linarith) (neg_add_self 1) _ h hαβ

def mapping_cone.lift {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
   K ⟶ mapping_cone φ :=
cocycle.hom_of (mapping_cone.lift_cocycle φ α β (zero_add 1) hαβ)

lemma mapping_cone.lift_fst {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (mapping_cone.lift φ α β hαβ)).comp
    (mapping_cone_fst φ : cochain (mapping_cone φ) F 1) (zero_add 1).symm =
      (α : cochain K F 1) :=
begin
  rw ← hom_complex.twist.lift_cochain_comp_fst (cocycle.of_hom φ)
    (α : cochain K F 1) β (by linarith) (zero_add 1),
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma mapping_cone.lift_fst_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (n n' : ℤ) (hnn' : n' = n+1) :
    (mapping_cone.lift φ α β hαβ).f n ≫
      (mapping_cone_fst φ : cochain (mapping_cone φ) F 1).v n n' hnn' =
      (α : cochain K F 1).v n n' hnn' :=
by simp only [← cochain.congr_v (mapping_cone.lift_fst φ α β hαβ) n n' hnn',
  cochain.zero_cochain_comp, cochain.of_hom_v]

lemma mapping_cone.lift_snd {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) :
  (cochain.of_hom (mapping_cone.lift φ α β hαβ)).comp
    (mapping_cone_snd φ) (add_zero 0).symm = β :=
begin
  conv_rhs { rw ← hom_complex.twist.lift_cochain_comp_snd (cocycle.of_hom φ)
    (α : cochain K F 1) β (by linarith), },
  congr' 1,
  tidy,
end

@[simp, reassoc]
lemma mapping_cone.lift_snd_f {K : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0) (n : ℤ) :
  (mapping_cone.lift φ α β hαβ).f n ≫ (mapping_cone_snd φ).v n n (add_zero n).symm =
    β.v n n (add_zero n).symm :=
by simp only [← cochain.congr_v (mapping_cone.lift_snd φ α β hαβ) n n (by linarith),
  cochain.comp_zero_cochain, cochain.of_hom_v]

#exit

lemma mapping_cone.lift_desc_f {K L : cochain_complex C ℤ} (α : cocycle K F 1) (β : cochain K G 0)
  (hαβ : δ 0 1 β + (α : cochain K F 1).comp (cochain.of_hom φ) (add_zero 1).symm = 0)
  (α' : cochain F L (-1)) (β' : G ⟶ L) (eq : δ (-1) 0 α' = cochain.of_hom (φ ≫ β'))
  (n n' : ℤ) (hnn' : n' = n+1) :
  (mapping_cone.lift φ α β hαβ).f n ≫ (mapping_cone.desc φ α' β' eq).f n =
    (α : cochain K F 1).v n n' hnn' ≫ α'.v n' n (by { rw [hnn', int.add_neg_one, add_tsub_cancel_right], }) +
      β.v n n (add_zero n).symm ≫ β'.f n :=
begin
  dsimp only [mapping_cone.lift, mapping_cone.lift_cocycle,
    mapping_cone.desc, mapping_cone.desc_cocycle, twist.lift_cocycle,
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

-- mapping_cone.lift_homotopy ?

end preadditive

section abelian

open hom_complex
variables [abelian C] {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

instance (n : ℤ) :
  preserves_finite_limits (homological_complex.eval C (complex_shape.up ℤ) n) := sorry
instance (n : ℤ) :
  preserves_finite_colimits (homological_complex.eval C (complex_shape.up ℤ) n) := sorry

include ex

lemma degreewise_exact (n : ℤ) :
  (S.map (homological_complex.eval C (complex_shape.up ℤ) n)).short_exact :=
ex.map_of_exact (homological_complex.eval C (complex_shape.up ℤ) n)

def from_mapping_cone_of_ses : mapping_cone S.f ⟶ S.X₃ :=
cocycle.hom_of
  (twist.desc_cocycle _ (0 : cochain _ _ (-1))
    (cocycle.of_hom S.g) (by linarith) (add_zero 0).symm
      (by simp only [δ_zero, ε_0, cocycle.of_hom_coe,
        one_zsmul, ← cochain.of_hom_comp, S.zero, cochain.of_hom_zero]))

@[simp, reassoc]
lemma inr_from_mapping_cone_of_ses (n : ℤ) :
  (mapping_cone_inr S.f).f n ≫ (from_mapping_cone_of_ses ex).f n = S.g.f n :=
begin
  dsimp only [from_mapping_cone_of_ses, mapping_cone_inr, twist.inr,
    twist.desc_cocycle],
  simp only [twist.desc_cochain_eq _ _ _ _ (zero_add 1), twist.snd, zero_add, cochain.comp_zero,
    cocycle.of_hom_coe, cocycle.hom_of_f, cocycle.mk_coe, cochain.comp_zero_cochain,
    cochain.mk_v, hom_complex.cochain.of_hom_v, homological_complex.id_f, comp_id,
    biprod.inr_snd_assoc],
end

@[simp, reassoc]
lemma inl_from_mapping_cone_of_ses (p q : ℤ) (hpq : q = p + (-1)) :
  (mapping_cone_inl S.f).v p q hpq ≫ (from_mapping_cone_of_ses ex).f q = 0 :=
begin
  have eq := hom_complex.cochain.congr_v
    (hom_complex.twist.inl_comp_snd (hom_complex.cocycle.of_hom S.f) (neg_add_self 1)) p q (by linarith),
  rw hom_complex.cochain.comp_v _ _ _ p q q hpq (add_zero q).symm at eq,
  dsimp only [mapping_cone_inl, from_mapping_cone_of_ses, hom_complex.twist.desc_cocycle],
  simp only [cocycle.of_hom_coe, cocycle.hom_of_f, cocycle.mk_coe,
    twist.desc_cochain_eq _ _ _ _ (zero_add 1), zero_add, cochain.comp_zero,
    cochain.comp_zero_cochain, cochain.of_hom_v, ← assoc, eq,
    cochain.zero_v, zero_comp],
end

lemma from_mapping_cone_of_ses_quasi_iso : quasi_iso (from_mapping_cone_of_ses ex) :=
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
    obtain ⟨x, y, rfl⟩ := to_mapping_cone_decomposition x₂ _ rfl,
    simp only [preadditive.add_comp, assoc, mapping_cone_inr_d, preadditive.comp_sub,
      mapping_cone_inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith)] at hxy,
    obtain ⟨hx, hy⟩ := (to_mapping_cone_ext_iff _ _ _ rfl).mp hxy,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone_inr_fst,
      comp_zero, mapping_cone_inl_fst, comp_id, zero_sub, add_zero, zero_comp, neg_eq_zero] at hx,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone_inr_snd, comp_id,
      mapping_cone_inl_snd, comp_zero, sub_zero, zero_comp, ← eq_neg_iff_add_eq_zero] at hy,
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
    refine ⟨A', π, hπ, w ≫ (mapping_cone_inl S.f).v n (n-1) (show n-1 = n+(-1), by refl) + z' ≫ (mapping_cone_inr S.f).f (n-1),
      (to_mapping_cone_ext_iff _ _ _ rfl).mpr ⟨_, _⟩⟩,
    { simp only [assoc, preadditive.add_comp, mapping_cone_inr_fst, comp_zero, add_zero,
        mapping_cone_inl_fst, comp_id, mapping_cone_inr_d_assoc,
        mapping_cone_inl_d_assoc S.f (n-1) n (n+1) (by refl) (by linarith),
        preadditive.sub_comp, preadditive.comp_sub, ← cancel_mono (S.f.f (n+1)), zero_comp],
      simp only [← S.f.comm, reassoc_of hw, preadditive.sub_comp, assoc, homological_complex.d_comp_d,
        comp_zero, sub_zero, zero_sub, hy, preadditive.comp_neg], },
    { simp only [assoc, preadditive.comp_add, preadditive.add_comp, mapping_cone_inl_snd, comp_zero,
        zero_add, mapping_cone_inr_snd, comp_id, mapping_cone_inr_d_assoc, preadditive.comp_sub,
        preadditive.sub_comp, hw,
        mapping_cone_inl_d S.f (n-1) n (n+1) (show n-1 = n+(-1), by refl) (by linarith)],
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
    refine ⟨A', π, hπ, y ≫ (mapping_cone_inr S.f).f n -
      x ≫ (mapping_cone_inl S.f).v (n+1) n (show n = (n+1)+(-1), by linarith), _, _⟩,
    { simp only [preadditive.sub_comp, assoc, mapping_cone_inr_d, ← reassoc_of hx,
        mapping_cone_inl_d S.f n (n+1) (n+1+1) (by linarith) (by linarith), preadditive.comp_sub,
        reassoc_of hdx, zero_comp, sub_zero, sub_self], },
    { exact ⟨0, by simp only [hy, preadditive.sub_comp, assoc, inr_from_mapping_cone_of_ses,
        inl_from_mapping_cone_of_ses, comp_zero, sub_zero, zero_comp, add_zero]⟩, }, },
end⟩

end abelian

end cochain_complex
