import category_theory.shift
import tactic.linarith

noncomputable theory

namespace category_theory

open category

variables {C D : Type*} [category C] [category D] (F : C ⥤ D)
  {A G : Type*} [add_monoid A] [add_group G]
  [has_shift C A] [has_shift D A] [has_shift C G] [has_shift D G]
  [has_shift C ℤ] [has_shift D ℤ]

variable (C)

def shift_functor_iso_of_eq {a b : A} (h : a = b) :
  shift_functor C a ≅ shift_functor C b := eq_to_iso (by rw h)

def shift_functor_add' (a b c : A) (h : a + b = c) :
  shift_functor C c ≅ shift_functor C a ⋙ shift_functor C b :=
(shift_functor_iso_of_eq C h.symm) ≪≫ shift_functor_add C a b

namespace functor

variables (A) {C}

def comm_shift_iso := Π (a : A), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a

@[simps]
def comm_shift_iso₀ : shift_functor C (0 : A) ⋙ F ≅ F ⋙ shift_functor D (0 : A) :=
calc shift_functor C (0 : A) ⋙ F ≅ 𝟭 _ ⋙ F : iso_whisker_right (shift_functor_zero C A) _
... ≅ F : left_unitor F
... ≅ F ⋙ 𝟭 _ : (right_unitor F).symm
... ≅ F ⋙ shift_functor D (0 : A) : iso_whisker_left _ (shift_functor_zero D A).symm

variable {A}

def comm_shift_iso_of_eq {a b : A} (h : a = b)
  (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b :=
iso_whisker_right (shift_functor_iso_of_eq C h.symm) F ≪≫
    e ≪≫ iso_whisker_left F (shift_functor_iso_of_eq D h)

@[simp]
def comm_shift_iso_of_eq_refl (a : A)
  (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  comm_shift_iso_of_eq F (rfl : a = a) e = e :=
begin
  ext1,
  dsimp [comm_shift_iso_of_eq, iso.trans, shift_functor_iso_of_eq],
  simp only [whisker_right_id', comp_id, id_comp],
end

@[simp]
lemma comm_shift_iso_eq_of_eq {a b : A} (h : a = b)
  (e : comm_shift_iso F A) : comm_shift_iso_of_eq F h (e a) = e b :=
begin
  subst h,
  ext1,
  dsimp [comm_shift_iso_of_eq, shift_functor_iso_of_eq],
  simp only [whisker_right_id', comp_id, id_comp],
end

@[simps]
def comm_shift_iso_add (a b c : A) (h : a + b = c)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c :=
calc shift_functor C c ⋙ F ≅ shift_functor C (a + b) ⋙ F :
  iso_whisker_right (shift_functor_iso_of_eq C h.symm) _
... ≅ (shift_functor C a ⋙ shift_functor C b) ⋙ F :
  iso_whisker_right (shift_functor_add C a b) _
... ≅ _ : functor.associator _ _ _
... ≅ _ : iso_whisker_left _ e₂
... ≅ _ : (functor.associator _ _ _).symm
... ≅ _ : iso_whisker_right e₁ _
... ≅ _ : functor.associator _ _ _
... ≅ _ : iso_whisker_left _ (shift_functor_add D a b).symm
... ≅ _ : iso_whisker_left _ (shift_functor_iso_of_eq D h)

lemma comm_shift_iso_add_zero {a b : A} (h : a = b)
  (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  F.comm_shift_iso_add a 0 b ((add_zero a).trans h) e (F.comm_shift_iso₀ A) =
    F.comm_shift_iso_of_eq h e := sorry

lemma comm_shift_iso_zero_add {a b : A} (h : a = b)
  (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  F.comm_shift_iso_add 0 a b ((zero_add a).trans h)
      (F.comm_shift_iso₀ A) e = F.comm_shift_iso_of_eq h e := sorry

include F
lemma comm_shift_iso_add_assoc (a b c ab bc abc : A) (hab : a + b = ab) (hbc : b + c = bc)
  (habc : abc = a + b + c)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  (e₃ : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c) :
  comm_shift_iso_add F ab c abc (by rw [habc, hab])
    (comm_shift_iso_add F a b ab hab e₁ e₂) e₃ =
  comm_shift_iso_add F a bc abc (by rw [habc, add_assoc, hbc]) e₁
    (comm_shift_iso_add F b c bc hbc e₂ e₃) := sorry

@[simps]
def comm_shift_iso_cancel_add (a b c : A) (h : a + b = c)
  (e₁ : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a :=
begin
  let eq := as_equivalence (shift_functor D b),
  calc shift_functor C a ⋙ F ≅ _ ⋙ 𝟭 D : (right_unitor _).symm
  ... ≅ _ : iso_whisker_left _ eq.unit_iso
  ... ≅ _ : functor.associator _ _ _
  ... ≅ _ : iso_whisker_left _ (functor.associator _ _ _).symm
  ... ≅ _ : iso_whisker_left _ (iso_whisker_right e₂.symm _)
  ... ≅ _ : (functor.associator _ _ _).symm
  ... ≅ _ : iso_whisker_right (functor.associator _ _ _).symm _
  ... ≅ _ : iso_whisker_right (iso_whisker_right (shift_functor_add' C a b c h).symm _) _
  ... ≅ _ : iso_whisker_right e₁ _
  ... ≅ _ : functor.associator _ _ _
  ... ≅ _ : iso_whisker_left _ (iso_whisker_right ((shift_functor_add' D a b c h)) _)
  ... ≅ _ : iso_whisker_left _ (functor.associator _ _ _)
  ... ≅ _ : iso_whisker_left _ (iso_whisker_left _ eq.unit_iso.symm)
  ... ≅ _ : (functor.associator _ _ _).symm
  ... ≅ _ : right_unitor _
end

@[simp]
lemma comm_shift_iso_cancel_add_add (a b c : A) (h : a + b = c)
  (e₁ : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  F.comm_shift_iso_add a b c h (F.comm_shift_iso_cancel_add a b c h e₁ e₂) e₂ = e₁ := sorry

lemma comm_shift_iso_cancel_add' (a b c : A) (h : a + b = c)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  e₁ = F.comm_shift_iso_cancel_add a b c h (F.comm_shift_iso_add a b c h e₁ e₂) e₂ :=
begin
  ext X,
  dsimp [comm_shift_iso_cancel_add, comm_shift_iso_add],
  simp only [assoc, id_comp, comp_id, functor.map_id,
    ← functor.map_comp],
  apply (shift_functor D b).map_injective,
  sorry,
end

def comm_shift_iso_add_injective (a b c : A) (h : a + b = c)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) [is_equivalence (shift_functor D b)] :
  function.injective (λ e₁, F.comm_shift_iso_add a b c h e₁ e₂) :=
begin
  intros e₁ e₁' h',
  rw [comm_shift_iso_cancel_add' F _ _ _ h e₁ e₂, comm_shift_iso_cancel_add' F _ _ _ h e₁' e₂],
  congr' 1,
end

variables (F A)

@[ext]
structure comm_shift :=
(iso : comm_shift_iso F A)
(iso_zero : iso 0 = comm_shift_iso₀ F A)
(iso_add : ∀ (a b : A), iso (a + b) = comm_shift_iso_add F a b _ rfl (iso a) (iso b))

namespace comm_shift

variables {F A}

lemma iso_add_eq_of_iso_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (ha : e₁.iso a = e₂.iso a) (hb : e₁.iso b = e₂.iso b) :
  e₁.iso (a + b) = e₂.iso (a + b) :=
by rw [e₁.iso_add, e₂.iso_add, ha, hb]

lemma iso_eq_of_iso_add_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (hb : e₁.iso b = e₂.iso b) (hab : e₁.iso (a + b) = e₂.iso (a+b))
  [is_equivalence (shift_functor D b)] : e₁.iso a = e₂.iso a :=
begin
  rw F.comm_shift_iso_cancel_add' a b _ rfl (e₁.iso a) (e₁.iso b),
  rw F.comm_shift_iso_cancel_add' a b _ rfl (e₂.iso a) (e₂.iso b),
  congr' 1,
  rw [← e₁.iso_add, ← e₂.iso_add, hab],
end

@[ext]
lemma iso_eq_of_iso_one_eq (e₁ e₂ : F.comm_shift ℤ)
  (h : e₁.iso (1 : ℤ) = e₂.iso (1 : ℤ)) : e₁ = e₂ :=
begin
  suffices : ∀ (n : ℕ), e₁.iso (n : ℤ) = e₂.iso (n : ℤ),
  { ext n : 2,
    cases n,
    { apply this, },
    { have eq : (-[1+n]+(1+n)) = 0,
      { simp only [int.neg_succ_of_nat_coe, nat.cast_add, nat.cast_one, neg_add_rev],
        linarith, },
      refine iso_eq_of_iso_add_eq e₁ e₂ (-[1+n]) (1+n) (this _) _,
      rw [eq, e₁.iso_zero, e₂.iso_zero], }, },
  intro n,
  induction n with n hn,
  { exact e₁.iso_zero.trans (e₂.iso_zero.symm), },
  { rw [nat.cast_succ, e₁.iso_add, e₂.iso_add, hn, h], },
end

end comm_shift

section

namespace comm_shift_iso

def ℤ_mk' (e : comm_shift_iso F ℤ) (e₀ : e 0 = comm_shift_iso₀ F ℤ)
  (e_add_one : ∀ (n : ℤ), e (n + 1) = comm_shift_iso_add F n 1 _ rfl (e n) (e 1)) : F.comm_shift ℤ :=
{ iso := e,
  iso_zero := e₀,
  iso_add := begin
    have e_add_one' : ∀ (n m : ℤ) (h : m + 1 = n),
      e n = comm_shift_iso_add F _ _ _ h (e m) (e 1),
    { intros n m h,
      subst h,
      exact e_add_one m, },
    have h : ∀ (b : ℕ) (a c : ℤ) (hc : a + b = c), e c = F.comm_shift_iso_add a b c hc (e a) (e b),
    { intros b a c hc,
      subst hc,
      revert a,
      induction b with b hb,
      { intro a,
        erw e₀,
        erw F.comm_shift_iso_add_zero (show a = a + (0 : ℕ), by simp) (e a),
        rw comm_shift_iso_eq_of_eq, },
      { intro a,
        rw [e_add_one' b.succ b (by simp),
          ← comm_shift_iso_add_assoc F a b 1 (a + b) b.succ (a + b.succ) rfl (by simp)
          (by { push_cast, rw add_assoc, }), ← hb, e_add_one'], }, },
    have h'' : ∀ (b : ℕ) (a : ℤ), e (a - b) = F.comm_shift_iso_add a (-b) _ rfl (e a) (e (- b)),
    { intros b a,
      apply comm_shift_iso_add_injective F (a - b) b a (by simp) (e b),
      dsimp only,
      rw ← h b (a - b) a (by simp),
      rw F.comm_shift_iso_add_assoc a (-b) b (a-b) 0 a rfl (by simp) (by simp),
      rw ← h b (-b) 0 (by simp),
      rw e₀,
      rw F.comm_shift_iso_add_zero rfl (e a),
      rw comm_shift_iso_eq_of_eq, },
    rintro a (b|b),
    { apply h, },
    { have eq : -[1+b] = -(1+b),
      { rw int.neg_succ_of_nat_coe,
        push_cast,
        congr' 1,
        rw add_comm, },
      convert h'' (1+b) a, },
  end, }

variable (e : shift_functor C (1 : ℤ) ⋙ F ≅ F ⋙ shift_functor D (1 : ℤ))

noncomputable def ℤ_mk_iso_pos :
  Π (n : ℕ), shift_functor C (n : ℤ) ⋙ F ≅ F ⋙ shift_functor D (n : ℤ)
| 0 := F.comm_shift_iso₀ ℤ
| 1 := e
| (n+1) := F.comm_shift_iso_add (n : ℤ) 1 _ rfl (ℤ_mk_iso_pos n) e

lemma ℤ_mk_iso_pos_one : ℤ_mk_iso_pos F e 1 = e := rfl

lemma ℤ_mk_iso_pos_succ (n : ℕ) :
  ℤ_mk_iso_pos F e (n+1) = F.comm_shift_iso_add (n : ℤ) 1 _ rfl (ℤ_mk_iso_pos F e n) e :=
begin
  rcases n with (_|n),
  { unfold ℤ_mk_iso_pos,
    simpa only [comm_shift_iso_of_eq_refl] using
      (comm_shift_iso_zero_add F (rfl : 1 = 1) e).symm, },
  { unfold ℤ_mk_iso_pos, },
end

noncomputable
def ℤ_mk_iso : F.comm_shift_iso ℤ
| (int.of_nat n) := ℤ_mk_iso_pos F e n
| (int.neg_succ_of_nat n) := comm_shift_iso_cancel_add F (-[1+n]) (n+1) 0
      (by { simp only [int.neg_succ_of_nat_coe, int.coe_nat_succ], linarith, })
      (F.comm_shift_iso₀ ℤ) (ℤ_mk_iso_pos F e (n+1))

lemma ℤ_mk_iso_neg_add_self {a b : ℤ} (h : a + b = 0) (hb : 0 ≤ b) :
  F.comm_shift_iso_add _ _ _ h (ℤ_mk_iso F e a) (ℤ_mk_iso F e b) =
    F.comm_shift_iso₀ ℤ :=
begin
  cases a,
  { have eq : b = -int.of_nat a := by linarith,
    subst eq,
    simp only [int.of_nat_eq_coe, right.nonneg_neg_iff,
      int.coe_nat_nonpos_iff] at hb,
    subst hb,
    erw F.comm_shift_iso_zero_add (rfl : (0 : ℤ) = 0),
    simpa only [comm_shift_iso_of_eq_refl], },
  { have eqb : b = a+1,
    { rw int.neg_succ_of_nat_coe at h,
      push_cast at h,
      linarith, },
    subst eqb,
    apply F.comm_shift_iso_cancel_add_add, },
end

lemma ℤ_mk_iso_add_pos (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b):
  ℤ_mk_iso F e (a + b) = F.comm_shift_iso_add a b _ rfl (ℤ_mk_iso F e a)
    (ℤ_mk_iso F e b) := sorry

def ℤ_mk : F.comm_shift ℤ :=
ℤ_mk' F (ℤ_mk_iso F e) rfl
(λ n, begin
  cases n,
  { apply ℤ_mk_iso_pos_succ, },
  { apply F.comm_shift_iso_add_injective (-[1+n]+1) n 0
      (by { rw int.neg_succ_of_nat_coe, push_cast, simp, }) (ℤ_mk_iso F e n),
    simp only [ℤ_mk_iso_neg_add_self _ _ _ (nat.cast_nonneg _),
      F.comm_shift_iso_add_assoc (-[1+n]) 1 n (-[1+n]+1) (1+n) 0
      (by rw int.neg_succ_of_nat_coe) rfl
      (by { rw int.neg_succ_of_nat_coe, push_cast, simp, })
      (ℤ_mk_iso F e -[1+ n]) (ℤ_mk_iso F e 1) (ℤ_mk_iso F e n),
      ← ℤ_mk_iso_add_pos F e _ _ zero_le_one (nat.cast_nonneg _)],
    rw ℤ_mk_iso_neg_add_self F e,
    linarith, },
end)

end comm_shift_iso

end

end functor

end category_theory
