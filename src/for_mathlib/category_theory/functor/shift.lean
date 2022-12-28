import category_theory.shift
import tactic.linarith
import for_mathlib.category_theory.functor.shift_compatibility
import for_mathlib.category_theory.triangulated.shift_compatibility
import for_mathlib.category_theory.shift_misc

noncomputable theory

namespace category_theory

open category

variables {C D E : Type*} [category C] [category D] [category E] (F : C ⥤ D)
  {A G : Type*} [add_monoid A] [add_group G]
  [has_shift C A] [has_shift D A] [has_shift E A]
  [hCℤ : has_shift C ℤ] [hDℤ : has_shift D ℤ]

namespace functor

variables (F A)

namespace comm_shift

def unit : shift_functor C (0 : A) ⋙ F ≅ F ⋙ shift_functor D (0 : A) :=
shift.compatibility.comm_shift.unit _ _ F

@[simp]
lemma unit_hom_app (X : C) :
  (unit F A).hom.app X = F.map ((shift_functor_zero C A).hom.app X) ≫
    (shift_functor_zero D A).inv.app (F.obj X) :=
begin
  dsimp [unit, shift.compatibility.comm_shift.unit],
  erw [id_comp, id_comp],
end

variables {F A}

@[simp]
def change {a b : A} (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (h : a = b) :
  shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b :=
shift.compatibility.comm_shift.change e (eq_to_iso (by subst h))

def add {a b : A} (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b) :=
shift.compatibility.comm_shift.comp e₁ e₂

@[simp]
lemma add_hom_app {a b : A} (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) (X : C) :
  (add e₁ e₂).hom.app X = F.map ((shift_functor_add C a b).hom.app X) ≫
    e₂.hom.app (X⟦a⟧) ≫ (e₁.hom.app X)⟦b⟧' ≫ (shift_functor_add D a b).inv.app (F.obj X) :=
begin
  dsimp [add, shift.compatibility.comm_shift.comp],
  erw [id_comp, id_comp, id_comp],
end

@[simp]
def add' {a b c : A} (h : a + b = c) (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c :=
(shift.compatibility.comm_shift.comp e₁ e₂).change (eq_to_iso (by simpa only [← h]))

lemma add'_eq_add {a b : A} (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  add' rfl e₁ e₂ = add e₁ e₂ :=
by simp only [add', add, eq_to_iso_refl, shift.compatibility.comm_shift.change_refl]

def sub {a b : A} (e : shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b))
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) [is_equivalence (shift_functor D b)] :
  shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a :=
@shift.compatibility.comm_shift.comp_cancel _ _ _ _ _ _ _ _ _ F (discrete.mk a) (discrete.mk b) e f _

def add_equiv {b : A} (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] (a : A) :
  (shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) ≃
    (shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b)) :=
{ to_fun := λ e, add e f,
  inv_fun := λ e, sub e f,
  left_inv := (shift.compatibility.comm_shift.comp_equiv f (discrete.mk a)).left_inv,
  right_inv := (shift.compatibility.comm_shift.comp_equiv f (discrete.mk a)).right_inv, }

def sub' {a b c : A} (h : a + b = c) (e : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c)
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) [is_equivalence (shift_functor D b)] :
  shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a :=
sub (change e h.symm) f

lemma sub'_eq_sub {a b : A} (e : shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b))
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) [is_equivalence (shift_functor D b)] :
  sub' rfl e f = sub e f :=
begin
  dsimp only [sub'],
  simp only [change, eq_to_iso_refl, shift.compatibility.comm_shift.change_refl],
end

def add'_equiv {a b c : A} (h : a + b = c)
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  (shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) ≃
    (shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c) :=
{ to_fun := λ e, add' h e f,
  inv_fun := λ e, sub' h e f,
  left_inv := begin
    subst h,
    simpa only [sub'_eq_sub, add'_eq_add] using (add_equiv f a).left_inv,
  end,
  right_inv := begin
    subst h,
    simpa only [sub'_eq_sub, add'_eq_add] using (add_equiv f a).right_inv,
  end, }

lemma add_bijective {b : A} (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] (a : A) :
  function.bijective (λ (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a),
    add e f) :=
(add_equiv f a).bijective

lemma add'_bijective {a b c : A} (h : a + b = c)
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  function.bijective (λ (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a),
    add' h e f) :=
(add'_equiv h f).bijective

@[simp]
lemma add'_sub' {a b c : A} (h : a + b = c) (e : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c)
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) [is_equivalence (shift_functor D b)] :
  add' h (sub' h e f) f = e :=
(add'_equiv h f).right_inv e

lemma add'_assoc (a b c ab bc abc : A) (hab : a + b = ab) (hbc : b + c = bc)
  (habc : a + b + c = abc)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  (e₃ : shift_functor C c ⋙ F ≅ F ⋙ shift_functor D c) :
  add' (show ab + c = abc, by rw [← hab, habc]) (add' hab e₁ e₂) e₃ =
    add' (show a + bc = abc, by rw [← hbc, ← add_assoc, habc]) e₁ (add' hbc e₂ e₃) :=
begin
  substs hab hbc habc,
  simp only [add'_eq_add],
  apply shift.compatibility.comm_shift.comp_assoc,
end

@[protected]
lemma zero_add {a : A} (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  add (unit _ _) e = change e (zero_add a).symm :=
shift.compatibility.comm_shift.unit_comp e

@[protected]
lemma add_zero {a : A} (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  add e (unit _ _) = change e (add_zero a).symm :=
shift.compatibility.comm_shift.comp_unit e

@[simp]
lemma add'_zero {a : A} (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a) :
  add' (add_zero a) e (unit _ _) = e :=
begin
  change change (add e (unit _ _)) (add_zero a) = e,
  rw comm_shift.add_zero,
  simp only [change, shift.compatibility.comm_shift.change_comp, eq_to_iso_trans,
    eq_to_iso_refl, shift.compatibility.comm_shift.change_refl],
end

end comm_shift

variables (F A)

@[ext, nolint has_nonempty_instance]
class has_comm_shift :=
(iso : Π (a : A), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
(iso_zero : iso 0 = comm_shift.unit F A)
(iso_add : ∀ (a b : A), iso (a + b) = comm_shift.add (iso a) (iso b))

variable {A}
def comm_shift_iso [F.has_comm_shift A] (a : A) :
  shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a :=
has_comm_shift.iso a

lemma comm_shift_iso_add [F.has_comm_shift A] (a b : A) :
  F.comm_shift_iso (a + b) = comm_shift.add (F.comm_shift_iso a) (F.comm_shift_iso b) :=
has_comm_shift.iso_add _ _

variable (A)

lemma comm_shift_iso_zero [F.has_comm_shift A] :
  F.comm_shift_iso (0 : A) = comm_shift.unit F A :=
has_comm_shift.iso_zero

variable {A}
lemma comm_shift_congr_iso {a b : A} [F.has_comm_shift A] (h : a = b) (X : C) :
  (F.comm_shift_iso a).hom.app X = eq_to_hom (by rw h) ≫
    (F.comm_shift_iso b).hom.app X ≫ eq_to_hom (by rw h) :=
by { subst h, simp only [eq_to_hom_refl, comp_id, id_comp], }

namespace comm_shift

variables {F A}

lemma iso_add_eq_of_iso_eq (e₁ e₂ : F.has_comm_shift A) (a b : A)
  (ha : e₁.iso a = e₂.iso a) (hb : e₁.iso b = e₂.iso b) :
  e₁.iso (a + b) = e₂.iso (a + b) :=
by rw [e₁.iso_add, e₂.iso_add, ha, hb]

lemma iso_eq_of_iso_add_eq (e₁ e₂ : F.has_comm_shift A) (a b : A)
  (hb : e₁.iso b = e₂.iso b) (hab : e₁.iso (a + b) = e₂.iso (a+b))
  [is_equivalence (shift_functor D b)] : e₁.iso a = e₂.iso a :=
(comm_shift.add_bijective (e₁.iso b) a).1
  (by { dsimp only, rw [← e₁.iso_add, hb, ← e₂.iso_add, hab], })

include hCℤ hDℤ

@[ext]
lemma eq_of_iso_one_eq (e₁ e₂ : F.has_comm_shift ℤ)
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

variable (e : shift_functor C (1 : ℤ) ⋙ F ≅ F ⋙ shift_functor D (1 : ℤ))

namespace mk_ℤ

noncomputable
def iso_ℕ : Π (n : ℕ), shift_functor C (int.of_nat n) ⋙ F ≅ F ⋙ shift_functor D (int.of_nat n)
| 0 := unit _ _
| 1 := e
| (n+2) := add (iso_ℕ (n+1)) e

@[simp]
lemma iso_ℕ_zero : iso_ℕ e 0 = unit _ _ := rfl

@[simp]
lemma iso_ℕ_one : iso_ℕ e 1 = e := rfl

lemma iso_ℕ_add_one (n : ℕ) : add (iso_ℕ e n) e = iso_ℕ e (n+1) :=
begin
  cases n,
  { unfold iso_ℕ,
    simp only [comm_shift.zero_add, change, eq_to_iso_refl, shift.compatibility.comm_shift.change_refl], },
  { unfold iso_ℕ, },
end

lemma iso_ℕ_add'_one (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
  add' (by { simp only [← h, int.of_nat_eq_coe], push_cast, })
    (iso_ℕ e n₀) e = iso_ℕ e n₁ :=
begin
  subst h,
  erw add'_eq_add,
  apply iso_ℕ_add_one,
end

def iso_ℤ : Π (n : ℤ), shift_functor C (n : ℤ) ⋙ F ≅ F ⋙ shift_functor D (n : ℤ)
| (int.of_nat n) := iso_ℕ e n
| -[1+n] := sub' (by { rw int.of_nat_eq_coe, rw int.neg_succ_of_nat_coe', push_cast, linarith, })
  (unit F ℤ) (iso_ℕ e (1+n))

@[simp]
lemma iso_ℤ_zero : iso_ℤ e 0 = unit _ _ := rfl

@[simp]
lemma iso_ℤ_one : iso_ℤ e 1 = e := rfl

lemma iso_ℕ_add' (n₁ n₂ n₃ : ℕ) (h : n₁ + n₂ = n₃) :
  add' (by simp only [← h, int.of_nat_eq_coe, nat.cast_add]) (iso_ℕ e n₁) (iso_ℕ e n₂) =
    iso_ℕ e n₃ :=
begin
  revert h n₃ n₁,
  induction n₂ with n₂ hn₂,
  { intros n₁ n₃ h,
    have h' : n₁ = n₃ := by simpa only [add_zero] using h,
    subst h',
    exact add'_zero (iso_ℕ e n₁), },
  { intros n₁ n₃ h,
    rw ← iso_ℕ_add_one,
    rw ← add'_eq_add,
    conv_lhs { congr, skip, congr, skip, rw ← iso_ℕ_one e, },
    erw ← add'_assoc (int.of_nat n₁) (int.of_nat n₂) 1 (int.of_nat (n₁ + n₂))
      (int.of_nat n₂ + 1) n₃ (by simp) (by simp) (by { rw ← h, push_cast, simp, rw add_assoc,}),
    rw hn₂ _ _ rfl,
    erw iso_ℕ_add'_one,
    rw [← h, nat.succ_eq_add_one, add_assoc], },
end

lemma iso_ℤ_add'_nonneg (n₁ n₂ n₃ : ℤ) (h : n₁ + n₂ = n₃) (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) :
  add' h (iso_ℤ e n₁) (iso_ℤ e n₂) = iso_ℤ e n₃ :=
begin
  have h₁ : ∃ (m₁ : ℕ), n₁ = int.of_nat m₁ := int.eq_coe_of_zero_le hn₁,
  have h₂ : ∃ (m₂ : ℕ), n₂ = int.of_nat m₂ := int.eq_coe_of_zero_le hn₂,
  rcases h₁ with ⟨m₁, hm₁⟩,
  rcases h₂ with ⟨m₂, hm₂⟩,
  have h₃ : n₃ = int.of_nat (m₁ + m₂),
  { simp only [← h, hm₁, hm₂, int.of_nat_eq_coe, nat.cast_add], },
  substs hm₁ hm₂ h₃,
  unfold iso_ℤ,
  exact iso_ℕ_add' e _ _ _ rfl,
end

lemma iso_ℤ_add'_neg (n₁ n₂ : ℤ) (h : n₁ + n₂ = 0) (hn₂ : 0 ≤ n₂):
  add' h (iso_ℤ e n₁) (iso_ℤ e n₂) = unit F ℤ :=
begin
  cases n₁,
  { have hn₁ : 0 ≤ int.of_nat n₁ := int.of_nat_nonneg n₁,
    have h₂ : n₂ = 0 := by linarith,
    subst h₂,
    have h₁ : n₁ = 0 := by simpa only [int.of_nat_eq_coe, add_zero, nat.cast_eq_zero] using h,
    subst h₁,
    erw [iso_ℤ_zero, add'_zero], },
  { have h₂ : n₂ = int.of_nat (1 + n₁),
    { rw int.neg_succ_of_nat_coe' at h,
      rw int.of_nat_eq_coe,
      push_cast,
      linarith, },
    subst h₂,
    unfold iso_ℤ,
    apply add'_sub', },
end

lemma iso_ℤ_add'_one (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : add' h (iso_ℤ e n₀) e = iso_ℤ e n₁ :=
begin
  cases n₀,
  { have h₁ : n₁ = int.of_nat (n₀ + 1),
    { rw ← h, simp, },
    subst h₁,
    unfold iso_ℤ,
    rw ← iso_ℕ_add_one e n₀,
    apply add'_eq_add, },
  { have h' := h,
    rw int.neg_succ_of_nat_coe' at h',
    apply (add'_bijective (show n₁ + int.of_nat n₀ = 0, by { rw int.of_nat_eq_coe, linarith, })
      (iso_ℤ e (int.of_nat n₀))).1 _,
    simp only,
    rw iso_ℤ_add'_neg e, swap, { apply int.of_nat_nonneg, },
    rw add'_assoc (-[1+n₀]) 1 (int.of_nat n₀) n₁ (int.of_nat (1+n₀)) 0 h
      (by simp) (by { rw int.neg_succ_of_nat_coe', simp,}),
    conv_lhs { congr, skip, congr, rw ← iso_ℤ_one e, },
    rw iso_ℤ_add'_nonneg e 1 (int.of_nat n₀) (int.of_nat (1+n₀)) (by simp) zero_le_one (int.of_nat_nonneg n₀),
    apply iso_ℤ_add'_neg,
    apply int.of_nat_nonneg, },
end

lemma iso_ℤ_add_one (n : ℤ) : add (iso_ℤ e n) (iso_ℤ e 1) = iso_ℤ e (n + 1) :=
begin
  rw ← add'_eq_add,
  apply iso_ℤ_add'_one,
end

end mk_ℤ

@[simps]
def mk'_ℤ (iso : Π (a : ℤ), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (iso_zero : iso 0 = comm_shift.unit F ℤ)
  (iso_add_one : ∀ (a : ℤ), iso (a + 1) = comm_shift.add (iso a) (iso 1)) :
  has_comm_shift F ℤ :=
{ iso := iso,
  iso_zero := iso_zero,
  iso_add := begin
    have iso_add_one' : ∀ (a b : ℤ) (h : a + 1 = b),
      iso b = comm_shift.add' h (iso a) (iso 1),
    { intros a b h,
      subst h,
      rw add'_eq_add,
      apply iso_add_one, },
    suffices : ∀ (a b c : ℤ) (h : a + b = c) (hb : 0 ≤ b),
      iso c = add' h (iso a) (iso b),
    { intros a b,
      by_cases hb : 0 ≤ b,
      { rw [this a b _ rfl hb, add'_eq_add], },
      { rw ← add'_eq_add,
        apply (add'_bijective (show (a+b)+(-b) = a, by linarith) (iso (-b))).1,
        simp only [← this (a+b) (-b) a (by linarith) (by linarith),
          add'_assoc a b (-b) (a+b) 0 a rfl (by linarith) (by linarith),
          ← this b (-b) 0 (by linarith) (by linarith), iso_zero, add'_zero], }, },
    intros a b c h hb,
    obtain ⟨b', hb'⟩ := int.eq_coe_of_zero_le hb,
    subst hb',
    clear hb,
    revert a c,
    induction b' with b hb,
    { intros a c h,
      have hc : c = a := by simp only [←h, nat.cast_zero, add_zero],
      subst hc,
      erw [iso_zero, add'_zero], },
    { intros a c h,
      rw iso_add_one' b b.succ (by push_cast),
      rw ← add'_assoc a b 1 _ b.succ c rfl (by push_cast)
        (by { rw ← h, push_cast, rw add_assoc, }),
      rw ← hb a _ rfl,
      apply iso_add_one', },
  end}

@[simps]
def mk_ℤ (e : shift_functor C (1 : ℤ) ⋙ F ≅ F ⋙ shift_functor D (1 : ℤ)) :
  has_comm_shift F ℤ :=
mk'_ℤ (mk_ℤ.iso_ℤ e) rfl (λ a, (mk_ℤ.iso_ℤ_add_one e a).symm)

variable (F)

@[simps]
def equiv_ℤ : has_comm_shift F ℤ ≃
  (shift_functor C (1 : ℤ) ⋙ F ≅ F ⋙ shift_functor D (1 : ℤ)) :=
{ to_fun := λ c, c.iso 1,
  inv_fun := λ e, mk_ℤ e,
  left_inv := λ c, by { ext, refl, },
  right_inv := λ e, rfl, }

end comm_shift

variable {A}

lemma iso_add_hom_app (F : C ⥤ D) [F.has_comm_shift A] (p q : A) (X : C) :
  (F.comm_shift_iso (p+q)).hom.app X = F.map ((shift_functor_add C p q).hom.app X) ≫
    (F.comm_shift_iso q).hom.app (X⟦p⟧) ≫ ((F.comm_shift_iso p).hom.app X)⟦q⟧' ≫
    (shift_functor_add D p q).inv.app (F.obj X) :=
begin
  simp only [comm_shift_iso_add, comm_shift.add, shift.compatibility.comm_shift.comp_hom_app,
    iso.symm_hom, iso.symm_inv, monoidal_functor.μ_iso_hom],
end

lemma map_shift_functor_add_comm {A : Type*} [add_comm_monoid A] (F : C ⥤ D)
  [has_shift C A] [has_shift D A] [F.has_comm_shift A] (p q : A) (X : C) :
    F.map ((shift_functor_add_comm C p q).hom.app X) ≫
      (F.comm_shift_iso p).hom.app (X⟦q⟧) ≫ ((F.comm_shift_iso q).hom.app X)⟦p⟧' =
    (F.comm_shift_iso q).hom.app (X⟦p⟧) ≫ ((F.comm_shift_iso p).hom.app X)⟦q⟧' ≫
      (shift_functor_add_comm D p q).hom.app (F.obj X) :=
begin
  have eq₁ := F.iso_add_hom_app p q X,
  simp only [← cancel_mono ((shift_functor_add D p q).hom.app (F.obj X)),
    assoc, iso.inv_hom_id_app] at eq₁,
  erw comp_id at eq₁,
  have eq₂ := F.iso_add_hom_app q p X,
  simp only [← cancel_epi (F.map ((shift_functor_add C q p).inv.app X)),
    ← F.map_comp_assoc, iso.inv_hom_id_app, F.map_id, id_comp] at eq₂,
  simp only [← cancel_epi (F.map ((shift_functor_add C p q).hom.app X)),
    ← cancel_mono ((shift_functor_add D q p).inv.app (F.obj X)), assoc],
  slice_rhs 1 3 { rw ← eq₁, },
  simp only [assoc, ← eq₂], clear eq₁ eq₂,
  dsimp only [shift_functor_add_comm, iso.symm, iso.trans, nat_trans.comp_app],
  simpa only [F.map_comp, ← F.map_comp_assoc, assoc, eq_to_iso, eq_to_hom_app, eq_to_hom_map,
    iso.hom_inv_id_app, iso.hom_inv_id_app_assoc, F.map_id, id_comp, comp_id,
    F.comm_shift_congr_iso (add_comm p q), assoc, eq_to_hom_trans, eq_to_hom_refl],
end

@[reassoc]
lemma compatibility_composition (F₁ : C ⥤ D) (F₂ : D ⥤ E)
  [F₁.has_comm_shift A] [F₂.has_comm_shift A] (a b : A) (X : C) :
  F₂.map ((shift_functor D b).map ((F₁.comm_shift_iso a).hom.app X)) ≫
  (F₂.comm_shift_iso b).hom.app ((shift_functor D a).obj (F₁.obj X)) =
  (F₂.comm_shift_iso b).hom.app (F₁.obj ((shift_functor C a).obj X)) ≫
    (shift_functor E b).map (F₂.map ((F₁.comm_shift_iso a).hom.app X)) :=
begin
  let α := (F₁.comm_shift_iso a).hom,
  let β := (F₂.comm_shift_iso b).hom,
  have eq := nat_trans.exchange (F₁.comm_shift_iso a).hom (𝟙 _) (𝟙 _) (F₂.comm_shift_iso b).hom,
  simp only [id_comp, comp_id] at eq,
  replace eq := congr_app eq.symm X,
  dsimp at eq,
  simpa only [assoc, id_comp, functor.map_id, comp_id] using eq,
end

instance has_comm_shift_comp (F₁ : C ⥤ D) (F₂ : D ⥤ E)
  [F₁.has_comm_shift A] [F₂.has_comm_shift A] : (F₁ ⋙ F₂).has_comm_shift A :=
{ iso := λ a, comm_shift_comp (F₁.comm_shift_iso a) (F₂.comm_shift_iso a),
  iso_zero := begin
    ext X,
    simp only [comm_shift_comp_hom_app, F₁.comm_shift_iso_zero A,
      F₂.comm_shift_iso_zero A],
    dsimp only [comm_shift.unit, shift.compatibility.comm_shift.unit],
    simp only [iso.trans_hom, iso_whisker_right_hom, iso.symm_hom,
      iso_whisker_left_hom, monoidal_functor.ε_iso_hom,
      nat_trans.comp_app, whisker_right_app, left_unitor_hom_app, right_unitor_inv_app,
      whisker_left_app, id_comp, map_comp, assoc, comp_map],
    erw [functor.map_id, id_comp, id_comp],
    dsimp [monoidal_functor.ε_iso],
    nth_rewrite 1 ← F₂.map_comp_assoc,
    rw [← nat_trans.comp_app, is_iso.hom_inv_id],
    erw [F₂.map_id, id_comp],
  end,
  iso_add := λ a b, begin
    ext X,
    simp only [assoc, comm_shift_comp_hom_app, comm_shift.add_hom_app, comp_map,
      comm_shift_iso_add, functor.map_comp, comp],
    slice_lhs 4 5 { erw [← F₂.map_comp, iso.inv_hom_id_app, F₂.map_id], },
    simpa only [assoc, id_comp, compatibility_composition_assoc],
  end, }

lemma shift_functor_add'_hom_app_obj [F.has_comm_shift A] (a b c : A) (h : c = a + b)
  (K : C) :
  ((shift_functor_add' D a b c) h).hom.app (F.obj K) =
    (F.comm_shift_iso c).inv.app K ≫
      F.map (((shift_functor_add' _ a b c) h).hom.app K) ≫
      (F.comm_shift_iso b).hom.app (K⟦a⟧) ≫
      (shift_functor D b).map ((F.comm_shift_iso a).hom.app K) :=
begin
  subst h,
  simp only [shift_functor_add'_eq_shift_functor_add, F.comm_shift_iso_add,
    comm_shift.add, iso.symm_hom, shift.compatibility.comm_shift.comp_inv_app, assoc,
    ← F.map_comp_assoc, μ_hom_inv_app],
  erw [F.map_id, id_comp, iso.inv_hom_id_app_assoc, ← functor.map_comp,
    iso.inv_hom_id_app, functor.map_id, comp_id],
end

variable (A)

lemma shift_functor_zero_hom_app_obj [F.has_comm_shift A] (K : C) :
  (shift_functor_zero D A).hom.app (F.obj K) =
    (F.comm_shift_iso 0).inv.app K ≫ F.map ((shift_functor_zero C A).hom.app K) :=
begin
  rw F.comm_shift_iso_zero,
  dsimp [comm_shift.unit, shift.compatibility.comm_shift.unit],
  erw [comp_id, comp_id, assoc, ← F.map_comp],
  simp only [ε_hom_inv_app, map_id, comp_id],
end

end functor

end category_theory
