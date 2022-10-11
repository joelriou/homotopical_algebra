import category_theory.shift
import tactic.linarith
import for_mathlib.category_theory.functor.shift_compatibility

noncomputable theory

/-lemma int.eq_int_of_nat_of_zero_le (a : ℤ) (ha : 0 ≤ a) : ∃ (n : ℕ), a = n :=
begin
  exact int.eq_coe_of_zero_le ha,
end-/

namespace category_theory

open category

variables {C D : Type*} [category C] [category D] (F : C ⥤ D)
  {A G : Type*} [add_monoid A] [add_group G]
  [has_shift C A] [has_shift D A]
  [hCℤ : has_shift C ℤ] [hDℤ : has_shift D ℤ]

namespace functor

variables (F A)

namespace comm_shift

def unit : shift_functor C (0 : A) ⋙ F ≅ F ⋙ shift_functor D (0 : A) :=
shift.compatibility.comm_shift.unit _ _ F

variables {F A}

@[simp]
def change {a b : A} (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (h : a = b) :
  shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b :=
shift.compatibility.comm_shift.change e (eq_to_iso (by subst h))

@[simp]
def add {a b : A} (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b) :=
shift.compatibility.comm_shift.comp e₁ e₂

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

lemma add'_assoc {a b c ab bc abc : A} (hab : a + b = ab) (hbc : b + c = bc)
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
structure comm_shift :=
(iso : Π (a : A), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
(iso_zero : iso 0 = comm_shift.unit F A)
(iso_add : ∀ (a b : A), iso (a + b) = comm_shift.add (iso a) (iso b))

namespace comm_shift

variables {F A}

lemma iso_add_eq_of_iso_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (ha : e₁.iso a = e₂.iso a) (hb : e₁.iso b = e₂.iso b) :
  e₁.iso (a + b) = e₂.iso (a + b) :=
by rw [e₁.iso_add, e₂.iso_add, ha, hb]

lemma iso_eq_of_iso_add_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (hb : e₁.iso b = e₂.iso b) (hab : e₁.iso (a + b) = e₂.iso (a+b))
  [is_equivalence (shift_functor D b)] : e₁.iso a = e₂.iso a :=
(comm_shift.add_bijective (e₁.iso b) a).1
  (by { dsimp only, rw [← e₁.iso_add, hb, ← e₂.iso_add, hab], })

include hCℤ hDℤ

@[ext]
lemma eq_of_iso_one_eq (e₁ e₂ : F.comm_shift ℤ)
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

lemma iso_ℕ_add_one (n : ℕ) : iso_ℕ e (n+1) = add (iso_ℕ e n) e :=
begin
  cases n,
  { unfold iso_ℕ,
    simp only [comm_shift.zero_add, change, eq_to_iso_refl, shift.compatibility.comm_shift.change_refl], },
  { unfold iso_ℕ, },
end

def iso_ℤ : Π (n : ℤ), shift_functor C (n : ℤ) ⋙ F ≅ F ⋙ shift_functor D (n : ℤ)
| (int.of_nat n) := iso_ℕ e n
| -[1+n] := sub' (by { rw int.of_nat_eq_coe, rw int.neg_succ_of_nat_coe', push_cast, linarith, })
  (unit F ℤ) (iso_ℕ e (1+n))

@[simp]
lemma iso_ℤ_zero : iso_ℤ e 0 = unit _ _ := rfl

lemma iso_ℤ_add_neg (n₁ n₂ : ℤ)(h : n₁ + n₂ = 0) (hn₂ : 0 ≤ n₂):
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


end mk_ℤ

end comm_shift

end functor

end category_theory
