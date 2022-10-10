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

lemma add_bijective {b : A} (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] (a : A) :
  function.bijective (λ (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a),
    add e f) :=
(shift.compatibility.comm_shift.comp_equiv f (discrete.mk a)).bijective

lemma add'_bijective {a b c : A} (h : a + b = c)
  (f : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  function.bijective (λ (e : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a),
    add' h e f) :=
begin
  subst h,
  simpa only [add', eq_to_iso_refl, shift.compatibility.comm_shift.change_refl]
    using add_bijective f a,
end

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

end comm_shift

end functor

end category_theory
