import category_theory.shift
import tactic.linarith

noncomputable theory

namespace category_theory

open category

namespace functor

universes v u

variables {C D : Type*} [category C] [category D] (F : C ⥤ D)
  (A G : Type*) [add_monoid A] [add_group G]
  [has_shift C A] [has_shift D A] [has_shift C G] [has_shift D G]
  [has_shift C ℤ] [has_shift D ℤ]

def comm_shift_iso := Π (a : A), shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a

@[simps]
def comm_shift_iso₀ : shift_functor C (0 : A) ⋙ F ≅ F ⋙ shift_functor D (0 : A) :=
calc shift_functor C (0 : A) ⋙ F ≅ 𝟭 _ ⋙ F : iso_whisker_right (shift_functor_zero C A) _
... ≅ F : left_unitor F
... ≅ F ⋙ 𝟭 _ : (right_unitor F).symm
... ≅ F ⋙ shift_functor D (0 : A) : iso_whisker_left _ (shift_functor_zero D A).symm

variable {A}

@[simps]
def comm_shift_iso_add (a b : A)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b) :
  shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b) :=
calc shift_functor C (a + b) ⋙ F ≅ (shift_functor C a ⋙ shift_functor C b) ⋙ F :
  iso_whisker_right (shift_functor_add C a b) _
... ≅ _ : functor.associator _ _ _
... ≅ _ : iso_whisker_left _ e₂
... ≅ _ : (functor.associator _ _ _).symm
... ≅ _ : iso_whisker_right e₁ _
... ≅ _ : functor.associator _ _ _
... ≅ _ : iso_whisker_left _ (shift_functor_add D a b).symm

@[simps]
def comm_shift_iso_cancel_add (a b : A)
  (e₁ : shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b))
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
  ... ≅ _ : iso_whisker_right (iso_whisker_right (shift_functor_add C a b).symm _) _
  ... ≅ _ : iso_whisker_right e₁ _
  ... ≅ _ : functor.associator _ _ _
  ... ≅ _ : iso_whisker_left _ (iso_whisker_right ((shift_functor_add D a b)) _)
  ... ≅ _ : iso_whisker_left _ (functor.associator _ _ _)
  ... ≅ _ : iso_whisker_left _ (iso_whisker_left _ eq.unit_iso.symm)
  ... ≅ _ : (functor.associator _ _ _).symm
  ... ≅ _ : right_unitor _
end

lemma comm_shift_iso_cancel_add' (a b : A)
  (e₁ : shift_functor C a ⋙ F ≅ F ⋙ shift_functor D a)
  (e₂ : shift_functor C b ⋙ F ≅ F ⋙ shift_functor D b)
  [is_equivalence (shift_functor D b)] :
  e₁ = F.comm_shift_iso_cancel_add a b (F.comm_shift_iso_add a b e₁ e₂) e₂ :=
begin
  ext X,
  dsimp [comm_shift_iso_cancel_add, comm_shift_iso_add],
  simp only [assoc, id_comp, comp_id, functor.map_id,
    ← functor.map_comp],
  apply (shift_functor D b).map_injective,
  sorry,
end

namespace comm_shift_iso

variables {F} {A}

@[simp]
def add (e : comm_shift_iso F A) (a b : A) :
  shift_functor C (a + b) ⋙ F ≅ F ⋙ shift_functor D (a + b) :=
comm_shift_iso_add F a b (e a) (e b)

end comm_shift_iso

variables (F A)

@[ext]
structure comm_shift :=
(iso : comm_shift_iso F A)
(iso_zero : iso 0 = comm_shift_iso₀ F A)
(iso_add : ∀ (a b : A), iso (a + b) = iso.add a b)

namespace comm_shift

variables {F A}

lemma iso_add_eq_of_iso_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (ha : e₁.iso a = e₂.iso a) (hb : e₁.iso b = e₂.iso b) :
  e₁.iso (a + b) = e₂.iso (a + b) :=
by simp only [e₁.iso_add, e₂.iso_add, comm_shift_iso.add, ha, hb]

lemma iso_eq_of_iso_add_eq (e₁ e₂ : F.comm_shift A) (a b : A)
  (hb : e₁.iso b = e₂.iso b) (hab : e₁.iso (a + b) = e₂.iso (a+b))
  [is_equivalence (shift_functor D b)] : e₁.iso a = e₂.iso a :=
begin
  rw F.comm_shift_iso_cancel_add' a b (e₁.iso a) (e₁.iso b),
  rw F.comm_shift_iso_cancel_add' a b (e₂.iso a) (e₂.iso b),
  congr' 1,
  change e₁.iso.add a b = e₂.iso.add a b,
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
  { rw [nat.cast_succ, e₁.iso_add, e₂.iso_add, comm_shift_iso.add, comm_shift_iso.add, hn, h], },
end

end comm_shift

section

namespace comm_shift_iso

variable (e : shift_functor C (1 : ℤ) ⋙ F ≅ F ⋙ shift_functor D (1 : ℤ))

noncomputable def ℕ_mk : Π (n : ℕ), shift_functor C (n : ℤ) ⋙ F ≅ F ⋙ shift_functor D (n : ℤ)
| 0 := F.comm_shift_iso₀ ℤ
| (n+1) := F.comm_shift_iso_add (n : ℤ) 1 (ℕ_mk n) e



end comm_shift_iso

end
--local attribute [instance] endofunctor_monoidal_category

--(comm_shift : shift_functor C (1 : ℤ) ⋙ to_functor ≅ to_functor ⋙ shift_functor D (1 : ℤ)

end functor

end category_theory
