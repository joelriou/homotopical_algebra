import for_mathlib.algebra.homology.hom_complex
import for_mathlib.algebra.homology.shift

open category_theory category_theory.category category_theory.limits

variables {C : Type*} [category C] [preadditive C]

namespace cochain_complex

namespace hom_complex

namespace cochain

variables {K L : cochain_complex C ℤ} {i : ℤ}
  (γ γ₂ : cochain K L i) (n : ℤ) (γ' γ'₂: cochain K (L⟦n⟧) i)

def right_shift (j : ℤ) (hj : i = j + n) : cochain K (L⟦n⟧) j :=
cochain.mk (λ p q hpq, γ.v p (p+i) rfl ≫
  (L.shift_functor_obj_X_iso n q (p+i) (by linarith)).inv)

lemma right_shift_v (j : ℤ) (hj : i = j + n) (p q : ℤ) (hpq : q = p + j)
  (p' : ℤ) (hp' : p' = p + i) :
  (γ.right_shift n j hj).v p q hpq = γ.v p p' hp' ≫
    (L.shift_functor_obj_X_iso n q p' (by rw [hp', hpq, hj, add_assoc])).inv :=
by { subst hp', refl, }

@[simp]
lemma right_shift_zero (j : ℤ) (hj : i = j + n) :
  (0 : cochain K L i).right_shift n j hj = 0 :=
by { dsimp [right_shift], tidy, }

@[simp]
lemma right_shift_smul (j : ℤ) (hj : i = j + n) (a : ℤ) :
  (a • γ).right_shift n j hj = a • γ.right_shift n j hj :=
begin
  ext p q hpq,
  simp only [right_shift_v _ n j hj p q hpq _ rfl, zsmul_v, linear.smul_comp],
end

@[simp]
lemma right_shift_add (j : ℤ) (hj : i = j + n) :
  (γ + γ₂).right_shift n j hj = γ.right_shift n j hj + γ₂.right_shift n j hj :=
begin
  ext p q hpq,
  simp only [right_shift_v _ n j hj p q hpq _ rfl, add_v, preadditive.add_comp],
end

variable {n}

def right_unshift (j : ℤ) (hj : j = i + n) : cochain K L j :=
cochain.mk (λ p q hpq, γ'.v p (p+i) rfl ≫
  (L.shift_functor_obj_X_iso n (p+i) q (by linarith)).hom)

def right_unshift_v (j : ℤ) (hj : j = i + n) (p q : ℤ) (hpq : q = p + j)
  (p' : ℤ) (hp' : p' = p + i):
  (γ'.right_unshift j hj).v p q hpq = γ'.v p p' hp' ≫
    (L.shift_functor_obj_X_iso n p' q (by rw [hp', hpq, hj, add_assoc])).hom :=
by { subst hp', refl, }

@[simp]
lemma right_unshift_zero (j : ℤ) (hj : j = i + n) :
  (0 : cochain K (L⟦n⟧) i).right_unshift j hj = 0 :=
by { dsimp [right_unshift], tidy, }

@[simp]
lemma right_unshift_smul (j : ℤ) (hj : j = i + n) (a : ℤ) :
  (a • γ').right_unshift j hj = a • γ'.right_unshift j hj :=
begin
  ext p q hpq,
  simp only [right_unshift_v _ j hj p q hpq _ rfl, zsmul_v, linear.smul_comp],
end

@[simp]
lemma right_unshift_add (j : ℤ) (hj : j = i + n) :
  (γ' + γ'₂).right_unshift j hj = γ'.right_unshift j hj + γ'₂.right_unshift j hj :=
begin
  ext p q hpq,
  simp only [right_unshift_v _ j hj p q hpq _ rfl, add_v, preadditive.add_comp],
end

@[simp]
lemma right_unshift_shift (j : ℤ) (hj : j = i + n) :
  (γ'.right_unshift j hj).right_shift n i hj = γ' :=
begin
  ext p q hpq,
  simp only [cochain.right_shift_v _ n i hj p q hpq _ rfl,
    cochain.right_unshift_v _ j hj p (p+j) rfl q hpq,
    homological_complex.shift_functor_obj_X_iso, assoc,
    homological_complex.X_iso_of_eq_hom_inv,
    homological_complex.X_iso_of_eq_refl, iso.refl_hom],
  erw category.comp_id,
end

variable (n)

@[simp]
lemma right_shift_unshift (j : ℤ) (hj : i = j + n) :
  (γ.right_shift n j hj).right_unshift i hj = γ :=
begin
  ext p q hpq,
  simp only [cochain.right_unshift_v _ i hj p q hpq _ rfl,
    cochain.right_shift_v _ n j hj p (p+j) rfl q hpq,
    homological_complex.shift_functor_obj_X_iso, assoc,
    homological_complex.X_iso_of_eq_inv_hom,
    homological_complex.X_iso_of_eq_refl, iso.refl_hom, category.comp_id],
end

lemma δ_right_shift (i' j j' : ℤ) (hj : i = j + n) (hj' : i' = j' + n) :
  δ j j' (γ.right_shift n j hj) = ε n • (δ i i' γ).right_shift n j' hj' :=
begin
  by_cases h₁ : i+1 = i', swap,
  { have h₂ : j+1 ≠ j' := λ h₃, by { exfalso, apply h₁, linarith, },
    simp only [δ_shape _ _ h₁, δ_shape _ _ h₂, right_shift_zero, smul_zero], },
  { have h₂ : j' = j+1 := by linarith,
    substs h₁ h₂,
    ext p q hpq,
    simp only [δ_v j _ rfl _ p q hpq (p+j) (p+1) (by linarith) rfl,
      γ.right_shift_v n j hj p (p+j) rfl (p+j+n) (by linarith),
      γ.right_shift_v n j hj (p+1) q (by linarith) (p+1+i) rfl, zsmul_v,
      right_shift_v _ n (j+1) hj' p q hpq (p+1+i) (by linarith),
      δ_v i _ rfl _ p (p+1+i) (by linarith) (p+j+n) _ (by linarith) rfl,
      homological_complex.shift_functor_obj_X_iso, assoc, preadditive.add_comp,
      homological_complex.d_comp_X_iso_of_eq_inv, linear.smul_comp,
      smul_add, smul_smul, ← ε_add],
    congr' 1,
    { erw [homological_complex.shift_functor_obj_d,
        homological_complex.X_iso_of_eq_refl,
        iso.refl_inv, category.id_comp, linear.comp_smul], },
    { congr' 1,
      rw [ε_eq_iff],
      exact ⟨-n, by linarith⟩, }, },
end

end cochain

@[simps]
def cochain_right_shift_equiv (K L : cochain_complex C ℤ) (n i j : ℤ) (h : i = j + n) :
  cochain K L i ≃+ cochain K (L⟦n⟧) j :=
{ to_fun := λ γ, γ.right_shift n j h,
  inv_fun := λ γ', γ'.right_unshift i h,
  left_inv := λ γ, γ.right_shift_unshift _ _ _,
  right_inv := λ γ', γ'.right_unshift_shift _ _,
  map_add' := λ γ₁ γ₂, cochain.right_shift_add γ₁ γ₂ _ _ _, }

@[simps]
def right_shift_iso (K L : cochain_complex C ℤ) (n : ℤ) :
  (hom_complex K L)⟦n⟧ ≅ hom_complex K (L⟦n⟧) :=
homological_complex.hom.iso_of_components
  (λ i, add_equiv.to_AddCommGroup_iso (cochain_right_shift_equiv K L n (i+n) i rfl))
  (λ i j hij, begin
    ext1 γ,
    simp only [comp_apply],
    dsimp [hom_complex, δ_hom],
    erw homological_complex.shift_functor_obj_d,
    dsimp,
    erw [γ.δ_right_shift n (j+n) i j rfl rfl, cochain.right_shift_smul],
  end)

example : ℕ := 42

#check right_shift_iso_hom_f_apply
end hom_complex

end cochain_complex
