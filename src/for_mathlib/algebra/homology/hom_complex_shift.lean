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

variable {n}

lemma δ_right_unshift (i' j j' : ℤ) (hj : j = i + n) (hj' : j' = i' + n) :
  δ j j' (γ'.right_unshift j hj) = ε n • (δ i i' γ').right_unshift j' hj' :=
begin
  conv_rhs { rw ← γ'.right_unshift_shift j hj, },
  rw [(γ'.right_unshift j hj).δ_right_shift n j' i i' hj hj',
    right_unshift_smul, cochain.right_shift_unshift, smul_smul,
    ← ε_add, ε_even _ (even_add_self n), one_smul],
end

@[simps]
def right_shift_equiv (K L : cochain_complex C ℤ) (n i j : ℤ) (h : i = j + n) :
  cochain K L i ≃+ cochain K (L⟦n⟧) j :=
{ to_fun := λ γ, γ.right_shift n j h,
  inv_fun := λ γ', γ'.right_unshift i h,
  left_inv := λ γ, γ.right_shift_unshift _ _ _,
  right_inv := λ γ', γ'.right_unshift_shift _ _,
  map_add' := λ γ₁ γ₂, cochain.right_shift_add γ₁ γ₂ _ _ _, }

end cochain

namespace cocycle

variables {K L : cochain_complex C ℤ} {i : ℤ}
  (γ : cocycle K L i) (n : ℤ) (γ' : cocycle K (L⟦n⟧) i)

def right_shift (j : ℤ) (hj : i = j + n) : cocycle K (L⟦n⟧) j :=
⟨γ.1.right_shift n j hj, begin
  rw [cocycle.mem_iff j (j+1) rfl, γ.1.δ_right_shift n (i+1) j (j+1) hj (by linarith)],
  simp only [subtype.val_eq_coe, δ_eq_zero, cochain.right_shift_zero, smul_zero],
end⟩

variable {n}

def right_unshift (j : ℤ) (hj : j = i + n) : cocycle K L j :=
⟨γ'.1.right_unshift j hj, begin
  rw [cocycle.mem_iff j (j+1) rfl, γ'.1.δ_right_unshift (i+1) j (j+1) hj (by linarith)],
  simp only [subtype.val_eq_coe, δ_eq_zero, cochain.right_unshift_zero, smul_zero],
end⟩

@[simps]
def right_shift_equiv (K L : cochain_complex C ℤ) (n i j : ℤ) (h : i = j + n) :
  cocycle K L i ≃+ cocycle K (L⟦n⟧) j :=
{ to_fun := λ γ, right_shift γ n j h,
  inv_fun := λ γ', right_unshift γ' i h,
  left_inv := λ γ, by { ext1, exact γ.1.right_shift_unshift _ _ _, },
  right_inv := λ γ', by { ext1, exact γ'.1.right_unshift_shift _ _, },
  map_add' := λ γ₁ γ₂, by { ext1, exact cochain.right_shift_add γ₁.1 γ₂.1 _ _ _, }, }

end cocycle

@[simps]
def right_shift_iso (K L : cochain_complex C ℤ) (n : ℤ) :
  (hom_complex K L)⟦n⟧ ≅ hom_complex K (L⟦n⟧) :=
homological_complex.hom.iso_of_components
  (λ i, add_equiv.to_AddCommGroup_iso (cochain.right_shift_equiv K L n (i+n) i rfl))
  (λ i j hij, begin
    ext1 γ,
    simp only [comp_apply],
    dsimp [hom_complex, δ_hom],
    erw homological_complex.shift_functor_obj_d,
    dsimp,
    erw [γ.δ_right_shift n (j+n) i j rfl rfl, cochain.right_shift_smul],
  end)

namespace cochain

variables {K L : cochain_complex C ℤ} {i : ℤ}
  (γ γ₂ : cochain K L i) (n : ℤ) (γ' γ'₂: cochain (K⟦n⟧) L i)

def left_shift (j : ℤ) (hj : j = i + n) : cochain (K⟦n⟧) L j :=
cochain.mk (λ p q hpq,
  ε (n*j + (n*(n-1)/2)) • (K.shift_functor_obj_X_iso n p (p+n) rfl).hom ≫ γ.v (p+n) q (by { dsimp, linarith, }))

lemma left_shift_v (j : ℤ) (hj : j = i + n) (p q : ℤ) (hpq : q = p + j)
  (p' : ℤ) (hp' : p' = p + n) :
  (γ.left_shift n j hj).v p q hpq = ε (n*j + (n*(n-1)/2)) • (K.shift_functor_obj_X_iso n p p' hp').hom ≫
    γ.v p' q (by rw [hpq, hp', hj, add_assoc, add_comm i]) :=
by { subst hp', refl, }

@[simp]
lemma left_shift_zero (j : ℤ) (hj : j = i + n) :
  (0 : cochain K L i).left_shift n j hj = 0 :=
by { dsimp [left_shift], tidy, }

@[simp]
lemma left_shift_smul (j : ℤ) (hj : j = i + n) (a : ℤ) :
  (a • γ).left_shift n j hj = a • γ.left_shift n j hj :=
begin
  ext p q hpq,
  simp only [left_shift_v _ n j hj p q hpq _ rfl, zsmul_v, linear.comp_smul,
    ← mul_smul, mul_comm a],
end

@[simp]
lemma left_shift_add (j : ℤ) (hj : j = i + n) :
  (γ + γ₂).left_shift n j hj = γ.left_shift n j hj + γ₂.left_shift n j hj :=
begin
  ext p q hpq,
  simp only [left_shift_v _ n j hj p q hpq _ rfl, add_v, preadditive.comp_add, smul_add],
end

variable {n}

def left_unshift (j : ℤ) (hj : i = j + n) : cochain K L j :=
cochain.mk (λ p q hpq,
  ε (n*i + (n*(n-1)/2)) • (K.shift_functor_obj_X_iso n (p-n) p (by linarith)).inv ≫
    γ'.v (p-n) q (by { change _ = _ - _ + _, linarith,}))


def left_unshift_v (j : ℤ) (hj : i = j + n) (p q : ℤ) (hpq : q = p + j)
  (p' : ℤ) (hp' : p' = p - n):
  (γ'.left_unshift j hj).v p q hpq =
  ε (n*i + (n*(n-1)/2)) • (K.shift_functor_obj_X_iso n p' p (by rw [hp', sub_add_cancel])).inv ≫
    γ'.v p' q (by rw [hpq, hp', hj, sub_add_add_cancel]) :=
by { subst hp', refl, }

@[simp]
lemma left_unshift_zero (j : ℤ) (hj : i = j + n) :
  (0 : cochain (K⟦n⟧) L i).left_unshift j hj = 0 :=
by { dsimp [left_unshift], tidy, }

@[simp]
lemma left_unshift_smul (j : ℤ) (hj : i = j + n) (a : ℤ) :
  (a • γ').left_unshift j hj = a • γ'.left_unshift j hj :=
begin
  ext p q hpq,
  simp only [left_unshift_v _ j hj p q hpq _ rfl, zsmul_v, linear.smul_comp, linear.comp_smul,
    ← mul_smul, mul_comm a],
end

@[simp]
lemma left_unshift_add (j : ℤ) (hj : i = j + n) :
  (γ' + γ'₂).left_unshift j hj = γ'.left_unshift j hj + γ'₂.left_unshift j hj :=
begin
  ext p q hpq,
  simp only [left_unshift_v _ j hj p q hpq _ rfl, add_v, preadditive.comp_add, smul_add],
end

@[simp]
lemma left_unshift_shift (j : ℤ) (hj : i = j + n) :
  (γ'.left_unshift j hj).left_shift n i hj = γ' :=
begin
  ext p q hpq,
  simp only [cochain.left_shift_v _ n i hj p q hpq _ rfl,
    cochain.left_unshift_v _ j hj (p+n) q (by linarith) p (by linarith),
    ε_add, linear.comp_smul, iso.hom_inv_id_assoc, ← mul_smul],
  nth_rewrite 0 mul_comm (ε (n*i)),
  rw ← mul_assoc,
  nth_rewrite 1 mul_assoc,
  rw [← ε_add, ε_even _ (even_add_self _), mul_one],
  rw [← ε_add, ε_even _ (even_add_self _), one_smul],
end

variable (n)

@[simp]
lemma left_shift_unshift (j : ℤ) (hj : j = i + n) :
  (γ.left_shift n j hj).left_unshift i hj = γ :=
begin
  ext p q hpq,
  simp only [cochain.left_unshift_v _ i hj p q hpq _ rfl,
    cochain.left_shift_v _ n j hj (p-n) q (by linarith) p (by linarith)],
  simp only [homological_complex.shift_functor_obj_X_iso, ε_add, linear.comp_smul,
    homological_complex.X_iso_of_eq_inv_hom_assoc,
    homological_complex.X_iso_of_eq_refl, iso.refl_hom, category.id_comp, ← mul_smul],
  nth_rewrite 0 mul_comm (ε (n*j)),
  rw ← mul_assoc,
  nth_rewrite 1 mul_assoc,
  rw [← ε_add, ε_even _ (even_add_self _), mul_one],
  rw [← ε_add, ε_even _ (even_add_self _), one_smul],
end


variable (n)

lemma δ_left_shift (i' j j' : ℤ) (hj : j = i + n) (hj' : j' = i' + n) :
  δ j j' (γ.left_shift n j hj) = ε (n) • (δ i i' γ).left_shift n j' hj' :=
begin
  by_cases h₁ : i+1 = i', swap,
  { have h₂ : j+1 ≠ j' := λ h₃, by { exfalso, apply h₁, linarith, },
    simp only [δ_shape _ _ h₁, δ_shape _ _ h₂, left_shift_zero, smul_zero], },
  { have h₂ : j' = j+1 := by linarith,
    substs h₁ h₂,
    ext p q hpq,
    rw δ_v j _ rfl _ p q hpq (p+j) (p+1) (by linarith) rfl,
    rw γ.left_shift_v n j hj p _ rfl _ rfl,
    rw γ.left_shift_v n j hj (p+1) q (by linarith) _ rfl,
    rw zsmul_v,
    rw left_shift_v _ n (j+1) hj' p q hpq _ rfl,
    rw δ_v i _ rfl _ (p+n) q (by linarith) (p+j) (p+1+n) (by linarith) (by linarith),
    simp only [homological_complex.shift_functor_obj_X_iso, homological_complex.X_iso_of_eq_refl,
      linear.smul_comp, assoc, ε_succ, linear.comp_smul, neg_smul, preadditive.comp_add,
      preadditive.comp_neg, smul_add, zsmul_neg', add_right_inj, neg_inj, ← mul_smul],
    dsimp [iso.refl],
    erw [homological_complex.shift_functor_obj_d],
    dsimp,
    simp only [preadditive.zsmul_comp, ← mul_smul],
    erw [category.id_comp, category.id_comp, category.id_comp],
    congr' 2,
    { simp only [mul_add, ε_add, mul_one, mul_comm _ (ε n)],
      simp only [← mul_assoc, ← ε_add n n, ε_even _ (even_add_self n)],
      ring, },
    { rw [hj],
      simp only [ε_add, neg_mul, mul_neg, neg_inj, mul_add],
      ring_nf, }, },
end

variable {n}

lemma δ_left_unshift (i' j j' : ℤ) (hj : i = j + n) (hj' : i' = j' + n) :
  δ j j' (γ'.left_unshift j hj) = ε n • (δ i i' γ').left_unshift j' hj' :=
begin
  conv_rhs { rw ← γ'.left_unshift_shift j hj, },
  rw [(γ'.left_unshift j hj).δ_left_shift n j' i i' hj hj',
    left_unshift_smul, cochain.left_shift_unshift, smul_smul,
    ← ε_add, ε_even _ (even_add_self n), one_smul],
end

@[simps]
def left_shift_equiv (K L : cochain_complex C ℤ) (n i j : ℤ) (h : j = i + n) :
  cochain K L i ≃+ cochain (K⟦n⟧) L j :=
{ to_fun := λ γ, γ.left_shift n j h,
  inv_fun := λ γ', γ'.left_unshift i h,
  left_inv := λ γ, γ.left_shift_unshift _ _ _,
  right_inv := λ γ', γ'.left_unshift_shift _ _,
  map_add' := λ γ₁ γ₂, cochain.left_shift_add γ₁ γ₂ _ _ _, }

end cochain

namespace cocycle

variables {K L : cochain_complex C ℤ} {i : ℤ}
  (γ : cocycle K L i) (n : ℤ) (γ' : cocycle (K⟦n⟧) L i)

def left_shift (j : ℤ) (hj : j = i + n) : cocycle (K⟦n⟧) L j :=
⟨γ.1.left_shift n j hj, begin
  rw [cocycle.mem_iff j (j+1) rfl, γ.1.δ_left_shift n (i+1) j (j+1) hj (by linarith)],
  simp only [subtype.val_eq_coe, δ_eq_zero, cochain.left_shift_zero, smul_zero],
end⟩

variable {n}

def left_unshift (j : ℤ) (hj : i = j + n) : cocycle K L j :=
⟨γ'.1.left_unshift j hj, begin
  rw [cocycle.mem_iff j (j+1) rfl, γ'.1.δ_left_unshift (i+1) j (j+1) hj (by linarith)],
  simp only [subtype.val_eq_coe, δ_eq_zero, cochain.left_unshift_zero, smul_zero],
end⟩

variables (K L)

@[simps]
def left_shift_equiv (n i j : ℤ) (h : j = i + n) :
  cocycle K L i ≃+ cocycle (K⟦n⟧) L j :=
{ to_fun := λ γ, left_shift γ n j h,
  inv_fun := λ γ', left_unshift γ' i h,
  left_inv := λ γ, by { ext1, exact γ.1.left_shift_unshift _ _ _, },
  right_inv := λ γ', by { ext1, exact γ'.1.left_unshift_shift _ _, },
  map_add' := λ γ₁ γ₂, by { ext1, exact cochain.left_shift_add γ₁.1 γ₂.1 _ _ _, }, }

end cocycle

@[simps]
def left_shift_iso (K L : cochain_complex C ℤ) (n : ℤ) :
  (hom_complex K L) ≅ (hom_complex (K⟦n⟧) L)⟦n⟧ :=
homological_complex.hom.iso_of_components
  (λ i, add_equiv.to_AddCommGroup_iso (cochain.left_shift_equiv K L n i (i+n) rfl))
  (λ i j hij, begin
    ext1 γ,
    simp only [comp_apply],
    dsimp [hom_complex, δ_hom],
    erw [homological_complex.shift_functor_obj_d],
    dsimp,
    rw [γ.δ_left_shift n j (i+n) (j+n) rfl rfl, ← mul_smul, ← ε_add,
      ε_even _ (even_add_self n), one_smul],
  end)

def shift_iso (K L : cochain_complex C ℤ) (n : ℤ) :
  hom_complex K L ≅ hom_complex (K⟦n⟧) (L⟦n⟧) :=
left_shift_iso K L n ≪≫ right_shift_iso (K⟦n⟧) L n

lemma δ_shift_iso_hom_f {K L : cochain_complex C ℤ} (n i j : ℤ) (γ : cochain K L i) :
  δ i j ((shift_iso K L n).hom.f i γ) = (shift_iso K L n).hom.f j (δ i j γ) :=
congr_hom (((shift_iso K L n).hom.comm i j)) γ

lemma mul_pred_div_two_of_even (k : ℤ) : ((k+k)* ((k+k)-1))/2 = k*(2*k-1) :=
by simp only [show k+k = 2*k, by ring, mul_assoc, int.mul_div_cancel_left, ne.def, bit0_eq_zero,
  one_ne_zero, not_false_iff]

lemma mul_succ_div_two_of_even (k : ℤ) : ((k+k)* (k+k+1))/2 = k*(2*k+1) :=
by simp only [show k+k = 2*k, by ring, mul_assoc, int.mul_div_cancel_left,
  int.mul_div_cancel_left, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff]

lemma mul_pred_div_two_of_odd (k : ℤ) : ((2*k+1)* ((2*k+1)-1))/2 = k*(2*k+1) :=
by simp only [add_tsub_cancel_right, mul_comm _ (2*k), mul_assoc,
  int.mul_div_cancel_left, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff]

lemma mul_succ_div_two_of_odd (k : ℤ) : ((2*k+1)* ((2*k+1)+1))/2 = (k+1)*(2*k+1) :=
by simp only [mul_comm (2*k+1), show 2*k+1+1 = 2*(k+1), by ring, mul_assoc,
  int.mul_div_cancel_left, ne.def, bit0_eq_zero, one_ne_zero, not_false_iff]

lemma mul_succ_div_two (n : ℤ) : (n * (n+1))/2 = (n*(n-1))/2 + n :=
begin
  by_cases hn : even n,
  { obtain ⟨k, rfl⟩ := hn,
    rw [mul_pred_div_two_of_even, mul_succ_div_two_of_even],
    ring, },
  { rw ← int.odd_iff_not_even at hn,
    obtain ⟨k, rfl⟩ := hn,
    rw [mul_succ_div_two_of_odd, mul_pred_div_two_of_odd],
    ring, },
end

lemma shift_iso_hom_f_of_hom {K L : cochain_complex C ℤ} (f : K ⟶ L) (n : ℤ) :
  ((shift_iso K L n).hom.f 0) (cochain.of_hom f) = ε ((n * (n+1))/2) • cochain.of_hom (f⟦n⟧') :=
begin
  ext p,
  dsimp only [shift_iso],
  simp only [iso.trans_hom, homological_complex.comp_f, comp_apply,
    left_shift_iso_hom_f_apply, right_shift_iso_hom_f_apply],
  rw cochain.right_shift_v _ n 0 rfl p p (by linarith) (p+n) (by linarith),
  rw cochain.left_shift_v _ n (0+n) rfl p (p+n) (by linarith) _ rfl,
  simp only [zero_add, homological_complex.shift_functor_obj_X_iso,
    homological_complex.X_iso_of_eq_refl, cochain.of_hom_v, linear.smul_comp, assoc],
  dsimp [iso.refl],
  have eq : ε (n * n + n * (n - 1) / 2) = ε (( n * (n+1)/2)),
  { simp only [mul_succ_div_two, ε_add, mul_comm _ (ε n)],
    congr' 1,
    by_cases hn : even n,
    { rw [ε_even _ hn, ε_even],
      obtain ⟨k, rfl⟩ := hn,
      exact ⟨2*k*k, by ring⟩, },
    { rw ← int.odd_iff_not_even at hn,
      rw [ε_odd _ hn, ε_odd],
      obtain ⟨k, rfl⟩ := hn,
      exact ⟨2*k*k+2*k, by ring⟩, }, },
  erw [id_comp, comp_id, eq],
  simpa only [cochain.of_hom_v],
end

end hom_complex

end cochain_complex

open cochain_complex.hom_complex

def homotopy.shift {K L : cochain_complex C ℤ} {f₁ f₂ : K ⟶ L} (h : homotopy f₁ f₂) (n : ℤ) :
  homotopy (f₁⟦n⟧') (f₂⟦n⟧') :=
(cochain_complex.hom_complex.equiv_homotopy _ _).symm begin
  obtain ⟨γ, hγ⟩ := (cochain_complex.hom_complex.equiv_homotopy _ _) h,
  replace hγ := congr_arg ((shift_iso K L n).hom.f 0) hγ.symm,
  simp only [map_add, shift_iso_hom_f_of_hom, ← δ_shift_iso_hom_f] at hγ,
  refine ⟨ε ((n*(n+1)/2)) • (shift_iso K L n).hom.f (-1) γ, _⟩,
  simp only [δ_zsmul, eq_sub_of_add_eq hγ, zsmul_sub, ← mul_smul, ← ε_add,
    ε_even _ (even_add_self _), one_smul, sub_add_cancel],
end

namespace homotopy_category

noncomputable instance : has_shift (homotopy_category C (complex_shape.up ℤ)) ℤ :=
quotient.shift (λ n K L f₁ f₂, by { rintro ⟨h⟩, exact ⟨h.shift n⟩, })

lemma quotient_map_shift {K L : cochain_complex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  (homotopy_category.quotient _ _).map (φ⟦n⟧') = ((homotopy_category.quotient _ _).map φ)⟦n⟧' := rfl

end homotopy_category
