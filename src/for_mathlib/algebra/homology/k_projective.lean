import for_mathlib.algebra.homology.derived_category
import for_mathlib.algebra.homology.trunc
import category_theory.preadditive.projective

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.pretriangulated

open_locale zero_object

def int.truncate (n : ℤ) : ℕ :=
if h : 0 ≤ n
  then (int.eq_coe_of_zero_le h).some
  else 0

lemma int.coe_truncate (n : ℤ) (hn : 0 ≤ n) : (n.truncate : ℤ) = n :=
begin
  dsimp [int.truncate],
  rw dif_pos hn,
  exact (int.eq_coe_of_zero_le hn).some_spec.symm,
end

lemma int.truncate_eq_zero (n : ℤ) (hn : n ≤ 0) : n.truncate = 0 :=
begin
  by_cases n = 0,
  { apply int.coe_nat_inj,
    rw [int.coe_truncate n (by linarith), h, int.coe_nat_zero], },
  { dsimp [int.truncate],
    rw dif_neg,
    intro h',
    apply h,
    linarith, },
end

lemma int.self_le_coe_truncate (n : ℤ) : n ≤ (n.truncate : ℤ) :=
begin
  by_cases 0 ≤ n,
  { rw n.coe_truncate h, },
  { simp only [not_le] at h,
    rw n.truncate_eq_zero (by linarith),
    linarith, },
end

lemma int.truncate_le_of_le {n n' : ℤ} (hnn' : n ≤ n') : n.truncate ≤ n'.truncate :=
begin
  by_cases n ≤ 0,
  { simp only [n.truncate_eq_zero h, zero_le'], },
  { rw [← int.coe_nat_le, int.coe_truncate n, int.coe_truncate n']; linarith, },
end


variables {C : Type*} [category C] [abelian C]

namespace homological_complex

variables {ι : Type*} {c : complex_shape ι} (K L : homological_complex C c)

def acyclic : Prop :=
  ∀ (i : ι), is_zero (K.homology i)

variables {K L}

lemma acyclic.of_iso {K L : homological_complex C c} (e : K ≅ L) (h : K.acyclic) :
  L.acyclic :=
λ i, is_zero.of_iso (h i) ((homology_functor C _ i).map_iso e.symm)

lemma acyclic.iff_of_iso {K L : homological_complex C c} (e : K ≅ L) :
  K.acyclic ↔ L.acyclic :=
⟨acyclic.of_iso e, acyclic.of_iso e.symm⟩

variables (K)
class is_K_projective : Prop :=
(null_homotopic : ∀ ⦃Y : homological_complex C c⦄ (f : K ⟶ Y)
  (hY : acyclic Y), nonempty (homotopy f 0))

variables {K L}

lemma is_K_projective.of_homotopy_equiv [K.is_K_projective] (e : homotopy_equiv K L) :
  L.is_K_projective :=
⟨λ Y f hY, begin
  obtain ⟨h⟩ := is_K_projective.null_homotopic (e.hom ≫ f) hY,
  exact ⟨(homotopy.of_eq (id_comp f).symm).trans
    ((e.homotopy_inv_hom_id.comp_right f).symm.trans
      ((homotopy.of_eq (assoc _ _ _)).trans
        ((h.comp_left e.inv).trans
        (homotopy.of_eq comp_zero))))⟩,
end⟩

lemma is_K_projective.of_iso [K.is_K_projective] (e : K ≅ L) : L.is_K_projective :=
is_K_projective.of_homotopy_equiv (homotopy_equiv.of_iso e)

lemma is_K_projective.iff_of_iso (e : K ≅ L) :
  K.is_K_projective ↔ L.is_K_projective :=
begin
  split,
  { introI, exact is_K_projective.of_iso e, },
  { introI, exact is_K_projective.of_iso e.symm, },
end

lemma is_K_projective.of_is_zero (h : is_zero K) : K.is_K_projective :=
⟨λ Y f hY, begin
  rw h.eq_of_src f 0,
  exact ⟨homotopy.refl _⟩
end⟩

instance zero_is_K_projective : is_K_projective (0 : homological_complex C c) :=
is_K_projective.of_is_zero (limits.is_zero_zero _)

/- TODO : stability by arbitrary direct sums. -/

end homological_complex

namespace homotopy_category

lemma quotient_obj_mem_acyclic_iff (K : cochain_complex C ℤ) :
  (quotient _ _).obj K ∈ (acyclic C) ↔ K.acyclic :=
begin
  let e := λ (n : ℤ), (homotopy_category.homology_factors C _ n).symm.app _ ≪≫
      (homotopy_category.shift_homology_functor_iso C n 0 n (zero_add n)).symm.app
        ((quotient _ _).obj K),
  split,
  { exact λ h n, is_zero.of_iso (h n) (e n), },
  { exact λ h n, is_zero.of_iso (h n) (e n).symm, },
end

end homotopy_category

namespace cochain_complex

open homological_complex

variables (K : cochain_complex C ℤ)

lemma acyclic.iff_shift (r : ℤ) :
  K.acyclic ↔ K⟦r⟧.acyclic :=
begin
  split,
  { intros h n,
    exact is_zero.of_iso (h _)
      ((shift_homology_functor_iso C r n _ rfl).app K), },
  { intros h n,
    exact is_zero.of_iso (h _)
      ((shift_homology_functor_iso C r (n-r) n (by linarith)).symm.app K), },
end

lemma acyclic.shift {K : cochain_complex C ℤ} (h : K.acyclic) (r : ℤ) :
  K⟦r⟧.acyclic := (acyclic.iff_shift K r).1 h

lemma is_K_projective_iff : is_K_projective K ↔
  (homotopy_category.quotient _ _).obj K
    ∈ triangulated.left_orthogonal (homotopy_category.acyclic C) :=
begin
  split,
  { introI,
    rintros ⟨Y⟩ f hY,
    obtain ⟨f, rfl⟩ := (homotopy_category.quotient _ _).map_surjective f,
    rw ← (homotopy_category.quotient C (complex_shape.up ℤ)).map_zero,
    refine homotopy_category.eq_of_homotopy _ _ (is_K_projective.null_homotopic _ _).some,
    erw homotopy_category.quotient_obj_mem_acyclic_iff at hY,
    exact hY, },
  { intro hK,
    refine ⟨λ Y f hY, ⟨homotopy_category.homotopy_of_eq _ _ _⟩⟩,
    simp only [functor.map_zero],
    apply hK,
    simpa only [homotopy_category.quotient_obj_mem_acyclic_iff] using hY, },
end

lemma shift_is_K_projective_iff (K : cochain_complex C ℤ) (r : ℤ) :
  is_K_projective (K⟦r⟧) ↔ is_K_projective K :=
begin
  simp only [is_K_projective_iff],
  erw [set.respects_iso.mem_iff_of_iso (triangulated.left_orthogonal (homotopy_category.acyclic C))
   (((homotopy_category.quotient C (complex_shape.up ℤ)).comm_shift_iso r).app K),
    ← triangulated.is_triangulated_subcategory.shift_iff],
end

end cochain_complex

namespace derived_category

lemma Qh_map_bijective_of_is_K_projective
  (K L : cochain_complex C ℤ) [K.is_K_projective] :
  function.bijective (λ (f : ((homotopy_category.quotient _ _).obj K ⟶
    (homotopy_category.quotient _ _).obj L)), Qh.map f) :=
(triangulated.subcategory.left_orthogonal_bijective_Q_map
  (homotopy_category.acyclic C) _ _
  ((cochain_complex.is_K_projective_iff K).1 infer_instance))

lemma Q_map_surjective_of_is_K_projective
  (K L : cochain_complex C ℤ) [K.is_K_projective] :
  function.surjective (λ (f : K ⟶ L), Q.map f) :=
λ f, begin
  obtain ⟨g, hg⟩ := (Qh_map_bijective_of_is_K_projective K L).2 f,
  dsimp at hg,
  obtain ⟨g, rfl⟩ := (homotopy_category.quotient _ _).map_surjective g,
  exact ⟨g, hg⟩,
end

def homotopy_of_eq_Qh_map_eq_of_is_K_projective
  {K L : cochain_complex C ℤ} [K.is_K_projective] (f₁ f₂ : K ⟶ L)
  (h : Q.map f₁ = Q.map f₂) : homotopy f₁ f₂ :=
homotopy_category.homotopy_of_eq _ _ ((Qh_map_bijective_of_is_K_projective K L).1 h)

end derived_category

namespace cochain_complex

open homological_complex hom_complex

variables (K L : cochain_complex C ℤ)

lemma is_K_projective_iff_hom_complex_acyclic_in_degree_zero :
  is_K_projective K ↔
    ∀ (L : cochain_complex C ℤ) (hL : L.acyclic) (z : cocycle K L 0),
        ∃ (x : cochain K L (-1)), (z : cochain K L 0) = δ (-1) 0 x :=
begin
  split,
  { introI,
    intros L hL z,
    obtain ⟨hf⟩ := is_K_projective.null_homotopic (cocycle.hom_of z) hL,
    exact ⟨cochain.of_homotopy hf, by simp only [δ_cochain_of_homotopy,
      cocycle.cochain_of_hom_hom_of_eq_coe, cochain.of_hom_zero, sub_zero]⟩, },
  { intro hK,
    refine ⟨λ L f hL, _⟩,
    obtain ⟨x, hx⟩ := hK L hL (cocycle.of_hom f),
    simp only [cocycle.of_hom_coe] at hx,
    refine ⟨_⟩,
    equiv_rw hom_complex.equiv_homotopy _ _,
    exact ⟨x, by simpa only [cochain.of_hom_zero, add_zero]⟩, },
end

lemma is_K_projective_iff_hom_complex_acyclic :
  is_K_projective K ↔
    ∀ (L : cochain_complex C ℤ) (hL : L.acyclic)
      (n₀ n₁ : ℤ) (h₀₁ : n₁ = n₀ + 1) (z : cocycle K L n₁),
        ∃ (x : cochain K L n₀), (z : cochain K L n₁) = δ n₀ n₁ x :=
begin
  rw is_K_projective_iff_hom_complex_acyclic_in_degree_zero,
  split,
  { intros hK L hL n₀ n₁ h z,
    obtain ⟨x, hx⟩ := hK (L⟦n₁⟧) (acyclic.shift hL n₁)
      (cocycle.right_shift (ε (n₁) • z) n₁ 0 (zero_add n₁).symm),
    refine ⟨x.right_unshift n₀ (by linarith), _⟩,
    simp only [hom_complex.cochain.δ_right_unshift _ 0 n₀ n₁
      (show n₀ = -1+n₁, by linarith) (zero_add n₁).symm, ← hx,
      cocycle.right_shift_coe, add_subgroup.coe_zsmul, cochain.right_shift_unshift, smul_smul,
      mul_ε_self, one_smul], },
  { intros hK L hL z,
    exact hK L hL (-1) 0 (neg_add_self 1).symm z, },
end

namespace is_K_projective_of_bounded_above_of_projective

variables {K L} (f : K ⟶ L)

@[ext]
structure lift (N : ℤ) :=
(y : cochain K L (-1))
(hy : ∀ (p : ℤ) (hp : N < p), (δ (-1) 0 y).v p p (add_zero p).symm = f.f p)

variable {f}

def lift.of_le {N : ℤ} (l : lift f N) (N' : ℤ) (h : N ≤ N') : lift f N' :=
{ y := l.y,
  hy := λ p hp, l.hy p (by linarith), }

def lift.induction_step {N₁ : ℤ} (l : lift f N₁) (N₀ : ℤ) (eq : N₁ = N₀+1)
  (hK : projective (K.X N₁)) (hL : is_zero (L.homology N₁)) :
  { l' : lift f N₀ //
    ∀ (p q : ℤ) (hpq : q = p + (-1)) (hp : N₁ < p), l'.y.v p q hpq = l.y.v p q hpq } :=
nonempty.some begin
  /- the exactness below should be part of the API of homological_complex :
      is_zero (K.homology j) ↔ (K.sc i j k).exact -/
  have ex : (L.sc N₀ N₁ (N₁+1)).exact := (short_complex.exact_iff_of_iso
    ((short_complex_functor_nat_iso C (complex_shape.up ℤ) eq.symm rfl).app L)).1
      ((short_complex.exact_iff_is_zero_homology _).2 hL),
  obtain ⟨A, π, hπ, x, hx⟩ :=
    ex.pseudo_exact' (f.f N₁ - (δ (-1) 0 l.y).v N₁ N₁ (add_zero N₁).symm)
    begin
      dsimp,
      simp only [preadditive.sub_comp,
        δ_v (-1) 0 _ _ N₁ N₁ (add_zero N₁).symm N₀ _ (by linarith) rfl,
        neg_add_self, ε_0, one_smul, preadditive.add_comp, assoc, L.d_comp_d, comp_zero,
        zero_add, f.comm, ← l.hy (N₁+1) (lt_add_one N₁), preadditive.comp_add, K.d_comp_d_assoc,
        δ_v (-1) 0 _ _ (N₁+1) _ (add_zero _).symm N₁ _ (by linarith) rfl,
        zero_comp, add_zero, sub_self],
    end,
  haveI := hπ,
  dsimp at x hx,
  let φ : K.X N₁ ⟶ L.X N₀ := projective.factor_thru (𝟙 _) π ≫ x,
  have hφ : φ ≫ L.d N₀ N₁ = f.f N₁ - (δ (-1) 0 l.y).v N₁ N₁ (add_zero N₁).symm,
  { simp only [φ, assoc, ← hx, projective.factor_thru_comp_assoc, id_comp], },
  let w : cochain K L (-1) := cochain.mk (λ p q hpq, begin
    by_cases p=N₁,
    { refine eq_to_hom (by rw h) ≫ φ ≫ eq_to_hom (by { congr', linarith, }), },
    { exact 0, },
  end),
  have hw : w.v N₁ N₀ (by linarith) = φ,
  { dsimp [w], simp only [eq_self_iff_true, comp_id, id_comp, if_true], },
  have hw_zero : ∀ (p q : ℤ) (hpq : q = p + (-1))
    (hp : p ≠ N₁), w.v p q hpq = 0,
  { intros p q hpq hp, dsimp [w], rw dif_neg hp, },
  let l' : lift f N₀ :=
  { y := l.y + w,
    hy := λ p hp, begin
      cases (int.add_one_le_iff.mpr hp).lt_or_eq,
      { rw [δ_add, cochain.add_v, l.hy p (by linarith), add_right_eq_self,
          δ_v (-1) 0 (neg_add_self 1).symm _ p p (add_zero p).symm _ _ rfl rfl,
          hw_zero p _ _ (by linarith), hw_zero (p+1) _ _ (by linarith), zero_comp,
          comp_zero, smul_zero, zero_add], },
      { have h' : N₁ = p := by linarith,
        unfreezingI { subst h', },
        simp only [δ_add, cochain.add_v, δ_add, δ_v (-1) 0 (neg_add_self 1).symm w N₁ N₁
          (add_zero N₁).symm N₀ _ (by linarith) rfl, neg_add_self, ε_0, one_smul, hw,
          hw_zero (N₁+1) _ _ (by linarith), comp_zero, add_zero, hφ,
          add_sub_cancel'_right], },
    end, },
  exact ⟨⟨l', λ p q hpq hp, by rw [cochain.add_v, hw_zero p q hpq (by linarith), add_zero]⟩⟩,
end

variables {N₀ : ℤ} (l₀ : lift f N₀) (hK : ∀ (p : ℤ) (hp : p ≤ N₀), projective (K.X p))
  (hL : ∀ (p : ℤ) (hp : p ≤ N₀), is_zero (L.homology p))

include l₀ hK hL

noncomputable
def lift.sequence : Π (k : ℕ), lift f (N₀-k)
| 0 := l₀.of_le _ (by simp only [algebra_map.coe_zero, tsub_zero])
| (k+1) := begin
  refine (lift.induction_step (lift.sequence k) _ _ (hK _ _) (hL _ _)).1,
  { simp only [nat.cast_add, algebra_map.coe_one], ring, },
  all_goals
  { simp only [sub_le_self_iff, nat.cast_nonneg], },
end

lemma lift.sequence_is_eventually_constant {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (p q : ℤ) (hpq : q = p+(-1))
  (hp : N₀ - k₁ < p):
  (lift.sequence l₀ hK hL k₁).y.v p q hpq =
    (lift.sequence l₀ hK hL k₂).y.v p q hpq :=
begin
  have h : ∀ (k₁ k₂ : ℕ) (hk₂ : k₂ = k₁ + 1) (hp : N₀ - k₁ < p),
    (lift.sequence l₀ hK hL k₁).y.v p q hpq = (lift.sequence l₀ hK hL k₂).y.v p q hpq,
  { rintro k₁ _ rfl hp,
    unfold lift.sequence,
    exact (((l₀.sequence hK hL k₁).induction_step _ _ _ _).2 _ _ _ hp).symm, },
  rw le_iff_exists_add at hk,
  obtain ⟨d, rfl⟩ := hk,
  induction d with d hd,
  { rw add_zero, },
  { rw hd,
    apply h,
    { rw [nat.succ_eq_add_one, add_assoc], },
    { simp only [nat.cast_add],
      exact lt_of_le_of_lt
        (by simp only [sub_le_sub_iff_left, le_add_iff_nonneg_right, nat.cast_nonneg]) hp, }, },
end

def lift.limit : cochain K L (-1) :=
cochain.mk (λ p q hpq, begin
  let k : ℕ := int.truncate (N₀+1 -p),
  exact ((lift.sequence l₀ hK hL) k).y.v p q hpq,
end)

lemma lift.δ_limit : δ (-1) 0 (lift.limit l₀ hK hL) = cochain.of_hom f :=
begin
  ext,
  dsimp [lift.limit],
  have ineq₁ := int.self_le_coe_truncate (N₀+1-p),
  have ineq₂ := int.self_le_coe_truncate (N₀+1-(p+1)),
  rw [cochain.of_hom_v, ← (l₀.sequence hK hL (N₀+1-p).truncate).hy p (by linarith)],
  simp only [δ_v (-1) 0 (neg_add_self 1).symm _ p p (add_zero p).symm _ _ rfl rfl,
    cochain.mk_v],
  congr' 3,
  { apply lift.sequence_is_eventually_constant,
    apply int.truncate_le_of_le,
    { linarith, },
    { linarith, }, },
end

def lift.homotopy_zero : homotopy f 0 :=
begin
  equiv_rw equiv_homotopy _ _,
  exact ⟨lift.limit l₀ hK hL,
    by simp only [lift.δ_limit, cochain.of_hom_zero, add_zero]⟩,
end

end is_K_projective_of_bounded_above_of_projective

lemma is_K_projective_of_bounded_above_of_projective
  (K : cochain_complex C ℤ) (n : ℤ) [K.is_strictly_le n]
  [∀ (n : ℤ), projective (K.X n)] : is_K_projective K :=
⟨λ L f hL, begin
  let l : is_K_projective_of_bounded_above_of_projective.lift f n :=
  { y := 0,
    hy := λ p hp, begin
      simp only [δ_zero, cochain.zero_v],
      apply ((is_strictly_le.is_zero K n) p hp).eq_of_src,
    end, },
  exact ⟨is_K_projective_of_bounded_above_of_projective.lift.homotopy_zero l
    (λ p hp, infer_instance) (λ p hp, hL p)⟩,
end⟩

instance (P : C) [projective P] (n n' : ℤ) :
  projective (((single C (complex_shape.up ℤ) n).obj P).X n') :=
begin
  by_cases n' = n,
  { subst h,
    exact projective.of_iso (single_obj_X_self C (complex_shape.up ℤ) _ P).symm
      infer_instance, },
  { dsimp [single],
    rw if_neg h,
    exact projective.zero_projective, },
end

instance (P : C) [projective P] (n : ℤ) :
  is_K_projective ((single C (complex_shape.up ℤ) n).obj P) :=
is_K_projective_of_bounded_above_of_projective _ n

end cochain_complex
