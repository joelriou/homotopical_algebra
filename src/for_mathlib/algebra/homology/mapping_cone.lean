import for_mathlib.algebra.homology.twist_cocycle
import algebra.homology.quasi_iso
import algebra.homology.short_complex.pseudoelements

noncomputable theory
open category_theory category_theory.category category_theory.limits

namespace cochain_complex

variables {C : Type*} [category C]

section preadditive

variables [preadditive C]
  {F G : cochain_complex C ℤ} [∀ p, has_binary_biproduct (F.X (p+1-(0 : ℤ))) (G.X p)]
  (φ : F ⟶ G)

def mapping_cone : cochain_complex C ℤ :=
hom_complex.twist (hom_complex.cocycle.of_hom φ)

def mapping_cone_X_inl (n n' : ℤ) (hnn' : n' = n+1) :
  F.X n' ⟶ (mapping_cone φ).X n :=
(hom_complex.twist.inl (hom_complex.cocycle.of_hom φ) (neg_add_self 1)).v _ _ (by linarith)

def mapping_cone_X_inr (n : ℤ) :
  G.X n ⟶ (mapping_cone φ).X n := biprod.inr

def mapping_cone_X_fst (n n' : ℤ) (hnn' : n' = n+1) :
  (mapping_cone φ).X n ⟶ F.X n' :=
(hom_complex.twist.fst (hom_complex.cocycle.of_hom φ) (zero_add 1)).1.v _ _ hnn'

def mapping_cone_X_snd (n : ℤ) :
  (mapping_cone φ).X n ⟶ G.X n := biprod.snd

@[simp, reassoc]
def mapping_cone_X_inl_fst (n n' : ℤ) (hnn' : n' = n+1) :
  mapping_cone_X_inl φ n n' hnn' ≫ mapping_cone_X_fst φ n n' hnn' = 𝟙 _ :=
begin
  have h : n' = n+1-0 := by linarith,
  subst h,
  dsimp [mapping_cone_X_inl, mapping_cone_X_fst, hom_complex.twist.inl,
    hom_complex.twist.fst],
  simp only [hom_complex.cochain.of_hom_v, homological_complex.id_f, id_comp, comp_id, biprod.inl_fst],
end

@[simp, reassoc]
lemma mapping_cone_X_inl_snd (n n' : ℤ) (hnn' : n' = n+1) :
  mapping_cone_X_inl φ n n' hnn' ≫ mapping_cone_X_snd φ n = 0 :=
begin
  have h : n' = n+1-0 := by linarith,
  subst h,
  dsimp [mapping_cone_X_inl, mapping_cone_X_snd, hom_complex.twist.inl],
  simp only [hom_complex.cochain.of_hom_v, homological_complex.id_f, id_comp, biprod.inl_snd],
end

@[simp, reassoc]
lemma mapping_cone_X_inr_fst (n n' : ℤ) (hnn' : n' = n+1) :
  mapping_cone_X_inr φ n ≫ mapping_cone_X_fst φ n n' hnn' = 0 :=
begin
  have h : n' = n+1-0 := by linarith,
  subst h,
  dsimp [mapping_cone_X_inr, mapping_cone_X_fst, hom_complex.twist.fst],
  simp only [hom_complex.cochain.of_hom_v, homological_complex.id_f, comp_id, biprod.inr_fst],
end

@[simp, reassoc]
lemma mapping_cone_X_inr_snd (n : ℤ) :
  mapping_cone_X_inr φ n ≫ mapping_cone_X_snd φ n = 𝟙 _ := biprod.inr_snd

def ι_mapping_cone : G ⟶ mapping_cone φ :=
hom_complex.cocycle.hom_of
  (hom_complex.twist.lift_cocycle (hom_complex.cocycle.of_hom φ) 0
    (hom_complex.cocycle.of_hom (𝟙 G)) (add_comm 0 1)
    (show (-1 : ℤ) + 1 = 0, by linarith) 1 (zero_add 1) (by simp))

@[reassoc]
def mapping_cone_X_inl_d (n n' n'' : ℤ) (hnn' : n' = n+1) (hnn'' : n'' = n'+1) :
  mapping_cone_X_inl φ n n' hnn' ≫ (mapping_cone φ).d n n' =
    φ.f n' ≫ mapping_cone_X_inr φ n' - F.d n' n'' ≫ mapping_cone_X_inl φ _ _ hnn'' :=
begin
  have h : n' = n+1-0 := by linarith,
  subst h,
  dsimp only [mapping_cone_X_inl, mapping_cone_X_inr, mapping_cone,
    hom_complex.twist.inl],
  tidy,
end

@[simp, reassoc]
def mapping_cone_X_inr_d (n n' : ℤ) :
  mapping_cone_X_inr φ n ≫ (mapping_cone φ).d n n' =
    G.d n n' ≫ mapping_cone_X_inr φ n' :=
begin
  dsimp [mapping_cone_X_inr, mapping_cone],
  tidy,
end

example : ℕ := 42
lemma mapping_cone_X_id (n n' : ℤ) (hnn' : n' = n+1) :
  mapping_cone_X_fst φ n n' hnn' ≫ mapping_cone_X_inl φ n n' hnn'
    + mapping_cone_X_snd φ n ≫ mapping_cone_X_inr φ n = 𝟙 _ :=
begin
  have h : n' = n+1-0 := by linarith,
  subst h,
  dsimp [mapping_cone_X_fst, mapping_cone_X_snd, hom_complex.twist.fst,
    mapping_cone_X_inl, mapping_cone_X_inr, hom_complex.twist.inl,
    mapping_cone],
  tidy,
end

variable {φ}

def to_mapping_cone_decomposition {A : C} {n : ℤ} (f : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  ∃ (x : A ⟶ F.X n') (y : A ⟶ G.X n), f = x ≫ mapping_cone_X_inl φ _ _ h
      + y ≫ mapping_cone_X_inr φ _ :=
begin
  refine ⟨f ≫ mapping_cone_X_fst φ _ _ h, f ≫ mapping_cone_X_snd φ n, _⟩,
  have h := f ≫= mapping_cone_X_id φ _ _ h,
  rw comp_id at h,
  nth_rewrite 0 ← h,
  simp,
end

lemma to_mapping_cone_ext_iff {A : C} {n : ℤ} (f g : A ⟶ (mapping_cone φ).X n)
  (n' : ℤ) (h : n' = n+1) :
  f = g ↔ f ≫ mapping_cone_X_fst φ _ _ h = g ≫ mapping_cone_X_fst φ _ _ h
    ∧ f ≫ mapping_cone_X_snd φ _ = g ≫ mapping_cone_X_snd φ _ :=
begin
  split,
  { intro h,
    rw h,
    tauto, },
  { rintro ⟨h₁, h₂⟩,
    rw [← cancel_mono (𝟙 ((mapping_cone φ).X n))],
    simp only [← mapping_cone_X_id _ _ _ h, preadditive.comp_add,
      reassoc_of h₁, reassoc_of h₂], },
end

end preadditive

section abelian

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
hom_complex.cocycle.hom_of
  (hom_complex.twist.desc_cocycle _ (0 : hom_complex.cochain _ _ (-1))
    (hom_complex.cocycle.of_hom S.g) (by linarith) (add_zero 0).symm
      (by simp only [hom_complex.δ_zero, hom_complex.ε_0, hom_complex.cocycle.of_hom_coe,
        one_zsmul, ← hom_complex.cochain.of_hom_comp, S.zero, hom_complex.cochain.of_hom_zero]))

lemma from_mapping_cone_of_ses_quasi_iso : quasi_iso (from_mapping_cone_of_ses ex) :=
⟨λ n, begin
  rw is_iso_homology_map_iff_short_complex_quasi_iso'
    (from_mapping_cone_of_ses ex) (show (n-1)+1=n, by linarith) rfl,
  change is_iso _,
  rw is_iso_iff_mono_and_epi,
  split,
  { rw short_complex.mono_homology_map_iff,
    dsimp,
    intros A x₂ hxy y₁ hy₁,
    obtain ⟨x, y, rfl⟩ := to_mapping_cone_decomposition x₂ _ rfl,
    simp only [preadditive.add_comp, assoc,
      mapping_cone_X_inl_d, mapping_cone_X_inr_d, mapping_cone_X_inl_d _ _ _ _ _ rfl,
      preadditive.comp_sub] at hxy,
    obtain ⟨hx, hy⟩ := (to_mapping_cone_ext_iff _ _ _ rfl).mp hxy,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone_X_inr_fst,
      comp_zero, mapping_cone_X_inl_fst, comp_id, zero_sub, add_zero, zero_comp, neg_eq_zero] at hx,
    simp only [preadditive.add_comp, preadditive.sub_comp, assoc, mapping_cone_X_inr_snd, comp_id,
      mapping_cone_X_inl_snd, comp_zero, sub_zero, zero_comp] at hy,
    clear hxy,
    sorry, },
  { rw short_complex.epi_homology_map_iff,
    dsimp,
    intros A y₂ hy₂,
    sorry, },
end⟩

end abelian

end cochain_complex
