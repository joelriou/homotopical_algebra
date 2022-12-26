import for_mathlib.category_theory.abelian.extensions
import for_mathlib.algebra.homology.double

noncomputable theory

open category_theory category_theory.limits category_theory.category derived_category

namespace homological_complex

variables {C ι : Type*} [category C] [has_zero_morphisms C] [has_zero_object C]
  (c : complex_shape ι) (n : ι) [decidable_eq ι]

end homological_complex

variables {C : Type*} [category C] [abelian C]

@[simps]
def category_theory.short_complex.short_exact.extension
  {S : short_complex C} (ex : S.short_exact) :
  category_theory.abelian.extension S.X₃ S.X₁ :=
{ X := S.X₂,
  i := S.f,
  p := S.g,
  w := S.zero,
  ex := begin
    refine (short_complex.short_exact.iff_of_iso _).1 ex,
    exact (short_complex.mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)),
  end, }

instance category_theory.preadditive.is_iso_neg {C : Type*} [category C] [preadditive C]
  {X Y : C} (f : X ⟶ Y) [is_iso f] : is_iso (-f) :=
by simpa only [iso.trans_hom, preadditive.mul_iso_hom, units.coe_neg_one, iso.refl_hom,
  neg_smul, one_zsmul, as_iso_hom, preadditive.neg_comp, id_comp]
  using is_iso.of_iso ((preadditive.mul_iso (-1 : units ℤ) (iso.refl X)).trans (as_iso f))

@[simp]
lemma category_theory.preadditive.neg_inv {C : Type*} [category C] [preadditive C]
  {X Y : C} (f : X ⟶ Y) [is_iso f] : inv (-f) = - inv f :=
by rw [← cancel_mono (-f), is_iso.inv_hom_id, preadditive.neg_comp,
  preadditive.comp_neg, neg_neg, is_iso.inv_hom_id]

open category_theory category_theory.limits category_theory.category derived_category

namespace category_theory.abelian

namespace extension

variables {A B : C} (e : extension A B)

def σ := cochain_complex.double.σ (neg_add_self 1) e.w
def ι := cochain_complex.double.ι (neg_add_self 1) e.p
def σ' := cochain_complex.double.σ' (neg_add_self 1) e.w
def π := cochain_complex.double.π (neg_add_self 1) e.i

def homotopy_πσ'_σι : homotopy (e.π ≫ e.σ') (-e.σ ≫ e.ι)  :=
cochain_complex.double.homotopy_πσ'_σι (neg_add_self 1) e.w

instance : quasi_iso e.σ :=
cochain_complex.double.quasi_iso_σ (neg_add_self 1) e.w e.ex

instance : quasi_iso e.σ' :=
cochain_complex.double.quasi_iso_σ' (neg_add_self 1) e.w e.ex

def δ' : (single_functor C 0).obj A ⟶ (single_functor C (-1)).obj B :=
-inv (Q.map e.σ) ≫ Q.map e.π

lemma δ'_eq : e.δ' = -inv (Q.map e.σ) ≫ Q.map e.π := rfl

lemma δ'_eq' : e.δ' = Q.map e.ι ≫ inv (Q.map e.σ') :=
by simp only [δ', ← cancel_epi (Q.map e.σ), ← cancel_mono (Q.map e.σ'), assoc,
  is_iso.hom_inv_id_assoc, preadditive.comp_neg, preadditive.neg_comp, is_iso.inv_hom_id,
  comp_id, ← Q.map_comp, derived_category.Q_map_eq_of_homotopy _ _ e.homotopy_πσ'_σι,
  functor.map_neg, neg_neg]

lemma δ_eq'' : e.δ' = (short_complex.short_exact.extension e.ex).δ' := rfl

def δ : (single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦(1 : ℤ)⟧ :=
e.δ' ≫ (single_functor_shift_iso C 0 1 (-1) (neg_add_self 1)).inv.app B

def triangle : pretriangulated.triangle (derived_category C) :=
pretriangulated.triangle.mk ((single_functor C 0).map e.i) ((single_functor C 0).map e.p) e.δ

@[simps]
def single_short_complex : short_complex (cochain_complex C ℤ) :=
short_complex.mk ((homological_complex.single C _ 0).map e.i)
  ((homological_complex.single C _ 0).map e.p)
  (by rw [← functor.map_comp, e.w, functor.map_zero])

lemma single_short_complex_short_exact : e.single_short_complex.short_exact :=
short_complex.short_exact.map_of_exact e.ex (homological_complex.single C (complex_shape.up ℤ) 0)

def iso_mapping_cone := cochain_complex.double_iso_mapping_cone e.i

lemma compatibility_mapping_cone_σ : e.σ = (cochain_complex.double_iso_mapping_cone e.i).hom ≫
  cochain_complex.from_mapping_cone_of_ses e.single_short_complex_short_exact :=
begin
  refine cochain_complex.from_double_ext (neg_add_self 1) _ _ _ _,
  { dsimp,
    simp only [σ, cochain_complex.from_mapping_cone_of_ses, single_short_complex_g,
      cochain_complex.double.σ_f₁, id_comp, cochain_complex.double.desc.f₁, assoc,
      zero_eq_neg, preadditive.is_iso.comp_left_eq_zero],
    erw [cochain_complex.mapping_cone.inl_desc_v, cochain_complex.hom_complex.cochain.zero_v,
      comp_zero], },
  { dsimp,
    simp only [σ, cochain_complex.from_mapping_cone_of_ses, single_short_complex_g,
      cochain_complex.double.σ_f₂, homological_complex.single_obj_X_self_inv,
      eq_to_hom_refl, comp_id, id_comp, cochain_complex.double.desc.f₂, assoc],
    erw [cochain_complex.mapping_cone.inr_desc_f],
    dsimp,
    simp only [eq_self_iff_true, comp_id, id_comp, if_true], },
end

open cochain_complex.hom_complex

lemma compatibility_mapping_cone_π :
  e.π = -(cochain_complex.double_iso_mapping_cone e.i).hom ≫
  cochain_complex.mapping_cone.δ ((homological_complex.single C _ 0).map e.i) ≫
  (cochain_complex.single_shift_iso C 0 1 (-1) (neg_add_self 1).symm).hom.app B :=
begin
  refine cochain_complex.to_single_ext _ _ (-1) _,
  simp only [π, cochain_complex.mapping_cone.δ, cochain_complex.double.π_f, eq_to_hom_refl,
    cochain_complex.double.desc.f₁, comp_id, homological_complex.single_obj_X_self_inv,
    id_comp, cochain_complex.double_iso_mapping_cone_hom, homological_complex.neg_f_apply,
    homological_complex.comp_f, cochain_complex.double.desc_f,
    cochain_complex.hom_complex.cocycle.hom_of_f,
    cochain_complex.hom_complex.cocycle.right_shift_coe,
    cochain_complex.mapping_cone.δ_as_cocycle_coe, assoc,
    cochain_complex.hom_complex.cochain.right_shift_v _ 1 0
      (zero_add 1).symm (-1) (-1) (by linarith) 0 (neg_add_self 1).symm, cochain.neg_v,
    preadditive.neg_comp, preadditive.comp_neg, neg_neg],
  erw cochain_complex.mapping_cone.inl_fst_assoc,
  dsimp [cochain_complex.double.X_iso₁, homological_complex.X_iso_of_eq, iso.refl,
    cochain_complex.single_shift_iso, cochain_complex.single_shift_iso_app],
  simp only [cochain_complex.lift_single_f, id_comp],
  erw [id_comp, id_comp],
  refl,
end

lemma δ_eq_triangle_of_ses_δ :
  e.δ = triangle_of_ses_δ e.single_short_complex_short_exact :=
begin
  dsimp [triangle_of_ses_δ, δ, δ', mapping_cone_triangle],
  simp only [← cancel_epi (Q.map (cochain_complex.from_mapping_cone_of_ses
    e.single_short_complex_short_exact)), is_iso.hom_inv_id_assoc,
    ← Q.map (cochain_complex.double_iso_mapping_cone e.i).hom,
    preadditive.neg_comp, preadditive.comp_neg,
    e.compatibility_mapping_cone_σ, functor.map_neg, Q.map_comp, preadditive.neg_inv,
    is_iso.inv_comp, neg_neg, assoc,
    ← cancel_epi (Q.map (cochain_complex.double_iso_mapping_cone e.i).hom), mapping_cone_δ,
    ← cancel_mono ((comm_shift_Q C 1).inv.app ((homological_complex.single C _ 0).obj B)),
    iso.hom_inv_id_app, single_functor_shift_iso_inv_app, compatibility_mapping_cone_π],
    erw [← Q.map_comp, iso.hom_inv_id_app, Q.map_id],
    refl,
end

lemma triangle_iso : e.triangle ≅ triangle_of_ses e.single_short_complex_short_exact :=
pretriangulated.triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)
  (by { dsimp [triangle], simp only [category_theory.functor.map_id, comp_id,
    id_comp, δ_eq_triangle_of_ses_δ], })

lemma triangle_distinguished : e.triangle ∈ dist_triang (derived_category C) :=
pretriangulated.isomorphic_distinguished _ (triangle_of_ses_dist _) _ e.triangle_iso

lemma iso_of_triangle_map (e₁ e₂ : extension A B)
  (φ : e₁.triangle ⟶ e₂.triangle) (hφ₁ : φ.hom₁ = 𝟙 _) (hφ₃ : φ.hom₃ = 𝟙 _) : e₁ ≅ e₂ :=
as_iso begin
  have eq₁ := φ.comm₁,
  have eq₂ := φ.comm₂,
  dsimp only [triangle] at eq₁ eq₂,
  simp only [pretriangulated.triangle.mk_mor₁, hφ₁] at eq₁,
  erw id_comp at eq₁,
  simp only [pretriangulated.triangle.mk_mor₂, hφ₃] at eq₂,
  erw comp_id at eq₂,
  refine extension.hom.mk' ((single_functor C 0).preimage φ.hom₂) _ _,
  { apply (single_functor C 0).map_injective,
    rw [functor.map_comp, functor.image_preimage, eq₁], },
  { apply (single_functor C 0).map_injective,
    rw [functor.map_comp, functor.image_preimage, eq₂], },
end

section naturality

variables {S₁ S₂ : short_complex C} (φ : S₁ ⟶ S₂)
  (ex₁ : S₁.short_exact) (ex₂ : S₂.short_exact)

include φ ex₁ ex₂

@[reassoc]
lemma σ_naturality :
  ex₁.extension.σ ≫ (homological_complex.single C _ 0).map φ.τ₃ =
    cochain_complex.double.map (neg_add_self 1) S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
      ex₂.extension.σ :=
begin
  refine cochain_complex.to_single_ext _ _ 0 _,
  { dsimp only [short_complex.short_exact.extension, extension.σ],
    simp only [homological_complex.comp_f, cochain_complex.double.σ_f₂,
      homological_complex.single_obj_X_self_inv, eq_to_hom_refl,
      comp_id, homological_complex.single_map_f_self, homological_complex.single_obj_X_self_hom,
      assoc, cochain_complex.double.map_f₂, iso.inv_hom_id_assoc, iso.cancel_iso_hom_left,
      φ.comm₂₃],
    erw id_comp, },
end

@[reassoc]
lemma π_naturality :
  ex₁.extension.π ≫ (homological_complex.single C _ (-1 : ℤ)).map φ.τ₁ =
    cochain_complex.double.map (neg_add_self 1) S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
    ex₂.extension.π :=
begin
  refine cochain_complex.to_single_ext _ _ (-1) _,
  { dsimp only [short_complex.short_exact.extension, extension.π],
    simp only [homological_complex.comp_f, cochain_complex.double.π_f, eq_to_hom_refl,
      cochain_complex.double.desc.f₁, comp_id, homological_complex.single_map_f_self,
      homological_complex.single_obj_X_self_hom, homological_complex.single_obj_X_self_inv,
      cochain_complex.double.map_f₁, assoc, iso.inv_hom_id, iso.cancel_iso_hom_left],
    apply id_comp, },
end

@[reassoc]
lemma δ'_naturality :
  ex₁.extension.δ' ≫ (single_functor C (-1)).map φ.τ₁ =
    (single_functor C 0).map φ.τ₃ ≫ ex₂.extension.δ' :=
begin
  dsimp only [extension.δ', single_functor, functor.comp_map],
  have hσ := Q.congr_map (σ_naturality φ ex₁ ex₂),
  have hπ := Q.congr_map (π_naturality φ ex₁ ex₂),
  simp only [Q.map_comp, ← cancel_mono (inv (Q.map ex₂.extension.σ)), assoc,
    is_iso.hom_inv_id, comp_id] at hσ,
  simp only [Q.map_comp] at hπ,
  simp only [← cancel_epi (Q.map ex₁.extension.σ), assoc, is_iso.hom_inv_id_assoc,
    hπ, ← hσ, preadditive.comp_neg, preadditive.neg_comp],
end

@[reassoc]
lemma δ_naturality :
  ex₁.extension.δ ≫ ((single_functor C 0).map φ.τ₁)⟦1⟧' =
    (single_functor C 0).map φ.τ₃ ≫ ex₂.extension.δ :=
begin
  dsimp only [extension.triangle, pretriangulated.triangle.mk, extension.δ],
  simpa only [← δ'_naturality_assoc φ ex₁ ex₂, assoc, nat_trans.naturality],
end

@[simps]
def triangle_map : ex₁.extension.triangle ⟶ ex₂.extension.triangle :=
{ hom₁ := (single_functor C 0).map φ.τ₁,
  hom₂ := (single_functor C 0).map φ.τ₂,
  hom₃ := (single_functor C 0).map φ.τ₃,
  comm₁' := by simpa only [functor.map_comp] using (single_functor C 0).congr_map φ.comm₁₂.symm,
  comm₂' := by simpa only [functor.map_comp] using (single_functor C 0).congr_map φ.comm₂₃.symm,
  comm₃' := δ_naturality φ ex₁ ex₂, }

end naturality

end extension

namespace extensions

variables {A B : C} (e : extension A B)

def δ : extensions A B → ((single_functor C 0).obj A ⟶
  ((single_functor C 0).obj B)⟦(1 : ℤ)⟧) :=
quot.lift extension.δ begin
  rintros E₁ E₂ ⟨e⟩,
  have eq := extension.δ_naturality
    ((extension.to_short_exact_sequence_functor A B).map e.hom) E₁.ex E₂.ex,
  dsimp at eq,
  simpa only [category_theory.functor.map_id, id_comp, comp_id] using eq,
end

variable (C)

@[simps]
def δ_nat_trans : extensions_functor C ⟶
  ((single_functor C 0).op ⋙ (single_functor C 0 ⋙ shift_functor _ (1 : ℤ) ⋙ yoneda).flip).flip :=
{ app := λ B,
  { app := λ A, extensions.δ,
    naturality' := λ A₁ A₂ π, begin
      ext e,
      obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' e,
      have eq := extension.δ_naturality (E.pull_short_complex π.unop)
        ((E.pull π.unop).ex) E.ex,
      dsimp at eq,
      simpa only [category_theory.functor.map_id, comp_id] using eq,
    end, },
  naturality' := begin
    rintro B₁ B₂ ι,
    ext A e,
    obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' e,
    have eq := extension.δ_naturality (E.push_short_complex ι) E.ex (E.push ι).ex,
    dsimp at eq,
    simpa only [category_theory.functor.map_id, id_comp] using eq.symm,
  end, }

variables {C}

lemma δ_nat_trans_surjective'
  (φ : (single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦(1 : ℤ)⟧) :
  ∃ (e : extension A B), φ = e.δ :=
begin
  obtain ⟨φ, rfl⟩ : ∃ (φ' : (single_functor C 0).obj A ⟶ (single_functor C (-1)).obj B),
    φ = φ' ≫ (single_functor_shift_iso C 0 1 (-1) (neg_add_self 1)).inv.app B,
  { refine ⟨φ ≫ (single_functor_shift_iso C 0 1 (-1) (neg_add_self 1)).hom.app B, _⟩,
    simp only [assoc, iso.hom_inv_id_app],
    erw comp_id, },
  suffices : ∃ (E' A' : C) (f' : A ⟶ A') (i' : B ⟶ E') (p' : E' ⟶ A') (w : i' ≫ p' = 0)
    (ex : (short_complex.mk _ _ w).short_exact),
      φ ≫ Q.map ex.extension.σ' = (single_functor C 0).map f' ≫ Q.map ex.extension.ι,
  { obtain ⟨E', A', f', i', p', w, ex, z⟩ := this,
    refine ⟨ex.extension.pull f', _⟩,
    have eq := extension.δ_naturality (ex.extension.pull_short_complex f')
      (ex.extension.pull f').ex ex.extension.ex,
    simp only [extension.pull_short_complex, category_theory.functor.map_id, comp_id] at eq,
    refine trans _ eq.symm,
    dsimp only [extension.δ],
    rw ← assoc,
    congr' 1,
    erw [extension.δ'_eq', ← cancel_mono (Q.map ex.extension.σ'), assoc, assoc, is_iso.inv_hom_id,
      comp_id],
    exact z, },
  haveI : cochain_complex.is_strictly_le ((homological_complex.single C
    (complex_shape.up ℤ) (-1)).obj B) 0 :=
      cochain_complex.is_strictly_le_of_le _ (-1) 0 (by linarith),
  obtain ⟨E', A', p', f, s, hs, eq⟩ : ∃ (B' E' : C) (i' : B' ⟶ E')
   (f : (homological_complex.single C _ 0).obj A ⟶ cochain_complex.double (neg_add_self 1) i')
   (s : (homological_complex.single C _ (-1)).obj B ⟶ cochain_complex.double (neg_add_self 1) i')
   (hs : quasi_iso s), by { haveI := hs, exact φ = Q.map f ≫ inv (Q.map s), },
  { obtain ⟨L', L'_le, L'_ge, f, s, hs, hφ⟩ :=
      left_factorisation_of_is_strictly_le_of_is_strictly_ge φ 0 (-1),
    haveI := L'_le,
    obtain ⟨E', A', p', ⟨e⟩⟩ := cochain_complex.exists_iso_double (neg_add_self 1) L',
    refine ⟨E', A', p', f ≫ e.hom, s ≫ e.hom, infer_instance, _⟩,
    simp only [hφ, Q.map_comp, is_iso.inv_comp, assoc, is_iso.hom_inv_id_assoc], },
  obtain ⟨f', rfl⟩ := cochain_complex.eq_single_to_double' f,
  obtain ⟨i', w, hs'⟩ := cochain_complex.eq_single_to_double s,
  refine ⟨E', A', f', i', p', w, _, _⟩,
  { simpa only [hs', cochain_complex.single_to_double_quasi_iso_iff] using hs, },
  { dsimp only [single_functor, functor.comp_map],
    rw ← Q.map_comp,
    haveI := hs,
    simp only [← cancel_mono (Q.map s), assoc, is_iso.inv_hom_id, comp_id, hs'] at eq,
    convert eq,
    refine cochain_complex.from_single_ext _ _ 0 _,
    dsimp [short_complex.short_exact.extension, extension.ι],
    simp only [eq_self_iff_true, comp_id, id_comp, if_true, cochain_complex.double.lift.f₂,
      cochain_complex.desc_single_f],
    erw id_comp, },
end

lemma _root_.category_theory.abelian.extension.δ_eq_iff (e₁ e₂ : extension A B) :
  (e₁.δ = e₂.δ) ↔ nonempty (e₁ ≅ e₂) :=
begin
  split,
  { intro h,
    obtain ⟨β, hβ₁, hβ₂⟩ := pretriangulated.complete_distinguished_triangle_morphism₂ _ _
      e₁.triangle_distinguished e₂.triangle_distinguished (𝟙 _) (𝟙 _)
      (by simpa only [category_theory.functor.map_id, comp_id, id_comp] using h),
    let γ : e₁.triangle ⟶ e₂.triangle :=
    { hom₁ := 𝟙 _,
      hom₂ := β,
      hom₃ := 𝟙 _, },
    exact ⟨extension.iso_of_triangle_map e₁ e₂ γ rfl rfl⟩, },
  { rintro ⟨h⟩,
    change extensions.δ (quot.mk _ e₁) = extensions.δ (quot.mk _ e₂),
    congr' 1,
    exact quot.sound ⟨h⟩, },
end

variables (A B)

lemma δ_nat_trans_bijective :
  function.bijective (@extensions.δ _ _ _ A B) :=
begin
  split,
  { rintros ⟨e₁⟩ ⟨e₂⟩ (h : e₁.δ = e₂.δ),
    rw extension.δ_eq_iff at h,
    exact quot.sound h, },
  { intro φ,
    obtain ⟨e, rfl⟩ := δ_nat_trans_surjective' φ,
    exact ⟨quotient.mk' e, rfl⟩, },
end

instance : is_iso (δ_nat_trans C) :=
begin
  haveI : ∀ (A : C), is_iso ((δ_nat_trans C).app A),
  { intro A,
    haveI : ∀ (B : Cᵒᵖ), is_iso (((δ_nat_trans C).app A).app B),
    { intro B,
      rw is_iso_iff_bijective,
      apply δ_nat_trans_bijective, },
    apply nat_iso.is_iso_of_is_iso_app, },
  apply nat_iso.is_iso_of_is_iso_app,
end

variable (C)

@[simps]
def δ_nat_iso := as_iso (δ_nat_trans C)

end extensions

namespace extension

variables (A B : C)

@[simp]
lemma trivial.δ : (trivial A B).δ = 0 :=
begin
  haveI : is_split_epi (abelian.extension.trivial A B).triangle.mor₂ := is_split_epi.mk'
  { section_ := Q.map ((homological_complex.single _ _ _).map biprod.inr),
    id' := begin
      erw [← functor.map_comp, ← functor.map_comp, biprod.inr_snd,
        category_theory.functor.map_id, category_theory.functor.map_id],
      refl,
    end, },
  simpa only [← cancel_epi (abelian.extension.trivial A B).triangle.mor₂, comp_zero]
    using pretriangulated.triangle.comp_zero₂₃ _ (trivial A B).triangle_distinguished,
end


variables {A B}

lemma δ_eq_zero_iff (e : extension A B) : e.δ = 0 ↔ nonempty (e ≅ trivial A B) :=
by simp only [← extension.δ_eq_iff, trivial.δ]

lemma δ_neq_zero_iff (e : extension A B) : e.δ ≠ 0 ↔ is_empty (e ≅ trivial A B) :=
by simpa only [not_nonempty_iff] using e.δ_eq_zero_iff.not

end extension

end category_theory.abelian
