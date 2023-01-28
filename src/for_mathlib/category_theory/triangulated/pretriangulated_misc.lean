import category_theory.triangulated.pretriangulated

noncomputable theory

namespace category_theory

open limits category preadditive
open_locale zero_object

namespace pretriangulated

variables {C : Type*} [category C] [preadditive C] [has_shift C ℤ]

@[simps]
def triangle.mk_iso (T T' : triangle C) (e₁ : T.obj₁ ≅ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂)
  (e₃ : T.obj₃ ≅ T'.obj₃)
  (comm₁ : T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁)
  (comm₂ : T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
  (comm₃ : T.mor₃ ≫ (shift_functor C 1).map e₁.hom = e₃.hom ≫ T'.mor₃) : T ≅ T' :=
{ hom :=
  { hom₁ := e₁.hom,
    hom₂ := e₂.hom,
    hom₃ := e₃.hom,
    comm₁' := comm₁,
    comm₂' := comm₂,
    comm₃' := comm₃, },
  inv :=
  { hom₁ := e₁.inv,
    hom₂ := e₂.inv,
    hom₃ := e₃.inv,
    comm₁' := by rw [← cancel_mono e₂.hom, assoc, e₂.inv_hom_id, comp_id, assoc, comm₁, e₁.inv_hom_id_assoc],
    comm₂' := by { rw [← cancel_mono e₃.hom, assoc, e₃.inv_hom_id, comp_id, assoc, comm₂, e₂.inv_hom_id_assoc], },
    comm₃' := by { rw [← cancel_epi e₃.hom, ← assoc, ← comm₃, assoc, ← functor.map_comp, e₁.hom_inv_id, functor.map_id, comp_id, e₃.hom_inv_id_assoc], }, },
  hom_inv_id' := by { ext; apply iso.hom_inv_id, },
  inv_hom_id' := by { ext; apply iso.inv_hom_id, }, }

@[simp, reassoc]
lemma triangle.hom_inv_id_hom₁ {T T' : triangle C} (e : T ≅ T') :
  e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ :=
by { change (e.hom ≫ e.inv).hom₁ = _, simpa only [e.hom_inv_id], }

@[simp, reassoc]
lemma triangle.inv_hom_id_hom₁ {T T' : triangle C} (e : T ≅ T') :
  e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ :=
by { change (e.inv ≫ e.hom).hom₁ = _, simpa only [e.inv_hom_id], }

@[simp, reassoc]
lemma triangle.hom_inv_id_hom₂ {T T' : triangle C} (e : T ≅ T') :
  e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ :=
by { change (e.hom ≫ e.inv).hom₂ = _, simpa only [e.hom_inv_id], }

@[simp, reassoc]
lemma triangle.inv_hom_id_hom₂ {T T' : triangle C} (e : T ≅ T') :
  e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ :=
by { change (e.inv ≫ e.hom).hom₂ = _, simpa only [e.inv_hom_id], }
@[simp, reassoc]

lemma triangle.hom_inv_id_hom₃ {T T' : triangle C} (e : T ≅ T') :
  e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ :=
by { change (e.hom ≫ e.inv).hom₃ = _, simpa only [e.hom_inv_id], }

@[simp, reassoc]
lemma triangle.inv_hom_id_hom₃ {T T' : triangle C} (e : T ≅ T') :
  e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ :=
by { change (e.inv ≫ e.hom).hom₃ = _, simpa only [e.inv_hom_id], }

lemma triangle.is_iso_of_is_iso_homs {T T' : triangle C} (f : T ⟶ T')
  (h₁ : is_iso f.hom₁) (h₂ : is_iso f.hom₂) (h₃ : is_iso f.hom₃) : is_iso f :=
begin
  haveI := h₁,
  haveI := h₂,
  haveI := h₃,
  convert is_iso.of_iso (triangle.mk_iso T T' (as_iso f.hom₁) (as_iso f.hom₂) (as_iso f.hom₃)
    f.comm₁ f.comm₂ f.comm₃),
  ext; refl,
end

section
variables [∀ (n : ℤ), functor.additive (shift_functor C n)] [has_zero_object C] [pretriangulated C]

@[reassoc]
lemma triangle.comp_zero₁₂ (T : triangle C) (hT : T ∈ dist_triang C) : T.mor₁ ≫ T.mor₂ = 0 :=
begin
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism _ _
    (contractible_distinguished T.obj₁) hT (𝟙 T.obj₁) T.mor₁ rfl,
  dsimp at hc₁,
  rw [← hc₁, zero_comp],
end

@[reassoc]
lemma triangle.comp_zero₂₃ (T : triangle C) (hT : T ∈ dist_triang C) : T.mor₂ ≫ T.mor₃ = 0 :=
triangle.comp_zero₁₂ _ (rot_of_dist_triangle _ _ hT)

@[reassoc]
lemma triangle.comp_zero₃₁ (T : triangle C) (hT : T ∈ dist_triang C) : T.mor₃ ≫ T.mor₁⟦1⟧' = 0 :=
begin
  rw [← neg_inj, ← comp_neg, neg_zero],
  exact triangle.comp_zero₁₂ _ (rot_of_dist_triangle _ _ (rot_of_dist_triangle _ _ hT)),
end

lemma distinguished_cocone_triangle₂ {Z X : C} (h : Z ⟶ X⟦(1 : ℤ)⟧) :
  ∃ (Y : C) (f : X ⟶ Y) (g : Y ⟶ Z), triangle.mk f g h ∈ dist_triang C :=
begin
  obtain ⟨Y', f', g', mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ h,
  let T := triangle.mk h f' g',
  change T ∈ dist_triang C at mem,
  let T' := T.inv_rotate.inv_rotate,
  let e₁ := (shift_functor_comp_shift_functor_neg C (1 : ℤ)).app X,
  let e₂ := (shift_functor_neg_comp_shift_functor C (1 : ℤ)).app ((shift_functor C (1 : ℤ)).obj X),
  let T'' := triangle.mk (e₁.inv ≫ T'.mor₁) T'.mor₂ (T'.mor₃ ≫ e₂.hom),
  let e₃ : T' ≅ T'' := begin
    dsimp only [T', T'', triangle.mk],
    refine triangle.mk_iso _ _ e₁ (iso.refl _) (iso.refl _) _ _ _,
    { dsimp only [iso.refl],
      rw [comp_id, e₁.hom_inv_id_assoc], },
    { dsimp only [iso.refl],
      rw [comp_id, id_comp], },
    { dsimp only [iso.refl],
      rw id_comp,
      congr' 1,
      have h : (shift_functor C 1).map e₁.inv ≫ e₂.hom = 𝟙 _ := shift_equiv_triangle (1 : ℤ) X,
      rw [← cancel_epi ((shift_functor C (1 : ℤ)).map e₁.inv), h, ← functor.map_comp,
        iso.inv_hom_id, functor.map_id], },
  end,
  have eq : h = T'.mor₃ ≫ e₂.hom,
  { dsimp,
    simp only [unit_of_tensor_iso_unit_inv_app, ε_app_obj, discrete.functor_map_id,
      nat_trans.id_app, id_comp, assoc, ε_inv_app_obj, μ_inv_hom_app_assoc],
    erw comp_id, },
  rw eq,
  refine ⟨T''.obj₂, T''.mor₁, T''.mor₂, _⟩,
  exact pretriangulated.isomorphic_distinguished _
    (inv_rot_of_dist_triangle _ _ (inv_rot_of_dist_triangle _ _ mem)) _ e₃.symm,
end

lemma distinguished_cocone_triangle₁ {Y Z : C} (g : Y ⟶ Z) :
  ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦1⟧), triangle.mk f g h ∈ dist_triang C :=
begin
  obtain ⟨X', f', g', mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ g,
  exact ⟨_, _, _, inv_rot_of_dist_triangle _ _ mem⟩,
end

lemma complete_distinguished_triangle_morphism₁ (T₁ T₂ : triangle C)
  (hT₁ : T₁ ∈ dist_triang C) (hT₂ : T₂ ∈ dist_triang C) (b : T₁.obj₂ ⟶ T₂.obj₂)
  (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
  ∃ (a : T₁.obj₁ ⟶ T₂.obj₁), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
    T₁.mor₃ ≫ (shift_functor C (1 : ℤ)).map a = c ≫ T₂.mor₃ :=
begin
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism _ _
    (rot_of_dist_triangle _ _ hT₁) (rot_of_dist_triangle _ _ hT₂) b c comm,
  refine ⟨(shift_functor C (1 : ℤ)).preimage a, ⟨_, _⟩⟩,
  { apply (shift_functor C (1 : ℤ)).map_injective,
    dsimp at ha₂,
    rw [neg_comp, comp_neg, neg_inj] at ha₂,
    simpa only [functor.map_comp, functor.image_preimage] using ha₂, },
  { simpa only [functor.image_preimage] using ha₁, },
end

lemma complete_distinguished_triangle_morphism₂ (T₁ T₂ : triangle C)
  (hT₁ : T₁ ∈ dist_triang C) (hT₂ : T₂ ∈ dist_triang C) (a : T₁.obj₁ ⟶ T₂.obj₁)
  (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₃ ≫ (shift_functor C (1 : ℤ)).map a = c ≫ T₂.mor₃) :
  ∃ (b : T₁.obj₂ ⟶ T₂.obj₂), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧ T₁.mor₂ ≫ c = b ≫ T₂.mor₂ :=
begin
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism _ _
    (inv_rot_of_dist_triangle _ _ hT₁) (inv_rot_of_dist_triangle _ _ hT₂)
      ((shift_functor C (-1 : ℤ)).map c) a begin
    dsimp only [triangle.inv_rotate, triangle.mk],
    simp only [neg_comp, comp_neg, neg_inj, assoc, ← functor.map_comp_assoc, ← comm,
      iso.app_hom, unit_of_tensor_iso_unit_hom_app, discrete.functor_map_id,
      nat_trans.id_app, id_comp, assoc, functor.map_comp, μ_naturality_assoc,
      nat_trans.naturality, functor.id_map],
  end,
  refine ⟨a, ⟨ha₁, _⟩⟩,
  dsimp at ha₂,
  erw [assoc, ← nat_trans.naturality, functor.id_map] at ha₂,
  simp only [← cancel_mono ((shift_functor_neg_comp_shift_functor C (1 : ℤ)).inv.app T₂.obj₃),
    assoc, ha₂],
end

lemma contractible_distinguished₁ (X : C) : triangle.mk (0 : 0 ⟶ X) (𝟙 X) 0 ∈ dist_triang C :=
begin
  refine pretriangulated.isomorphic_distinguished _ (inv_rot_of_dist_triangle C _ (pretriangulated.contractible_distinguished X)) _ _,
  refine triangle.mk_iso _ _ (functor.map_zero_object _).symm (iso.refl _) (iso.refl _)
    (by tidy) (by tidy) (by tidy),
end

lemma contravariant_yoneda_exact₂ (T : triangle C) (hT : T ∈ dist_triang C) {X : C} (f : T.obj₂ ⟶ X)
  (hf : T.mor₁ ≫ f = 0) : ∃ (g : T.obj₃ ⟶ X), f = T.mor₂ ≫ g :=
begin
  obtain ⟨g, ⟨hg₁, hg₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism T (triangle.mk (0 : 0 ⟶ X) (𝟙 _) 0) hT
    (pretriangulated.contractible_distinguished₁ _) 0 f (by tidy),
  dsimp at hg₁,
  exact ⟨g, by simpa only [comp_id] using hg₁.symm⟩,
end

lemma covariant_yoneda_exact₂ (T : triangle C) (hT : T ∈ dist_triang C) {X : C} (f : X ⟶ T.obj₂)
  (hf : f ≫ T.mor₂ = 0) : ∃ (g : X ⟶ T.obj₁), f = g ≫ T.mor₁ :=
begin
  obtain ⟨a, ⟨ha₁, ha₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism₁ _ T
    (pretriangulated.contractible_distinguished X) hT f 0 (by { dsimp, rw [zero_comp, hf]}),
  dsimp at ha₁,
  exact ⟨a, by simpa only [id_comp] using ha₁⟩,
end

lemma covariant_yoneda_exact₁ (T : triangle C) (hT : T ∈ dist_triang C) {X : C} (f : X ⟶ T.obj₁⟦(1 : ℤ)⟧)
  (hf : f ≫ T.mor₁⟦1⟧' = 0) : ∃ (g : X ⟶ T.obj₃), f = g ≫ T.mor₃ :=
covariant_yoneda_exact₂ _ (rot_of_dist_triangle _ _
  (rot_of_dist_triangle _ _ hT)) f (by { dsimp, rw [comp_neg, hf, neg_zero], })

lemma covariant_yoneda_exact₃ (T : triangle C) (hT : T ∈ dist_triang C) {X : C} (f : X ⟶ T.obj₃)
  (hf : f ≫ T.mor₃ = 0) : ∃ (g : X ⟶ T.obj₂), f = g ≫ T.mor₂ :=
covariant_yoneda_exact₂ _ (rot_of_dist_triangle _ _ hT) f hf

lemma isomorphic_distinguished_iff {T₁ T₂ : triangle C} (e : T₁ ≅ T₂) :
  (T₁ ∈ dist_triang C) ↔ T₂ ∈ dist_triang C :=
begin
  split,
  { intro hT₁,
    exact isomorphic_distinguished _ hT₁ _ e.symm, },
  { intro hT₂,
    exact isomorphic_distinguished _ hT₂ _ e, },
end

lemma inv_rotate_distinguished_triangle (T : triangle C) :
  (T.inv_rotate ∈ dist_triang C) ↔ T ∈ dist_triang C :=
begin
  split,
  { intro hT,
    exact isomorphic_distinguished _ (rot_of_dist_triangle _ _ hT) _
      ((triangle_rotation C).counit_iso.symm.app T), },
  { intro hT,
    exact inv_rot_of_dist_triangle _ T hT, },
end

end

variable (C)

@[simps]
def contractible_triangle_functor [has_zero_object C] : C ⥤ triangle C :=
{ obj := λ X, contractible_triangle X,
  map := λ X Y f,
  { hom₁ := f,
    hom₂ := f,
    hom₃ := 0, }, }

end pretriangulated

end category_theory
