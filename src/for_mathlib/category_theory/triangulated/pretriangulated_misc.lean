import category_theory.triangulated.pretriangulated
import for_mathlib.category_theory.localization.triangulated

namespace category_theory

open limits category preadditive
open_locale zero_object

namespace triangulated

open pretriangulated

variables {C : Type*} [category C] [preadditive C] [has_zero_object C] [has_shift C ℤ]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

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

lemma pretriangulated.distinguished_cocone_triangle₂ {Z X : C} (h : Z ⟶ X⟦(1 : ℤ)⟧) :
  ∃ (Y : C) (f : X ⟶ Y) (g : Y ⟶ Z), triangle.mk C f g h ∈ dist_triang C :=
begin
  obtain ⟨Y', f', g', mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ h,
  let T := triangle.mk C h f' g',
  change T ∈ dist_triang C at mem,
  let T' := T.inv_rotate.inv_rotate,
  let e₁ := (shift_functor_comp_shift_functor_neg C (1 : ℤ)).app X,
  let e₂ := (shift_functor_neg_comp_shift_functor C (1 : ℤ)).app ((shift_functor C (1 : ℤ)).obj X),
  let T'' := triangle.mk C (e₁.inv ≫ T'.mor₁) T'.mor₂ (T'.mor₃ ≫ e₂.hom),
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

lemma pretriangulated.distinguished_cocone_triangle₁ {Y Z : C} (g : Y ⟶ Z) :
  ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦1⟧), triangle.mk C f g h ∈ dist_triang C :=
begin
  obtain ⟨X', f', g', mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ g,
  exact ⟨_, _, _, inv_rot_of_dist_triangle _ _ mem⟩,
end

lemma pretriangulated.complete_distinguished_triangle_morphism₁ (T₁ T₂ : triangle C)
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

lemma pretriangulated.complete_distinguished_triangle_morphism₂ (T₁ T₂ : triangle C)
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

lemma pretriangulated.contractible_distinguished₁ (X : C) : triangle.mk C (0 : 0 ⟶ X) (𝟙 X) 0 ∈ dist_triang C :=
begin
  refine pretriangulated.isomorphic_distinguished _ (inv_rot_of_dist_triangle C _ (pretriangulated.contractible_distinguished X)) _ _,
  refine triangle.mk_iso _ _ (functor.map_zero_object _).symm (iso.refl _) (iso.refl _)
    (by tidy) (by tidy) (by tidy),
end

lemma contravariant_yoneda_exact₂ (T : triangle C) (hT : T ∈ dist_triang C) {X : C} (f : T.obj₂ ⟶ X)
  (hf : T.mor₁ ≫ f = 0) : ∃ (g : T.obj₃ ⟶ X), f = T.mor₂ ≫ g :=
begin
  obtain ⟨g, ⟨hg₁, hg₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism T (triangle.mk C (0 : 0 ⟶ X) (𝟙 _) 0) hT
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

end triangulated

end category_theory
