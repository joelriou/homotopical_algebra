import for_mathlib.category_theory.triangulated.homological_functor
import for_mathlib.category_theory.shift_op

noncomputable theory

namespace category_theory

open category limits

namespace functor

variables {C₁ C₂ D : Type*} [category C₁] [category C₂] [category D]

section

variables (F : C₁ ⥤ C₂ ⥤ D) {A G : Type*} [add_comm_monoid A]
  [has_shift C₁ A] [has_shift C₂ A]

def shift_swap (a : A) :=
  (shift_functor C₁ a) ⋙ F ≅ F ⋙ (whiskering_left _ _ D).obj (shift_functor C₂ a)

namespace shift_swap

variable (A)

def zero : shift_swap F (0 : A) :=
iso_whisker_right (shift_functor_zero C₁ A) F ≪≫ F.left_unitor ≪≫
  F.right_unitor.symm ≪≫
  iso_whisker_left F ((whiskering_left_id _ _).symm ≪≫
    (whiskering_left _ _ D).map_iso (shift_functor_zero C₂ A).symm)

lemma zero_hom_app_app (X₁ : C₁) (X₂ : C₂) :
  ((zero F A).hom.app X₁).app X₂ =
  (F.map ((shift_functor_zero C₁ A).hom.app X₁)).app X₂ ≫
    (F.obj X₁).map ((shift_functor_zero C₂ A).inv.app X₂) :=
begin
  dsimp only [zero, left_unitor, right_unitor, iso.trans, iso_whisker_right, iso_whisker_left,
    whiskering_right, whiskering_left, iso.symm, nat_trans.comp_app, whiskering_left_id,
    nat_iso.of_components, map_iso, whisker_left, whisker_right],
  erw [id_comp, id_comp, id_comp],
end

lemma zero_inv_app_app (X₁ : C₁) (X₂ : C₂) :
  ((zero F A).inv.app X₁).app X₂ =
  (F.obj X₁).map ((shift_functor_zero C₂ A).hom.app X₂) ≫
  (F.map ((shift_functor_zero C₁ A).inv.app X₁)).app X₂ :=
begin
  dsimp only [zero, left_unitor, right_unitor, iso.trans, iso_whisker_right, iso_whisker_left,
    whiskering_right, whiskering_left, iso.symm, nat_trans.comp_app, whiskering_left_id,
    nat_iso.of_components, map_iso, whisker_left, whisker_right],
  erw [comp_id, comp_id, comp_id],
end

variables {F A}

def add' {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b) (c : A) (h : c = a+b) :
  shift_swap F c :=
iso_whisker_right (shift_functor_add' C₁ a b c h) F ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left _ e₂ ≪≫ (functor.associator _ _ _).symm ≪≫
  iso_whisker_right e₁ _ ≪≫ functor.associator _ _ _ ≪≫
  iso_whisker_left F ((whiskering_left _ _ D).map_iso
    (shift_functor_add' C₂ b a c (by rw [h, add_comm])).symm)

def add {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b) :
  shift_swap F (a+b) := add' e₁ e₂ (a+b) rfl

lemma add'_hom_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (c : A) (h : c = a+b) (X₁ : C₁) (X₂ : C₂) :
  ((add' e₁ e₂ c h).hom.app X₁).app X₂ =
    (F.map ((shift_functor_add' C₁ a b c h).hom.app X₁)).app X₂ ≫
    (e₂.hom.app (X₁⟦a⟧)).app X₂ ≫ (e₁.hom.app X₁).app (X₂⟦b⟧) ≫
    (F.obj X₁).map ((shift_functor_add' C₂ b a c (by rw [h, add_comm])).inv.app X₂) :=
begin
  dsimp [add'],
  erw [id_comp, id_comp, id_comp],
end

lemma add_hom_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
   (X₁ : C₁) (X₂ : C₂) :
  ((add e₁ e₂).hom.app X₁).app X₂ =
    (F.map ((shift_functor_add C₁ a b).hom.app X₁)).app X₂ ≫
    (e₂.hom.app (X₁⟦a⟧)).app X₂ ≫ (e₁.hom.app X₁).app (X₂⟦b⟧) ≫
    (F.obj X₁).map
      ((shift_functor_add' C₂ b a (a+b) (add_comm a b)).inv.app X₂) :=
begin
  dsimp only [add],
  rw [add'_hom_app_app, shift_functor_add'_eq_shift_functor_add],
end

lemma add'_inv_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (c : A) (h : c = a+b) (X₁ : C₁) (X₂ : C₂) :
  ((add' e₁ e₂ c h).inv.app X₁).app X₂ =
    (F.obj X₁).map ((shift_functor_add' C₂ b a c (by rw [h, add_comm])).hom.app X₂) ≫
    (e₁.inv.app X₁).app (X₂⟦b⟧) ≫
    (e₂.inv.app (X₁⟦a⟧)).app X₂ ≫
    (F.map ((shift_functor_add' C₁ a b c h).inv.app X₁)).app X₂ :=
begin
  dsimp [add'],
  erw [comp_id, comp_id, comp_id, assoc, assoc],
end

lemma add_inv_app_app {a b : A} (e₁ : shift_swap F a) (e₂ : shift_swap F b)
  (X₁ : C₁) (X₂ : C₂) :
  ((add e₁ e₂).inv.app X₁).app X₂ =
    (F.obj X₁).map ((shift_functor_add' C₂ b a _ (add_comm a b)).hom.app X₂) ≫
    (e₁.inv.app X₁).app (X₂⟦b⟧) ≫
    (e₂.inv.app (X₁⟦a⟧)).app X₂ ≫
    (F.map ((shift_functor_add C₁ a b).inv.app X₁)).app X₂ :=
begin
  dsimp only [add],
  rw [add'_inv_app_app, shift_functor_add'_eq_shift_functor_add],
end

end shift_swap

variable (A)

class has_shift_swap :=
(iso [] : Π (a : A), F.shift_swap a)
(iso_zero [] : iso 0 = shift_swap.zero F A)
(iso_add [] : ∀ (a b : A), iso (a+b) = shift_swap.add (iso a) (iso b))

variable {A}

def has_shift_swap.iso' [F.has_shift_swap A] (a b c : A) (h : c = a + b) :
  (shift_functor C₁ a) ⋙ F ⋙ (whiskering_left _ _ D).obj (shift_functor C₂ b) ≅
    F ⋙ (whiskering_left _ _ D).obj (shift_functor C₂ c) :=
(functor.associator _ _ _).symm ≪≫ iso_whisker_right (has_shift_swap.iso F a) _ ≪≫
  functor.associator _ _ _ ≪≫ iso_whisker_left _ ((whiskering_left C₂ C₂ D).map_iso (shift_functor_add' C₂ b a c (by rw [h, add_comm])).symm)

namespace has_shift_swap

variable [F.has_shift_swap A]

lemma iso'_hom_app_app (a b c : A) (h : c = a + b) (X₁ : C₁) (X₂ : C₂ ):
  ((iso' F a b c h).hom.app X₁).app X₂ =
    ((iso F a).hom.app X₁).app ((shift_functor C₂ b).obj X₂) ≫
      (F.obj X₁).map ((shift_functor_add' C₂ b a c (by rw [h, add_comm])).inv.app X₂) :=
begin
  dsimp [iso'],
  rw [id_comp, id_comp],
end

lemma iso'_zero_hom_app_app (b : A) (X₁ : C₁) (X₂ : C₂ ):
  ((iso' F 0 b b (zero_add b).symm).hom.app X₁).app X₂ =
    (F.map ((shift_functor_zero C₁ A).hom.app X₁)).app (X₂⟦b⟧) :=
begin
  simp only [iso'_hom_app_app, has_shift_swap.iso_zero,
    shift_swap.zero_hom_app_app, assoc, ← functor.map_comp],
  convert comp_id _,
  convert functor.map_id _ _,
  sorry,
end

lemma iso'_hom_app_app_comp (a b c a' d e : A) (hc : c = a + b) (he : e = a'+a) (hd : d = a'+c)
   (X₁ : C₁) (X₂ : C₂ ) :
  ((iso' F a b c hc).hom.app (X₁⟦a'⟧)).app X₂ ≫ ((iso' F a' c d hd).hom.app X₁).app X₂ =
    (F.map ((shift_functor_add' C₁ a' a e he).inv.app X₁)).app (X₂⟦b⟧) ≫
      ((iso' F e b d (by rw [hd, he, hc, add_assoc])).hom.app X₁).app X₂ :=
begin
  sorry,
end

end has_shift_swap

end

section

variables {C : Type*} [category C] [has_shift C ℤ]
  [preadditive C] [∀ (n : ℤ), (shift_functor C n).additive]

local attribute [instance] has_shift_op_neg_ℤ

@[simps]
def preadditive_yoneda_shift_swap_add_equiv (X₁ X₂ : C) (n : ℤ) :
  (X₂ ⟶ X₁⟦n⟧) ≃+ (X₂⟦-n⟧ ⟶ X₁) :=
{ to_fun := λ f, f⟦-n⟧' ≫ (shift_equiv C n).unit_iso.inv.app X₁,
  inv_fun := λ f, (shift_equiv C n).counit_iso.inv.app X₂ ≫ f⟦n⟧',
  left_inv := λ f, begin
    dsimp only,
    erw [functor.map_comp, ← nat_trans.naturality_assoc,
      (shift_equiv C n).counit_inv_functor_comp, comp_id],
    refl,
  end,
  right_inv := λ f, begin
    dsimp only,
    erw [functor.map_comp, assoc],
    erw (shift_equiv C n).unit_iso.inv.naturality f,
    slice_lhs 1 2 { erw (shift_equiv C n).inverse_counit_inv_comp, },
    erw id_comp,
    refl,
  end,
  map_add' := λ f₁ f₂, by rw [functor.map_add, preadditive.add_comp], }

variable (C)

@[simps]
def preadditive_yoneda_shift_swap (n : ℤ) :
  shift_swap (preadditive_yoneda : C ⥤ _) n :=
nat_iso.of_components (λ X₁, nat_iso.of_components
  (λ X₂, add_equiv.to_AddCommGroup_iso (preadditive_yoneda_shift_swap_add_equiv X₁ X₂.unop n))
  (by tidy)) (by tidy)

-- this would be better with coyoneda instead

def hom_functor_has_shift_swap : (preadditive_yoneda : C ⥤ _).has_shift_swap ℤ :=
{ iso := preadditive_yoneda_shift_swap C,
  iso_zero := begin
    ext X₁ X₂ x,
    dsimp at x,
    rw shift_swap.zero_hom_app_app,
    dsimp only [preadditive_yoneda_shift_swap, nat_iso.of_components,
      preadditive_yoneda_shift_swap_add_equiv, add_equiv.to_AddCommGroup_iso,
      add_equiv.to_add_monoid_hom, add_monoid_hom.coe_mk],
    rw [comp_apply, preadditive_yoneda_map_app_apply],
    erw preadditive_yoneda_obj_map_apply,
    --let y := ((shift_functor_zero Cᵒᵖ ℤ).inv.app X₂).unop,
    --let y' := (shift_functor_zero C ℤ).hom.app (opposite.unop X₂),
    --change _ = y ≫ _,
    sorry,
  end,
  iso_add := sorry, }

end

section

variables (F : C₁ ⥤ C₂ ⥤ D) [has_shift C₁ ℤ] [has_shift C₂ ℤ] [abelian D]
  [preadditive C₁] [has_zero_object C₁] [∀ (n : ℤ), (shift_functor C₁ n).additive]
  [pretriangulated C₁]
  [∀ (Y₂ : C₂), (((whiskering_right _ _ _).obj
    ((evaluation C₂ D).obj Y₂)).obj F).preserves_zero_morphisms]
  [∀ (Y₂ : C₂), (((whiskering_right _ _ _).obj
    ((evaluation C₂ D).obj Y₂)).obj F).is_homological]

lemma is_homological.bifunctor_map_distinguished (T : pretriangulated.triangle C₁)
  (hT : T ∈ dist_triang C₁) (Y₂ : C₂) :
  ((T.short_complex hT).map (((whiskering_right C₁ (C₂ ⥤ D) D).obj
    ((evaluation C₂ D).obj Y₂)).obj F)).exact :=
is_homological.map_distinguished (((whiskering_right _ _ _).obj
  ((evaluation C₂ D).obj Y₂)).obj F) T hT

lemma is_homological.bifunctor_ex₁₂ (T : pretriangulated.triangle C₁)
  (hT : T ∈ dist_triang C₁) (Y₂ : C₂) (n : ℤ) :
  (short_complex.mk ((F.map T.mor₁).app (Y₂⟦n⟧)) ((F.map T.mor₂).app (Y₂⟦n⟧))
    (by simpa only [← nat_trans.comp_app, ← F.map_comp, pretriangulated.triangle.comp_zero₁₂ T hT]
        using (((whiskering_right _ _ _).obj ((evaluation C₂ D).obj _)).obj F).map_zero T.obj₁ T.obj₃)).exact :=
is_homological.map_distinguished (((whiskering_right _ _ _).obj
  ((evaluation C₂ D).obj (Y₂⟦n⟧))).obj F) T hT

variables [F.has_shift_swap ℤ]

def is_homological.bifunctor_δ₁ (T : pretriangulated.triangle C₁) (hT : T ∈ dist_triang C₁)
  (Y₂ : C₂) (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (F.obj T.obj₃).obj (Y₂⟦n₀⟧) ⟶ (F.obj T.obj₁).obj (Y₂⟦n₁⟧) :=
(F.map T.mor₃).app (Y₂⟦n₀⟧) ≫
  ((has_shift_swap.iso' F 1 n₀ n₁ (by rw [h, add_comm])).hom.app T.obj₁).app Y₂

lemma is_homological.bifunctor_comp_δ₁
  (T : pretriangulated.triangle C₁) (hT : T ∈ dist_triang C₁)
  (Y₂ : C₂) (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (F.map T.mor₂).app (Y₂⟦n₀⟧) ≫ is_homological.bifunctor_δ₁ F T hT Y₂ _ _ h = 0 :=
begin
  dsimp only [is_homological.bifunctor_δ₁],
  rw ← assoc,
  convert zero_comp,
  rw [← nat_trans.comp_app, ← F.map_comp, pretriangulated.triangle.comp_zero₂₃ T hT],
  exact (((whiskering_right _ _ _).obj ((evaluation C₂ D).obj _)).obj F).map_zero _ _,
end

lemma is_homological.bifunctor_ex₁₃
  (T : pretriangulated.triangle C₁) (hT : T ∈ dist_triang C₁)
  (Y₂ : C₂) (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (short_complex.mk _ _ (is_homological.bifunctor_comp_δ₁ F T hT Y₂ _ _ h)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1 (is_homological.map_distinguished
    (((whiskering_right _ _ _).obj ((evaluation C₂ D).obj (Y₂⟦n₀⟧))).obj F)
    _ ((pretriangulated.rotate_distinguished_triangle T).1 hT)),
  refine short_complex.mk_iso (iso.refl _) (iso.refl _)
    (((has_shift_swap.iso' F 1 n₀ n₁ (by rw [h, add_comm])).app T.obj₁).app Y₂) _ _,
  { dsimp, rw [id_comp, comp_id], },
  { dsimp,
    rw id_comp,
    refl, },
end

def is_homological.bifunctor_δ₁_comp
  (T : pretriangulated.triangle C₁) (hT : T ∈ dist_triang C₁)
  (Y₂ : C₂) (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  is_homological.bifunctor_δ₁ F T hT Y₂ _ _ h ≫ (F.map T.mor₁).app (Y₂⟦n₁⟧) = 0 :=
begin
  dsimp only [is_homological.bifunctor_δ₁],
  have eq := congr_app ((has_shift_swap.iso' F 1 n₀ n₁ (by rw [h, add_comm])).hom.naturality T.mor₁) Y₂,
  dsimp at eq,
  rw [assoc, ← eq, ← assoc],
  convert zero_comp,
  rw [← nat_trans.comp_app, ← F.map_comp, pretriangulated.triangle.comp_zero₃₁ T hT],
  exact (((whiskering_right _ _ _).obj ((evaluation C₂ D).obj _)).obj F).map_zero _ _,
end

lemma is_homological.bifunctor_ex₁₁
  (T : pretriangulated.triangle C₁) (hT : T ∈ dist_triang C₁)
  (Y₂ : C₂) (n₀ n₁ : ℤ) (h : n₁ = n₀+1) :
  (short_complex.mk _ _ (is_homological.bifunctor_δ₁_comp F T hT Y₂ _ _ h)).exact :=
begin
  refine (short_complex.exact_iff_of_iso _).1 (is_homological.map_distinguished
    (((whiskering_right _ _ _).obj ((evaluation C₂ D).obj (Y₂⟦n₁⟧))).obj F)
    _ ((pretriangulated.inv_rotate_distinguished_triangle T).2 hT)),
  refine short_complex.mk_iso (preadditive.mul_iso (-1) ((((has_shift_swap.iso' F (-1) n₁ n₀ (by linarith)).app T.obj₃)).app Y₂)) (iso.refl _) (iso.refl _) _ _,
  { dsimp only [preadditive.mul_iso, iso.refl,
      pretriangulated.triangle.inv_rotate, pretriangulated.triangle.mk,
      short_complex.map, whiskering_right, evaluation, functor.comp,
      pretriangulated.triangle.short_complex,
      pretriangulated.candidate_triangle.of_distinguished,
      pretriangulated.candidate_triangle.short_complex,
      is_homological.bifunctor_δ₁],
    have eq := congr_app ((has_shift_swap.iso' F (-1) n₁ n₀ (by linarith)).hom.naturality T.mor₃) Y₂,
    dsimp at eq,
    rw [comp_id, units.coe_neg_one, neg_smul, one_smul],
    nth_rewrite 0 preadditive.neg_comp,
    erw [← reassoc_of eq, ← preadditive.neg_comp, ← preadditive.neg_comp, F.map_comp],
    conv_rhs { rw nat_trans.comp_app, },
    congr' 1,
    { exact (functor.map_neg (((whiskering_right _ _ _).obj
        ((evaluation C₂ D).obj (Y₂⟦n₁⟧))).obj F)).symm, },
    { rw [has_shift_swap.iso'_hom_app_app_comp F (-1) n₁ n₀ 1 n₁ 0 (by linarith)
        (by linarith) (by linarith), has_shift_swap.iso'_zero_hom_app_app,
        ← nat_trans.comp_app, ← F.map_comp,
        ← shift_functor_comp_shift_functor_neg_eq_add'_comp_zero],
      refl, }, },
  { dsimp,
    rw [id_comp, comp_id], },
end

end

end functor

end category_theory
