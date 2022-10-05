import category_theory.preadditive.yoneda
import category_theory.triangulated.pretriangulated
import for_mathlib.algebra.homology.basic_five_lemma
import for_mathlib.category_theory.triangulated.pretriangulated_misc

noncomputable theory

namespace category_theory

open limits category

lemma is_iso_of_yoneda_bijective {C : Type*} [category C] {X Y : C} (f : X ⟶ Y)
  (hf : ∀ (A : C), function.bijective (λ (x : A ⟶ X), x ≫ f)) : is_iso f :=
begin
  haveI : ∀ (A : Cᵒᵖ), is_iso ((yoneda.map f).app A),
  { intro A,
    induction A using opposite.rec,
    rw is_iso_iff_bijective,
    exact hf A, },
  haveI : is_iso (yoneda.map f) := nat_iso.is_iso_of_is_iso_app _,
  exact yoneda.is_iso f,
end

lemma yoneda_bijective_of_is_iso {C : Type*} [category C] {X Y : C} (f : X ⟶ Y) (hf : is_iso f)
  (A : C) : function.bijective (λ (x : A ⟶ X), x ≫ f) :=
begin
  have h : is_iso ((yoneda.map f).app (opposite.op A)) := infer_instance,
  simpa only [is_iso_iff_bijective] using h,
end

namespace triangulated

variables {C : Type*} [category C] [preadditive C] [has_shift C ℤ]

@[simps]
def triangle.product {I : Type*} (T : I → triangle C) [has_product (λ i, (T i).obj₁)]
  [has_product (λ i, (T i).obj₂)] [has_product (λ i, (T i).obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)] : triangle C :=
{ obj₁ := ∏ (λ i, (T i).obj₁),
  obj₂ := ∏ (λ i, (T i).obj₂),
  obj₃ := ∏ (λ i, (T i).obj₃),
  mor₁ := limits.pi.map (λ i, (T i).mor₁),
  mor₂ := limits.pi.map (λ i, (T i).mor₂),
  mor₃ := limits.pi.map (λ i, (T i).mor₃) ≫ inv (pi_comparison _ _), }

@[simps]
def triangle.product.lift {I : Type*} {T' : triangle C}
  {T : I → triangle C} [has_product (λ i, (T i).obj₁)]
  [has_product (λ i, (T i).obj₂)] [has_product (λ i, (T i).obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).obj₁)]
  (f : Π i, T' ⟶ T i) :
  T' ⟶ triangle.product T :=
{ hom₁ := pi.lift (λ i, (f i).hom₁),
  hom₂ := pi.lift (λ i, (f i).hom₂),
  hom₃ := pi.lift (λ i, (f i).hom₃),
  comm₃' := begin
    simp only [triangle.product_mor₃,
      ← cancel_mono (pi_comparison (shift_functor C (1 : ℤ)) (λ (i : I), (T i).obj₁)),
      assoc, is_iso.inv_hom_id, comp_id],
    ext j,
    discrete_cases,
    simp only [map_lift_pi_comparison, assoc, limit.lift_π, fan.mk_π_app,
      triangle_morphism.comm₃, limit.lift_map, cones.postcompose_obj_π,
      nat_trans.comp_app, discrete.nat_trans_app],
  end, }

open algebra.homology


structure triangle.comp_eq_zero (T : triangle C) : Prop :=
(zero₁₂ : T.mor₁ ≫ T.mor₂ = 0)
(zero₂₃ : T.mor₂ ≫ T.mor₃ = 0)
(zero₃₁ : T.mor₃ ≫ T.mor₁⟦1⟧' = 0)

variables [has_zero_object C]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

lemma triangle.comp_eq_zero.of_distinguished (T : triangle C) (hT : T ∈ dist_triang C) :
  T.comp_eq_zero :=
begin
  constructor,
  exact pretriangulated.comp_dist_triangle_mor_zero₁₂ _ T hT,
  exact pretriangulated.comp_dist_triangle_mor_zero₂₃ _ T hT,
  exact pretriangulated.comp_dist_triangle_mor_zero₃₁ _ T hT,
end

variable (C)

@[derive category]
def candidate_triangle := full_subcategory (λ (T : triangle C), T.comp_eq_zero)

variable {C}

@[simps]
def candidate_triangle.of_distinguished (T : triangle C) (hT : T ∈ dist_triang C) :
  candidate_triangle C := ⟨T, triangle.comp_eq_zero.of_distinguished T hT⟩

variable (C)

@[simps]
def candidate_triangle.to_five_complex : candidate_triangle C ⥤ five_complex C :=
{ obj := λ T,
  { X₁ := T.1.obj₁,
    X₂ := T.1.obj₂,
    X₃ := T.1.obj₃,
    X₄ := T.1.obj₁⟦(1 : ℤ)⟧,
    X₅ := T.1.obj₂⟦(1 : ℤ)⟧,
    f₁ := T.1.mor₁,
    f₂ := T.1.mor₂,
    f₃ := T.1.mor₃,
    f₄ := T.1.mor₁⟦1⟧',
    h₁₂ := T.2.zero₁₂,
    h₂₃ := T.2.zero₂₃,
    h₃₄ := T.2.zero₃₁, },
  map := λ T T' φ,
  { τ₁ := φ.hom₁,
    τ₂ := φ.hom₂,
    τ₃ := φ.hom₃,
    τ₄ := φ.hom₁⟦1⟧',
    τ₅ := φ.hom₂⟦1⟧',
    comm₁ := φ.comm₁,
    comm₂ := φ.comm₂,
    comm₃ := φ.comm₃,
    comm₄ := by { dsimp, simp only [← functor.map_comp, φ.comm₁], }, },
  map_id' := λ T, by { ext; try { refl, }; apply functor.map_id, },
  map_comp' := λ T T' T'' φ ψ, by { ext; try { refl, }; apply functor.map_comp, }, }

variable {C}

lemma candidate_triangle.coyoneda_exact_of_distinguished (T : triangle C) (hT : T ∈ dist_triang C)
  (A : C) : five_complex.exact (((candidate_triangle.to_five_complex C) ⋙
    (preadditive_coyoneda.obj (opposite.op A)).map_five_complex).obj
      (candidate_triangle.of_distinguished T hT)) :=
{ ex₂ := λ x₂ hx₂, ⟨_, (covariant_yoneda_exact₂ T hT x₂ hx₂).some_spec.symm⟩,
  ex₃ := λ x₃ hx₃, ⟨_, (covariant_yoneda_exact₃ T hT x₃ hx₃).some_spec.symm⟩,
  ex₄ := λ x₁ hx₁, ⟨_, (covariant_yoneda_exact₁ T hT x₁ hx₁).some_spec.symm⟩, }

lemma is_iso_hom₃_of_distinguished {T T' : triangle C} (φ : T ⟶ T') [is_iso φ.hom₁]
  [is_iso φ.hom₂] (hT : T ∈ dist_triang C) (hT' : T' ∈ dist_triang C) : is_iso φ.hom₃ :=
is_iso_of_yoneda_bijective _ (λ A, begin
  let ψ : candidate_triangle.of_distinguished T hT ⟶
    candidate_triangle.of_distinguished T' hT' := φ,
  refine five_complex.five_lemma_bijective ((preadditive_coyoneda.obj
      (opposite.op A)).map_five_complex.map ((candidate_triangle.to_five_complex C).map ψ))
    (candidate_triangle.coyoneda_exact_of_distinguished _ _ _)
    (candidate_triangle.coyoneda_exact_of_distinguished _ _ _)
    (yoneda_bijective_of_is_iso _ _ _)
    (yoneda_bijective_of_is_iso _ _ _)
    (yoneda_bijective_of_is_iso _ _ _)
    (yoneda_bijective_of_is_iso _ _ _),
  all_goals { dsimp, apply_instance, },
end)

lemma is_iso_hom₂_of_distinguished {T T' : triangle C} (φ : T ⟶ T') [is_iso φ.hom₁]
  [is_iso φ.hom₃] (hT : T ∈ dist_triang C) (hT' : T' ∈ dist_triang C) : is_iso φ.hom₂ :=
begin
  haveI : is_iso ((inv_rotate C).map φ).hom₁,
  { dsimp, apply_instance, },
  haveI : is_iso ((inv_rotate C).map φ).hom₂,
  { dsimp, apply_instance, },
  exact is_iso_hom₃_of_distinguished ((inv_rotate C).map φ) (pretriangulated.inv_rot_of_dist_triangle _ _ hT)
    (pretriangulated.inv_rot_of_dist_triangle _ _ hT'),
end

lemma is_iso_hom₁_of_distinguished {T T' : triangle C} (φ : T ⟶ T') [is_iso φ.hom₂]
  [is_iso φ.hom₃] (hT : T ∈ dist_triang C) (hT' : T' ∈ dist_triang C) : is_iso φ.hom₁ :=
begin
  haveI : is_iso ((rotate C).map φ).hom₁ := by { dsimp, apply_instance, },
  haveI : is_iso ((rotate C).map φ).hom₂ := by { dsimp, apply_instance, },
  haveI : is_iso ((shift_functor C (1 : ℤ)).map φ.hom₁) := is_iso_hom₃_of_distinguished
    ((rotate C).map φ) (pretriangulated.rot_of_dist_triangle _ _ hT)
    (pretriangulated.rot_of_dist_triangle _ _ hT'),
  exact is_iso_of_reflects_iso φ.hom₁ (shift_functor C (1 : ℤ)),
end

@[simps hom_hom₁ hom_hom₂ inv_hom₁ inv_hom₂]
def iso_triangle_of_distinguished_of_is_iso₁₂ (T T' : triangle C) (hT : T ∈ dist_triang C)
  (hT' : T' ∈ dist_triang C) (e₁ : T.obj₁ ≅ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂)
  (comm : T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁) : T ≅ T' :=
begin
  let h := pretriangulated.complete_distinguished_triangle_morphism
    T T' hT hT' e₁.hom e₂.hom comm,
  let φ : T ⟶ T' :=
  { hom₁ := e₁.hom,
    hom₂ := e₂.hom,
    hom₃ := h.some,
    comm₁' := comm,
    comm₂' := h.some_spec.1,
    comm₃' := h.some_spec.2, },
  haveI : is_iso φ.hom₃ := is_iso_hom₃_of_distinguished φ hT hT',
  exact triangle.mk_iso _ _ e₁ e₂ (as_iso φ.hom₃) φ.comm₁ φ.comm₂ φ.comm₃,
end

lemma map_pi_map_pi_comparison {C D I : Type*} [category C] [category D]
  {X : I → C} {Y : I → C} (f : Π i, X i ⟶ Y i) (F : C ⥤ D) [has_product X]
  [has_product Y] [has_product (λ i, F.obj (X i))] [has_product (λ i, F.obj (Y i))] :
  F.map (pi.map f) ≫ pi_comparison F Y =
    pi_comparison F X ≫ pi.map (λ i, F.map (f i) : Π i, F.obj (X i) ⟶ F.obj (Y i)) :=
begin
  ext i,
  discrete_cases,
  simp only [assoc, pi_comparison_comp_π, lim_map_π, discrete.nat_trans_app,
    pi_comparison_comp_π_assoc, ← F.map_comp],
end

def candidate_triangle.pi {I : Type*} (T : I → candidate_triangle C)
  [has_product (λ i, (T i).1.obj₁)]
  [has_product (λ i, (T i).1.obj₂)] [has_product (λ i, (T i).1.obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).1.obj₁)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).1.obj₂)] :
  candidate_triangle C :=
begin
  refine ⟨triangle.product (λ i, (T i).1), ⟨_, _, _⟩⟩,
  { ext i,
    discrete_cases,
    simp only [triangle.product_mor₁, triangle.product_mor₂, assoc, lim_map_π,
      discrete.nat_trans_app, lim_map_π_assoc, zero_comp, (T i).2.1, comp_zero], },
  { simp only [triangle.product_mor₂, triangle.product_mor₃,
      ← cancel_mono (pi_comparison (shift_functor C (1 : ℤ)) (λ (i : I), (T i).1.obj₁)),
      is_iso.inv_hom_id, comp_id, zero_comp, assoc],
    ext i,
    discrete_cases,
    simp only [assoc, lim_map_π, discrete.nat_trans_app, lim_map_π_assoc, zero_comp,
      (T i).2.2, comp_zero], },
  { simp only [triangle.product_mor₃, triangle.product_mor₁, assoc],
    rw [← cancel_mono (pi_comparison (shift_functor C (1 : ℤ)) (λ (i : I), (T i).1.obj₂)),
      assoc, assoc, zero_comp, map_pi_map_pi_comparison, is_iso.inv_hom_id_assoc],
    ext i,
    discrete_cases,
    simp only [assoc, lim_map_π, discrete.nat_trans_app, lim_map_π_assoc, zero_comp],
    erw [(T i).2.3, comp_zero], },
end

lemma candidate_triangle.pi_coyoneda_exact {I : Type*} (T : I → candidate_triangle C)
  [has_product (λ i, (T i).1.obj₁)]
  [has_product (λ i, (T i).1.obj₂)] [has_product (λ i, (T i).1.obj₃)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).1.obj₁)]
  [has_product (λ i, (shift_functor C (1 : ℤ)).obj (T i).1.obj₂)] (A : C)
  (hT : ∀ (i : I), ((preadditive_coyoneda.obj (opposite.op A)).map_five_complex.obj ((candidate_triangle.to_five_complex C).obj (T i))).exact) :
  ((preadditive_coyoneda.obj (opposite.op A)).map_five_complex.obj ((candidate_triangle.to_five_complex C).obj (candidate_triangle.pi T))).exact :=
begin
  sorry,
end

end triangulated

end category_theory
