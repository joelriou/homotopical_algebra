import category_theory.limits.shapes.finite_products
import category_theory.products.basic

noncomputable theory

namespace category_theory

open category

variables {C D : Type*} [category C] [category D]

lemma adjunction.compatibility {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) {X : C} {Y : D}
  (f : G.obj X ⟶ Y) : G.map (adj.unit.app X) ≫ (F ⋙ G).map f ≫ adj.counit.app Y = f :=
by simp only [functor.comp_map, adjunction.counit_naturality, adjunction.left_triangle_components_assoc]

namespace limits

variable (C)

def is_left_adjoint_diag_of_has_binary_products [has_binary_products C] :
  is_left_adjoint (functor.diag C) :=
{ right := uncurry.obj prod.functor,
  adj :=
  { hom_equiv := λ X Y,
    { to_fun := λ f, prod.lift f.1 f.2,
      inv_fun := λ g, ⟨g ≫ prod.fst, g ≫ prod.snd⟩,
      left_inv := by tidy,
      right_inv := by tidy, },
    unit := { app := λ X, prod.lift (𝟙 X) (𝟙 X), },
    counit := { app := λ Y, ⟨prod.fst, prod.snd⟩, }, }, }

lemma limit_cone_pair_of_is_left_adjoint_diag [is_left_adjoint (functor.diag C)]
  (X₁ X₂ : C) : limit_cone (pair X₁ X₂) :=
begin
  let Δ := functor.diag C,
  let R := right_adjoint Δ,
  let adj : Δ ⊣ R := is_left_adjoint.adj,
  let η := adj.counit.app ⟨X₁, X₂⟩,
  refine limit_cone.mk (binary_fan.mk η.1 η.2) _,
  refine binary_fan.is_limit.mk _ (λ A f₁ f₂, (adj.hom_equiv A ⟨X₁, X₂⟩) ⟨f₁, f₂⟩)
    (λ A f₁ f₂, _) (λ A f₁ f₂, _) (λ A f₁ f₂ φ hφ₁ hφ₂, _),
  { dsimp [η],
    simpa only [adjunction.hom_equiv_unit, category.assoc]
      using congr_arg (λ x : (_ × _), x.1) (adj.compatibility (⟨f₁, f₂⟩ : Δ.obj A ⟶ ⟨X₁, X₂⟩)), },
  { dsimp [η],
    simpa only [adjunction.hom_equiv_unit, category.assoc]
      using congr_arg (λ x : (_ × _), x.2) (adj.compatibility (⟨f₁, f₂⟩ : Δ.obj A ⟶ ⟨X₁, X₂⟩)), },
  { dsimp,
    symmetry,
    rw [adj.hom_equiv_apply_eq, ← hφ₁, ← hφ₂],
    simp only [binary_fan.mk_fst, binary_fan.mk_snd, adjunction.hom_equiv_counit,
      functor.diag_map, prod_comp], },
end

lemma has_binary_products_of_is_left_adjoint_diag [is_left_adjoint (functor.diag C)] :
  has_binary_products C :=
begin
  haveI : ∀ (X₁ X₂ : C), has_limit (pair X₁ X₂) := λ X₁ X₂,
    has_limit.mk (limit_cone_pair_of_is_left_adjoint_diag X₁ X₂),
  apply has_binary_products_of_has_limit_pair,
end

lemma is_left_adjoint_const_of_has_terminal [has_terminal C]
  {T : Type*} (t : T) [subsingleton T] :
    is_left_adjoint ((functor.const C).obj (discrete.mk t)) :=
{ right := (functor.const (discrete T)).obj (terminal C),
  adj :=
  { hom_equiv := λ X Y,
    { to_fun := λ f, terminal.from _,
      inv_fun := λ f, eq_to_hom (subsingleton.elim _ _),
      left_inv := by tidy,
      right_inv := by tidy, },
    unit := { app := terminal.from, },
    counit := { app := λ Y, eq_to_hom (subsingleton.elim _ _), }, }, }

lemma has_terminal_of_is_left_adjoint_const {T : Type*} (t : T) [subsingleton T]
    [is_left_adjoint ((functor.const C).obj (discrete.mk t))] : has_terminal C :=
begin
  let G := ((functor.const C).obj (discrete.mk t)),
  let F := right_adjoint G,
  let adj : G ⊣ F := is_left_adjoint.adj,
  haveI : ∀ (X : C), unique (X ⟶ F.obj (discrete.mk t)),
  { intro X,
    haveI : subsingleton (X ⟶ F.obj (discrete.mk t)),
    { constructor,
      intros x y,
      apply (adj.hom_equiv _ _).symm.injective,
      apply subsingleton.elim, },
    exact unique_of_subsingleton
      (adj.hom_equiv _ _ (eq_to_hom (subsingleton.elim _ _))), },
  exact has_terminal_of_unique (F.obj (discrete.mk t)),
end

variable {C}

lemma limit.congr_π {J : Type*} [category J] (F : J ⥤ C) [has_limit F] {j₁ j₂ : J}
  (h : j₁ = j₂) : limit.π F j₁ ≫ eq_to_hom (by rw h) = limit.π F j₂ :=
by { subst h, rw [eq_to_hom_refl, category.comp_id], }

variable (C)

lemma has_finite_products_of_has_binary_products
  [has_terminal C] [has_binary_products C] : has_finite_products C :=
begin
  suffices : ∀ (n : ℕ), has_limits_of_shape (discrete (fin n)) C,
  { constructor,
    introsI J hJ,
    exact has_limits_of_shape_of_equivalence (discrete.equivalence (fintype.equiv_fin J).symm), },
  intro n,
  induction n with n hn,
  { exact has_limits_of_shape_of_equivalence (discrete.equivalence
      (equiv.equiv_of_is_empty (pempty : Type) (fin 0))), },
  { constructor,
    intro F,
    have hF : ∃ (φ : fin (n+1) → C), nonempty (F ≅ discrete.functor φ) :=
      ⟨F.obj ∘ discrete.mk, nonempty.intro discrete.nat_iso_functor⟩,
    rcases hF with ⟨φ, hφ⟩,
    suffices : has_limit (discrete.functor φ),
    { haveI := this,
      exact has_limit_of_iso hφ.some.symm, },
    clear hφ F,
    haveI := hn,
    let L := prod (φ 0) (limit (discrete.functor (λ (i : fin n), φ i.succ))),
    let π : Π (i : fin (n+1)), L ⟶ φ i,
    { intro i,
      by_cases i = 0,
      { subst h,
        exact prod.fst, },
      { exact prod.snd ≫ limit.π _ (discrete.mk (i.pred h)) ≫
        eq_to_hom (by { dsimp, rw i.succ_pred h,}), }, },
    have hπ₀ : π 0 = prod.fst := rfl,
    have hπ : ∀ (i : fin n), π i.succ = prod.snd ≫ limit.π _ (discrete.mk i),
    { intro i,
      dsimp [π],
      rw dif_neg i.succ_ne_zero,
      congr' 1,
      exact limit.congr_π (discrete.functor (λ (i : fin n), φ i.succ))
        (congr_arg discrete.mk i.pred_succ), },
    let c : fan φ := fan.mk L π,
    have hc : is_limit c,
    { refine mk_fan_limit _ (λ s, prod.lift (s.proj 0) (pi.lift (λ i, s.proj i.succ)))
         _ _,
      { intros s i,
        by_cases i = 0,
        { subst h,
          simp only [hπ₀, fan_mk_proj, prod.lift_fst], },
        { cases fin.eq_succ_of_ne_zero h with j hj,
          subst hj,
          simp only [hπ, fan_mk_proj, prod.lift_snd_assoc, limit.lift_π, fan.mk_π_app], }, },
      { intros s f hs,
        ext,
        { simpa only [prod.lift_fst] using hs 0, },
        { discrete_cases,
          rw [assoc, assoc, prod.lift_snd_assoc, limit.lift_π, fan.mk_π_app, ← hs j.succ],
          dsimp [c],
          rw hπ, }, }, },
    exact has_limit.mk ⟨c, hc⟩, },
end

end limits

end category_theory
