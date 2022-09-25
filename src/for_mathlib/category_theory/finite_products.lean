import category_theory.limits.shapes.finite_products
import category_theory.products.basic
import for_mathlib.category_theory.functor_misc

noncomputable theory

namespace category_theory

open category

section
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

variable {C}

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

variable (C)

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

end
example : ℕ := 42

section

variables {J : Type*} {C : J → Type*} {D : J → Type*}
  [Π j, category (C j)] [Π j, category (D j)] {E : Type*} [category E]

instance : category (Π j, C j) :=
{ hom := λ X Y, Π j, X j ⟶ Y j,
  id := λ X j, 𝟙 (X j),
  comp := λ X Y Z f g j, f j ≫ g j, }

@[simps]
def functor.pi_ (F : Π j, C j ⥤ D j) : (Π j, C j) ⥤ (Π j, D j) :=
{ obj := λ X j, (F j).obj (X j),
  map := λ X Y f j, (F j).map (f j), }

@[simps]
def functor.pi'_ (F : Π j, E ⥤ D j) : E ⥤ (Π j, D j) :=
{ obj := λ X j, (F j).obj X,
  map := λ X Y f j, (F j).map f, }

@[simps]
def nat_trans.pi_ {F G : Π j, C j ⥤ D j} (e : Π j, F j ⟶ G j) :
  functor.pi_ F ⟶ functor.pi_ G :=
{ app := λ X j, (e j).app (X j), }

@[simps]
def nat_iso.pi {F G : Π j, C j ⥤ D j} (e : Π j, F j ≅ G j) :
  functor.pi_ F ≅ functor.pi_ G :=
{ hom := nat_trans.pi_ (λ j, (e j).hom),
  inv := nat_trans.pi_ (λ j, (e j).inv), }

@[simps]
def nat_trans.pi'_ {F G : Π j, E ⥤ D j} (e : Π j, F j ⟶ G j) :
  functor.pi'_ F ⟶ functor.pi'_ G :=
{ app := λ X j, (e j).app X, }

@[simps]
def nat_iso.pi'_ {F G : Π j, E ⥤ D j} (e : Π j, F j ≅ G j) :
  functor.pi'_ F ≅ functor.pi'_ G :=
{ hom := nat_trans.pi'_ (λ j, (e j).hom),
  inv := nat_trans.pi'_ (λ j, (e j).inv), }

@[simps]
def equivalence.pi (e : Π j, C j ≌ D j) : (Π j, C j) ≌ (Π j, D j) :=
{ functor := functor.pi_ (λ j, (e j).functor),
  inverse := functor.pi_ (λ j, (e j).inverse),
  unit_iso := nat_iso.pi (λ j, (e j).unit_iso),
  counit_iso := nat_iso.pi (λ j, (e j).counit_iso), }

variable (C)

@[simps]
def functor.pi_.eval (j : J) : (Π j, C j) ⥤ C j :=
{ obj := λ X, X j,
  map := λ X Y f, f j, }

variable {C}

@[simp]
lemma functor.pi_eval (F : Π j, C j ⥤ D j) (j : J) :
  functor.pi_ F ⋙ functor.pi_.eval _ j = functor.pi_.eval _ j ⋙ F j := rfl

@[simp]
def functor.pi'__eval (F : Π j, E ⥤ D j) (j : J) :
  functor.pi'_ F ⋙ functor.pi_.eval _ j = F j :=
functor.ext (λ X, rfl) (by tidy)

@[simp]
def functor.pi'__eval_iso (F : Π j, E ⥤ D j) (j : J) :
  functor.pi'_ F ⋙ functor.pi_.eval _ j ≅ F j :=
eq_to_iso (functor.pi'__eval F j)

lemma functor.pi_.ext {F₁ F₂ : E ⥤ (Π j, C j)}
  (h : ∀ (j : J), F₁ ⋙ functor.pi_.eval _ j = F₂ ⋙ functor.pi_.eval _ j) : F₁ = F₂ :=
begin
  refine functor.ext (λ X, _) (λ X Y f, _),
  { ext j,
    exact functor.congr_obj (h j) X, },
  { ext j,
    simpa only [pi.comp_apply, functor.eq_to_hom_proj]
      using functor.congr_map_conjugate (h j) f, },
end

@[simps]
def functor.pi_.mk_nat_trans {F₁ F₂ : E ⥤ (Π j, C j)}
  (τ : Π (j : J), F₁ ⋙ functor.pi_.eval _ j ⟶ F₂ ⋙ functor.pi_.eval _ j) : F₁ ⟶ F₂ :=
{ app := λ X j, (τ j).app X,
  naturality' := λ X Y f, by { ext j, exact (τ j).naturality f, }, }

@[simps]
def functor.pi_.mk_nat_iso {F₁ F₂ : E ⥤ (Π j, C j)}
  (e : Π (j : J), F₁ ⋙ functor.pi_.eval _ j ≅ F₂ ⋙ functor.pi_.eval _ j) : F₁ ≅ F₂ :=
{ hom := functor.pi_.mk_nat_trans (λ j, (e j).hom),
  inv := functor.pi_.mk_nat_trans (λ j, (e j).inv), }

variable (C)

def pi.equivalence_of_eq {j j' : J} (eq : j = j') : C j ≌ C j' := by subst eq

def pi.equivalence_of_eq_functor_eq {J' : Type*} {j'₁ j'₂ : J'} (f : J' → J) (eq : j'₁ = j'₂) :
  (pi.equivalence_of_eq (λ j', C (f j')) eq).functor = (pi.equivalence_of_eq C (by rw eq)).functor :=
by { subst eq, refl, }

def pi.equivalence_of_eq_functor_iso {J' : Type*} {j'₁ j'₂ : J'} (f : J' → J) (eq : j'₁ = j'₂) :
  (pi.equivalence_of_eq (λ j', C (f j')) eq).functor ≅ (pi.equivalence_of_eq C (by rw eq)).functor :=
by { subst eq, refl, }

@[simp]
def pi.equivalence_of_eq_functor_iso_hom_app {J' : Type*} {j'₁ j'₂ : J'} (f : J' → J) (eq : j'₁ = j'₂)
  (X : C (f j'₁)) :
  (pi.equivalence_of_eq_functor_iso C f eq).hom.app X = eq_to_hom (by { subst eq, refl, }) :=
by { subst eq, refl, }

@[simp]
lemma pi.equivalence_of_eq_functor_iso_refl {J' : Type*} (j' : J') (f : J' → J) :
  pi.equivalence_of_eq_functor_iso C f (show j' = j', by refl) = iso.refl _ := rfl

def functor.pi_.eval_eq_of_eq {j j' : J} (eq : j = j') :
  functor.pi_.eval C j ⋙ (pi.equivalence_of_eq C eq).functor = functor.pi_.eval C j' :=
by { subst eq, refl, }

@[simps]
def functor.pi_.eval_iso_of_eq {j j' : J} (eq : j = j') :
  functor.pi_.eval C j ⋙ (pi.equivalence_of_eq C eq).functor ≅ functor.pi_.eval C j' :=
by { apply eq_to_iso, subst eq, refl, }

lemma functor.pi_.eval_iso_of_eq_refl (j : J) :
  functor.pi_.eval_iso_of_eq C (show j = j, by refl) = iso.refl _ := rfl

@[simp]
lemma functor.pi_.eval_iso_of_eq_eq_to_hom {j j' : J} (eq : j = j') (X : Π j, C j) :
  (functor.pi_.eval_iso_of_eq C eq).hom.app X = eq_to_hom (by { subst eq, refl, }) :=
by simp only [functor.pi_.eval_iso_of_eq_hom, eq_to_hom_app]

variable {C}

def functor.pi_.lift (F : Π j, E ⥤ C j) : E ⥤ Π j, C j :=
{ obj := λ X j, (F j).obj X,
  map := λ X Y f j, (F j).map f, }

end

variables (C : Type*) [category C]

@[simps]
def pi_equivalence_functors_from_discrete (J : Type*) :
  (Π (j : J), C) ≌ (discrete J ⥤ C) :=
{ functor :=
  { obj := λ F, discrete.functor F,
    map := λ F₁ F₂ f, discrete.nat_trans (by { rintro ⟨i⟩, exact f i}),
    map_id' := λ F, by { ext j, cases j, refl, },
    map_comp' := λ F₁ F₂ F₃ f g, by { ext j, cases j, refl, }, },
  inverse :=
  { obj := λ F j, F.obj (discrete.mk j),
    map := λ F₁ F₂ f j, f.app (discrete.mk j), },
  unit_iso := eq_to_iso rfl,
  counit_iso := eq_to_iso begin
    refine functor.ext (λ F, _) (λ F₁ F₂ f, _),
    { refine functor.ext _ _,
      { rintro ⟨j⟩, refl, },
      { rintros ⟨j⟩ ⟨j'⟩ f,
        have h := discrete.eq_of_hom f,
        dsimp at h,
        subst h,
        have h' : f = 𝟙 _ := by tidy,
        subst h',
        dsimp,
        simpa, }, },
    { ext j,
      cases j,
      dsimp,
      simp,
      erw id_comp, },
  end,
  functor_unit_iso_comp' := λ X, begin
    ext j,
    cases j,
    dsimp,
    simpa,
  end, }

def functor.pi.diag (J : Type*) : C ⥤ Π (j : J), C := functor.pi_.lift (λ j, 𝟭 C)

namespace limits

def is_left_adjoint_of_has_limits_of_shape_discrete (J : Type*)
  [has_limits_of_shape (discrete J) C] : is_left_adjoint (functor.pi.diag C J) :=
⟨_, const_lim_adj.comp (pi_equivalence_functors_from_discrete C J).symm.to_adjunction⟩

variable {C}

lemma pi.limit_cone_pair_of_is_left_adjoint_diag {J : Type*} [is_left_adjoint (functor.pi.diag C J)]
  (X : J → C) : limit_cone (discrete.functor X) :=
begin
  let Δ := functor.pi.diag C J,
  let R := right_adjoint Δ,
  let adj : Δ ⊣ R := is_left_adjoint.adj,
  refine limit_cone.mk (fan.mk (R.obj X) (λ j, adj.counit.app X j)) _,
  refine mk_fan_limit _ (λ s, adj.hom_equiv s.X X (λ j, s.proj j)) (λ s, _) (λ s m hm, _),
  { intro j,
    dsimp,
    simpa only [adjunction.hom_equiv_unit, assoc] using congr_arg
      (λ (f : Π j, s.X ⟶ X j), f j) (adj.compatibility (λ j, s.proj j : Δ.obj s.X ⟶ X)), },
  { dsimp,
    symmetry,
    simp only [adj.hom_equiv_apply_eq],
    ext j,
    rw ← hm,
    simpa only [adjunction.hom_equiv_counit], },
end

variable (C)

lemma has_limits_of_shape_discrete_of_is_left_adjoint_diag (J : Type*)
  [is_left_adjoint (functor.pi.diag C J)] : has_limits_of_shape (discrete J) C :=
⟨λ F, begin
  haveI : has_limit (discrete.functor (F.obj ∘ discrete.mk)),
  { exact ⟨nonempty.intro (pi.limit_cone_pair_of_is_left_adjoint_diag _)⟩, },
  exact has_limit_of_iso discrete.nat_iso_functor.symm,
end⟩

lemma has_finite_products_of_is_left_adjoint_diag
  [Π (J : Type) [fintype J], is_left_adjoint (functor.pi.diag C J)] : has_finite_products C :=
⟨λ J, by { introI, apply has_limits_of_shape_discrete_of_is_left_adjoint_diag, }⟩

end limits

end category_theory
