import category_theory.preadditive.additive_functor
import algebra.category.Group.preadditive
import algebra.category.Group.limits

noncomputable theory

universes v u

open category_theory category_theory.category

namespace AddCommGroup

open category_theory.limits

variables

def pi' {I : Type v} (X : I → AddCommGroup.{u}) := (AddCommGroup.of (Π i, (X i).α))

@[simps]
def cone_pi {I : Type} (X : I → AddCommGroup.{u}) : fan X := fan.mk (pi' X) (λ i,
  { to_fun := λ x, x i,
    map_zero' := by tidy,
    map_add' := by tidy, })

lemma cone_pi_is_limit {I : Type} (X : I → AddCommGroup.{u}) : is_limit (cone_pi X) :=
mk_fan_limit _
  (λ s,
    { to_fun := λ x i, s.proj i x,
      map_zero' := by tidy,
      map_add' := by tidy}) (by tidy)
  (λ s m hm, begin
    ext x i,
    dsimp,
    simpa only [← hm],
  end)

def pi_iso_pi' {I : Type} (X : I → AddCommGroup.{u}) : ∏ X ≅ pi' X :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (cone_pi_is_limit X)

variables {I : Type v} {X Y Z : I → AddCommGroup.{u}} (f : Π i, X i ⟶ Y i) (g : Π i, Y i ⟶ Z i)

@[simps]
def pi'_map : pi' X ⟶ pi' Y :=
{ to_fun := λ x i, f i (x i),
  map_zero' := by tidy,
  map_add' := by tidy, }

@[simp, reassoc]
lemma pi'_map_comp : pi'_map (λ i, f i ≫ g i) = pi'_map f ≫ pi'_map g := rfl

@[simps]
def pi'_lift {I : Type} {X : AddCommGroup.{u}} {Y : I → AddCommGroup.{u}} (φ : Π i, X ⟶ Y i) :
  X ⟶ pi' Y :=
{ to_fun := λ x i, φ i x,
  map_zero' := by tidy,
  map_add' := by tidy, }

end AddCommGroup

namespace algebra

namespace homology

def concrete_exact {X₁ X₂ X₃ : AddCommGroup.{u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) : Prop :=
∀ (x₂ : X₂) (h : f₂ x₂ = 0), ∃ (x₁ : X₁), f₁ x₁ = x₂

def concrete_exact.lift {X₁ X₂ X₃ : AddCommGroup.{u}} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
  (h : concrete_exact f₁ f₂) {x₂ : X₂} (zero : f₂ x₂ = 0) : X₁ :=
(h x₂ zero).some

@[simp]
lemma concrete_exact.lift_spec {X₁ X₂ X₃ : AddCommGroup.{u}} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
  (h : concrete_exact f₁ f₂) {x₂ : X₂} (zero : f₂ x₂ = 0) :
  f₁ (h.lift zero) = x₂ := (h x₂ zero).some_spec

lemma concrete_exact.of_iso {X₁ Y₁ X₂ Y₂ X₃ Y₃ : AddCommGroup.{u}} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃}
  (h : concrete_exact g₁ g₂) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂)
  (e₃ : X₃ ≅ Y₃) (comm₁ : f₁ ≫ e₂.hom = e₁.hom ≫ g₁) (comm₂ : f₂ ≫ e₃.hom = e₂.hom ≫ g₂) :
  concrete_exact f₁ f₂ :=
begin
  intros x₂ hx₂,
  have hy₂ : g₂ (e₂.hom x₂) = 0,
  { rw [← comp_apply, ← comm₂, comp_apply, hx₂, map_zero], },
  obtain ⟨y₁, hy₁⟩ := h _ hy₂,
  refine ⟨e₁.inv y₁, _⟩,
  have comm₁' : e₁.inv ≫ f₁ = g₁ ≫ e₂.inv,
  { rw [← cancel_mono e₂.hom, ← cancel_epi e₁.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
      e₁.hom_inv_id_assoc, comm₁], },
  rw [← comp_apply, comm₁', comp_apply, hy₁, ← comp_apply, e₂.hom_inv_id, id_apply],
end

lemma injective_iff {X₁ X₂ : AddCommGroup.{u}} (f : X₁ ⟶ X₂) :
  function.injective f ↔ ∀ (x₁ : X₁) (h : f x₁ = 0), x₁ = 0 :=
begin
  split,
  { intros h x₁ hx₁,
    apply h,
    rw [hx₁, map_zero], },
  { intros h x₁ x₂ hx,
    rw ← sub_eq_zero,
    apply h,
    rw [map_sub, hx, sub_self], },
end

lemma concrete_exact.pi' {I : Type v} {X₁ X₂ X₃ : I → AddCommGroup.{u}}
  (f₁ : Π i, X₁ i ⟶ X₂ i) (f₂ : Π i, X₂ i ⟶ X₃ i) (h : ∀ i, concrete_exact (f₁ i) (f₂ i)) :
  concrete_exact (AddCommGroup.pi'_map f₁) (AddCommGroup.pi'_map f₂) :=
begin
  intros x₂ hx₂,
  have h : ∀ (i : I), ∃ (x₁ : X₁ i), (f₁ i) x₁ = x₂ i := λ i, h i (x₂ i) (congr_fun hx₂ i),
  exact ⟨λ i, (h i).some, by { ext i, exact (h i).some_spec, }⟩,
end

variables (A : Type*) [category A] [preadditive A]

structure five_complex :=
(X₁ X₂ X₃ X₄ X₅ : A)
(f₁ : X₁ ⟶ X₂)
(f₂ : X₂ ⟶ X₃)
(f₃ : X₃ ⟶ X₄)
(f₄ : X₄ ⟶ X₅)
(h₁₂ : f₁ ≫ f₂ = 0)
(h₂₃ : f₂ ≫ f₃ = 0)
(h₃₄ : f₃ ≫ f₄ = 0)

namespace five_complex

variable {A}

@[ext]
structure hom (E E' : five_complex A) :=
(τ₁ : E.X₁ ⟶ E'.X₁)
(τ₂ : E.X₂ ⟶ E'.X₂)
(τ₃ : E.X₃ ⟶ E'.X₃)
(τ₄ : E.X₄ ⟶ E'.X₄)
(τ₅ : E.X₅ ⟶ E'.X₅)
(comm₁ : E.f₁ ≫ τ₂ = τ₁ ≫ E'.f₁)
(comm₂ : E.f₂ ≫ τ₃ = τ₂ ≫ E'.f₂)
(comm₃ : E.f₃ ≫ τ₄ = τ₃ ≫ E'.f₃)
(comm₄ : E.f₄ ≫ τ₅ = τ₄ ≫ E'.f₄)

@[simps]
instance : category (five_complex A) :=
{ hom := hom,
  id := λ E, hom.mk (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _) (by rw [id_comp,comp_id])
    (by rw [id_comp,comp_id]) (by rw [id_comp,comp_id]) (by rw [id_comp,comp_id]),
  comp := λ E E' E'' φ φ', hom.mk (φ.τ₁ ≫ φ'.τ₁) (φ.τ₂ ≫ φ'.τ₂) (φ.τ₃ ≫ φ'.τ₃)
    (φ.τ₄ ≫ φ'.τ₄) (φ.τ₅ ≫ φ'.τ₅) (by rw [assoc, reassoc_of (φ.comm₁), φ'.comm₁])
    (by rw [assoc, reassoc_of (φ.comm₂), φ'.comm₂])
    (by rw [assoc, reassoc_of (φ.comm₃), φ'.comm₃])
    (by rw [assoc, reassoc_of (φ.comm₄), φ'.comm₄]), }

variable (A)

@[simps]
def eval₁ : five_complex A ⥤ A :=
{ obj := λ E, E.X₁,
  map := λ E E' φ, φ.τ₁, }

@[simps]
def eval₂ : five_complex A ⥤ A :=
{ obj := λ E, E.X₂,
  map := λ E E' φ, φ.τ₂, }

@[simps]
def eval₃ : five_complex A ⥤ A :=
{ obj := λ E, E.X₃,
  map := λ E E' φ, φ.τ₃, }

@[simps]
def eval₄ : five_complex A ⥤ A :=
{ obj := λ E, E.X₄,
  map := λ E E' φ, φ.τ₄, }

@[simps]
def eval₅ : five_complex A ⥤ A :=
{ obj := λ E, E.X₅,
  map := λ E E' φ, φ.τ₅, }


lemma is_iso_of_isos {E E' : five_complex A} (φ : E ⟶ E') (h₁ : is_iso φ.τ₁)
  (h₂ : is_iso φ.τ₂) (h₃ : is_iso φ.τ₃) (h₄ : is_iso φ.τ₄) (h₅ : is_iso φ.τ₅) :
  is_iso φ :=
begin
  let ψ : E' ⟶ E :=
  { τ₁ := inv φ.τ₁,
    τ₂ := inv φ.τ₂,
    τ₃ := inv φ.τ₃,
    τ₄ := inv φ.τ₄,
    τ₅ := inv φ.τ₅,
    comm₁ := by { simp only [← cancel_mono (φ.τ₂), φ.comm₁, assoc, is_iso.inv_hom_id, comp_id,
      is_iso.inv_hom_id_assoc], },
    comm₂ := by { simp only [← cancel_mono (φ.τ₃), φ.comm₂, assoc, is_iso.inv_hom_id, comp_id,
      is_iso.inv_hom_id_assoc], },
    comm₃ := by { simp only [← cancel_mono (φ.τ₄), φ.comm₃, assoc, is_iso.inv_hom_id, comp_id,
      is_iso.inv_hom_id_assoc], },
    comm₄ := by { simp only [← cancel_mono (φ.τ₅), φ.comm₄, assoc, is_iso.inv_hom_id, comp_id,
      is_iso.inv_hom_id_assoc], }, },
  exact ⟨⟨ψ, ⟨by tidy, by tidy⟩⟩⟩,
end

variable {A}

structure exact (E : five_complex (AddCommGroup.{u})) : Prop :=
(ex₂ : concrete_exact E.f₁ E.f₂)
(ex₃ : concrete_exact E.f₂ E.f₃)
(ex₄ : concrete_exact E.f₃ E.f₄)

lemma concrete_comm₁ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₁ : E.X₁) : φ.τ₂ (E.f₁ x₁) = E'.f₁ (φ.τ₁ x₁) :=
by simp only [← comp_apply, φ.comm₁]

lemma concrete_comm₂ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₂ : E.X₂) : φ.τ₃ (E.f₂ x₂) = E'.f₂ (φ.τ₂ x₂) :=
by simp only [← comp_apply, φ.comm₂]

lemma concrete_comm₃ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₃ : E.X₃) : φ.τ₄ (E.f₃ x₃) = E'.f₃ (φ.τ₃ x₃) :=
by simp only [← comp_apply, φ.comm₃]

lemma concrete_comm₄ {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (x₄ : E.X₄) : φ.τ₅ (E.f₄ x₄) = E'.f₄ (φ.τ₄ x₄) :=
by simp only [← comp_apply, φ.comm₄]

lemma exact.of_iso {E E' : five_complex AddCommGroup.{u}} (φ : E ⟶ E') (hφ : is_iso φ)
  (hE' : E'.exact) : E.exact :=
begin
  let e := as_iso φ,
  constructor,
  { exact concrete_exact.of_iso hE'.ex₂ E.f₁ E.f₂ ((eval₁ _).map_iso e)
      ((eval₂ _).map_iso e) ((eval₃ _).map_iso e) φ.comm₁ φ.comm₂, },
  { exact concrete_exact.of_iso hE'.ex₃ E.f₂ E.f₃ ((eval₂ _).map_iso e)
      ((eval₃ _).map_iso e) ((eval₄ _).map_iso e) φ.comm₂ φ.comm₃, },
  { exact concrete_exact.of_iso hE'.ex₄ E.f₃ E.f₄ ((eval₃ _).map_iso e)
      ((eval₄ _).map_iso e) ((eval₅ _).map_iso e) φ.comm₃ φ.comm₄, },
end

lemma five_lemma_injective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₁ : function.surjective φ.τ₁)
  (h₂ : function.injective φ.τ₂)
  (h₄ : function.injective φ.τ₄) :
  function.injective φ.τ₃ :=
begin
  rw injective_iff at ⊢ h₄,
  intros x₃ hx₃,
  have eq₁ : E.f₃ x₃ = 0,
  { apply h₄,
    rw [concrete_comm₃, hx₃, map_zero], },
  let x₂ := hE.ex₃.lift eq₁,
  have hx₂ : E.f₂ x₂ = x₃ := hE.ex₃.lift_spec eq₁,
  let x₂' := φ.τ₂ x₂,
  have eq₂ : E'.f₂ x₂' = 0,
  { dsimp only [x₂'],
    rw [← concrete_comm₂, concrete_exact.lift_spec, hx₃], },
  let x₁' := hE'.ex₂.lift eq₂,
  obtain ⟨x₁, hx₁⟩ := h₁ x₁',
  have eq₃ : E.f₁ x₁ = x₂,
  { apply h₂,
    rw [concrete_comm₁, hx₁, concrete_exact.lift_spec], },
  rw [← hx₂, ← eq₃, ← comp_apply, E.h₁₂, AddCommGroup.zero_apply],
end

lemma five_lemma_surjective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₂ : function.surjective φ.τ₂)
  (h₄ : function.surjective φ.τ₄)
  (h₅ : function.injective φ.τ₅) :
  function.surjective φ.τ₃ :=
begin
  intro x₃',
  obtain ⟨x₄, hx₄⟩ := h₄ (E'.f₃ x₃'),
  have eq₁ : E.f₄ x₄ = 0,
  { apply h₅,
    rw [concrete_comm₄, hx₄, ← comp_apply, E'.h₃₄, AddCommGroup.zero_apply, map_zero], },
  let x₃ := hE.ex₄.lift eq₁,
  have hx₃ : E.f₃ x₃ = x₄ := by simp only [concrete_exact.lift_spec],
  let δ := x₃' - φ.τ₃ x₃,
  have eq₂ : E'.f₃ δ = 0,
  { dsimp only [δ],
    simp only [map_sub, ← concrete_comm₃, hx₃, hx₄, sub_self], },
  let ε := hE'.ex₃.lift eq₂,
  have hε : E'.f₂ ε = δ := by simp only [concrete_exact.lift_spec],
  obtain ⟨x₂, hx₂⟩ := h₂ ε,
  refine ⟨x₃ + E.f₂ x₂, _⟩,
  rw [map_add, concrete_comm₂, hx₂, hε, add_sub_cancel'_right],
end

lemma five_lemma_bijective {E E' : five_complex (AddCommGroup.{u})} (φ : E ⟶ E')
  (hE : E.exact) (hE' : E'.exact)
  (h₁ : function.bijective φ.τ₁)
  (h₂ : function.bijective φ.τ₂)
  (h₄ : function.bijective φ.τ₄)
  (h₅ : function.bijective φ.τ₅) :
  function.bijective φ.τ₃ :=
⟨five_lemma_injective φ hE hE' h₁.2 h₂.1 h₄.1, five_lemma_surjective φ hE hE' h₂.2 h₄.2 h₅.1⟩

@[simps]
def pi {I : Type} (E : I → five_complex AddCommGroup.{u}) : five_complex AddCommGroup.{u} :=
{ X₁ := ∏ (λ i, (E i).X₁),
  X₂ := ∏ (λ i, (E i).X₂),
  X₃ := ∏ (λ i, (E i).X₃),
  X₄ := ∏ (λ i, (E i).X₄),
  X₅ := ∏ (λ i, (E i).X₅),
  f₁ := limits.pi.map (λ i, (E i).f₁),
  f₂ := limits.pi.map (λ i, (E i).f₂),
  f₃ := limits.pi.map (λ i, (E i).f₃),
  f₄ := limits.pi.map (λ i, (E i).f₄),
  h₁₂ := limits.limit.hom_ext begin
    rintro ⟨i⟩,
    simp only [assoc, limits.lim_map_π, discrete.nat_trans_app, limits.lim_map_π_assoc,
      limits.zero_comp, (E i).h₁₂, limits.comp_zero],
  end,
  h₂₃ := limits.limit.hom_ext begin
    rintro ⟨i⟩,
    simp only [assoc, limits.lim_map_π, discrete.nat_trans_app, limits.lim_map_π_assoc,
      limits.zero_comp, (E i).h₂₃, limits.comp_zero],
  end,
  h₃₄ := limits.limit.hom_ext begin
    rintro ⟨i⟩,
    simp only [assoc, limits.lim_map_π, discrete.nat_trans_app, limits.lim_map_π_assoc,
      limits.zero_comp, (E i).h₃₄, limits.comp_zero],
  end, }

@[simps]
def pi' {I : Type v} (E : I → five_complex AddCommGroup.{u}) :
  five_complex AddCommGroup.{max u v} :=
{ X₁ := AddCommGroup.pi'.{v u} (λ i, (E i).X₁),
  X₂ := AddCommGroup.pi'.{v u} (λ i, (E i).X₂),
  X₃ := AddCommGroup.pi'.{v u} (λ i, (E i).X₃),
  X₄ := AddCommGroup.pi'.{v u} (λ i, (E i).X₄),
  X₅ := AddCommGroup.pi'.{v u} (λ i, (E i).X₅),
  f₁ := AddCommGroup.pi'_map (λ i, (E i).f₁),
  f₂ := AddCommGroup.pi'_map (λ i, (E i).f₂),
  f₃ := AddCommGroup.pi'_map (λ i, (E i).f₃),
  f₄ := AddCommGroup.pi'_map (λ i, (E i).f₄),
  h₁₂ := by simpa only [← AddCommGroup.pi'_map_comp, (E _).h₁₂],
  h₂₃ := by simpa only [← AddCommGroup.pi'_map_comp, (E _).h₂₃],
  h₃₄ := by simpa only [← AddCommGroup.pi'_map_comp, (E _).h₃₄], }

lemma pi'_exact {I : Type v} (E : I → five_complex AddCommGroup.{u})
  (h : ∀ i, (E i).exact) : (pi' E).exact :=
⟨concrete_exact.pi' _ _ (λ i, (h i).ex₂),
  concrete_exact.pi' _ _ (λ i, (h i).ex₃),
  concrete_exact.pi' _ _ (λ i, (h i).ex₄)⟩

@[simps]
def pi'_lift {I : Type} {E : five_complex AddCommGroup.{u}}
  {E' : I → five_complex AddCommGroup.{u}} (φ : Π i, E ⟶ E' i) :
  E ⟶ pi' E' :=
{ τ₁ := AddCommGroup.pi'_lift (λ i, (φ i).τ₁),
  τ₂ := AddCommGroup.pi'_lift (λ i, (φ i).τ₂),
  τ₃ := AddCommGroup.pi'_lift (λ i, (φ i).τ₃),
  τ₄ := AddCommGroup.pi'_lift (λ i, (φ i).τ₄),
  τ₅ := AddCommGroup.pi'_lift (λ i, (φ i).τ₅),
  comm₁ := begin
    ext x i,
    simp only [comp_apply, AddCommGroup.pi'_lift_apply, pi'_f₁, AddCommGroup.pi'_map_apply],
    simp only [← comp_apply, (φ i).comm₁],
  end,
  comm₂ := begin
    ext x i,
    simp only [comp_apply, AddCommGroup.pi'_lift_apply, pi'_f₂, AddCommGroup.pi'_map_apply],
    simp only [← comp_apply, (φ i).comm₂],
  end,
  comm₃ := begin
    ext x i,
    simp only [comp_apply, AddCommGroup.pi'_lift_apply, pi'_f₃, AddCommGroup.pi'_map_apply],
    simp only [← comp_apply, (φ i).comm₃],
  end,
  comm₄ := begin
    ext x i,
    simp only [comp_apply, AddCommGroup.pi'_lift_apply, pi'_f₄, AddCommGroup.pi'_map_apply],
    simp only [← comp_apply, (φ i).comm₄],
  end, }

end five_complex

end homology

end algebra

namespace category_theory

namespace functor

open algebra.homology

@[simps]
def map_five_complex {C D : Type*} [category C] [category D] [preadditive C]
  [preadditive D] (F : C ⥤ D) [F.additive] :
  five_complex C ⥤ five_complex D :=
{ obj := λ E,
  { X₁ := F.obj E.X₁,
    X₂ := F.obj E.X₂,
    X₃ := F.obj E.X₃,
    X₄ := F.obj E.X₄,
    X₅ := F.obj E.X₅,
    f₁ := F.map E.f₁,
    f₂ := F.map E.f₂,
    f₃ := F.map E.f₃,
    f₄ := F.map E.f₄,
    h₁₂ := by { rw [← F.map_comp, E.h₁₂, F.map_zero], },
    h₂₃ := by { rw [← F.map_comp, E.h₂₃, F.map_zero], },
    h₃₄ := by { rw [← F.map_comp, E.h₃₄, F.map_zero], }, },
  map := λ E E' φ,
  { τ₁ := F.map φ.τ₁,
    τ₂ := F.map φ.τ₂,
    τ₃ := F.map φ.τ₃,
    τ₄ := F.map φ.τ₄,
    τ₅ := F.map φ.τ₅,
    comm₁ := by simp only [← F.map_comp, φ.comm₁],
    comm₂ := by simp only [← F.map_comp, φ.comm₂],
    comm₃ := by simp only [← F.map_comp, φ.comm₃],
    comm₄ := by simp only [← F.map_comp, φ.comm₄], }, }

end functor

end category_theory
