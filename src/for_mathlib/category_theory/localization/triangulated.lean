import for_mathlib.category_theory.localization.preadditive
import category_theory.triangulated.triangulated
import for_mathlib.category_theory.localization.calculus_of_fractions
import for_mathlib.category_theory.preadditive.equivalence
import for_mathlib.category_theory.triangulated.triangulated
import for_mathlib.category_theory.functor.shift

noncomputable theory

namespace category_theory

open category limits pretriangulated

class morphism_property.compatible_with_shift {C : Type*} [category C]
  (W : morphism_property C) (A : Type*) [add_monoid A] [has_shift C A] : Prop :=
(translate : ∀ (a : A), W.inverse_image (shift_functor C a) = W)

lemma morphism_property.compatible_with_shift.iff {C : Type*} [category C]
  (W : morphism_property C) {A : Type*} [add_monoid A] [has_shift C A]
  [h : W.compatible_with_shift A]
  {X Y : C} (f : X ⟶ Y) (a : A) : W ((shift_functor C a).map f) ↔ W f :=
by { conv_rhs { rw ← h.translate a }, refl, }

class morphism_property.compatible_with_triangulation {C : Type*} [category C]
  [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [∀ (n : ℤ), (shift_functor C n).additive] [pretriangulated C]
  (W : morphism_property C) : Prop :=
(condition : ∀ (T₁ T₂ : triangle C) (h₁ : T₁ ∈ dist_triang C) (h₂ : T₂ ∈ dist_triang C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (ha : W a) (hb : W b)
  (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁),
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (hc : W c),
  (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃))

namespace shift
local attribute [reducible] discrete.add_monoidal

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  {A : Type*} [add_monoid A] [has_shift C A] [W.compatible_with_shift A]

include L W

lemma comp_localization_inverts (a : A) : W.is_inverted_by (shift_functor C a ⋙ L) :=
λ X Y f hf,
begin
  dsimp,
  rw ← morphism_property.compatible_with_shift.iff W f a at hf,
  exact localization.inverts L W _ hf,
end

variable (A)

def localization : has_shift D A :=
begin
  let F := λ (a : A), localization.lift (shift_functor C a ⋙ L)
    (shift.comp_localization_inverts L W a) L,
  let H : Π (a : A), Comm_sq (shift_functor C a) L L (F a) :=
    λ a, ⟨localization.lifting.iso L W (shift_functor C a ⋙ L) (F a)⟩,
  let H₀ : Comm_sq (𝟭 C) L L (𝟭 D) := Comm_sq.horiz_refl L,
  let ε : 𝟭 D ≅ F 0 := localization.lift_nat_iso' H₀ (H 0) W (shift_functor_zero C A).symm,
  let μ : Π (a₁ a₂ : A), F a₁ ⋙ F a₂ ≅ F (a₁ + a₂) := λ a₁ a₂,
    localization.lifting_comp_iso (H a₁) (H a₂) (H (a₁+a₂))
      (shift_functor_add C a₁ a₂).symm W W,
  let e : Π {a₁ a₂ : A} (h : a₁ = a₂), shift_functor C a₁ ≅ shift_functor C a₂ :=
    λ a₁ a₂ h, eq_to_iso (by rw h),
  have Heq : Π {a b : A} (h : a = b) (X : C), (H a).iso.inv.app X = eq_to_hom (by rw h) ≫ (H b).iso.inv.app X ≫ eq_to_hom (by rw h),
  { intros a b h X,
    subst h,
    simp only [eq_to_hom_refl, id_comp, comp_id], },
  have associativity : ∀ (a₁ a₂ a₃ : A),
    eq_to_hom (by rw functor.assoc) ≫ (μ a₁ a₂).hom ◫ 𝟙 (F a₃) ≫ (μ (a₁ + a₂) a₃).hom ≫ eq_to_hom (congr_arg F (add_assoc a₁ a₂ a₃)) =
    𝟙 (F a₁) ◫ (μ a₂ a₃).hom ≫ (μ a₁ (a₂ + a₃)).hom,
  { intros a₁ a₂ a₃,
    dsimp only [μ],
    simp only [eq_to_hom_refl, id_comp, ← localization.lift_nat_trans'_id (H a₃) W,
      ← localization.lift_nat_trans'_id (H a₁) W, localization.lifting_comp_iso_hom,
      localization.hcomp_lift_nat_trans', localization.comp_lift_nat_trans', localization.comp_lift_nat_trans'_assoc],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    have this : (shift_functor_add C a₁ a₂).symm.hom ◫ 𝟙 (shift_functor C a₃) ≫ (shift_functor_add C (a₁ + a₂) a₃).symm.hom =
      eq_to_hom (functor.assoc _ _ _) ≫ (𝟙 (shift_functor C a₁) ◫ (shift_functor_add C a₂ a₃).symm.hom ≫ (shift_functor_add C a₁ (a₂ + a₃)).symm.hom) ≫
        eq_to_hom (by rw (add_assoc a₁ a₂ a₃)),
    { ext X,
      dsimp,
      simp only [obj_μ_app, eq_to_iso.inv, id_comp, assoc, μ_inv_hom_app, comp_id, functor.map_id, eq_to_hom_app, eq_to_hom_map], },
    simp only [nat_trans.comp_app, eq_to_hom_app, localization.lift_nat_trans'_app,
      localization.lift_nat_trans'_app, Comm_sq.horiz_comp_assoc_iso, assoc, this,
      Heq (add_assoc a₁ a₂ a₃), eq_to_hom_trans, L.map_comp, eq_to_hom_map, eq_to_hom_refl,
      eq_to_hom_trans_assoc, id_comp, comp_id], },
  have left_unitality : ∀ (a : A), ε.hom ◫ 𝟙 (F a) ≫ (μ 0 a).hom =
    eq_to_hom (by simpa only [zero_add]),
  { intro a,
    dsimp [ε, μ],
    rw ← localization.lift_nat_trans'_id (H a) W,
    erw localization.lifting_comp_iso_nat_trans_compatibility H₀ (H a) (H (0 + a)) (H 0) (H a) (H (0 + a))
      ((functor.right_unitor _) ≪≫ e (zero_add a).symm) (shift_functor_add C 0 a).symm W W
      (shift_functor_zero C A).inv (𝟙 _) (𝟙 _) begin
        ext X,
        dsimp,
        simp only [eq_to_hom_map, obj_ε_app, eq_to_iso.inv, eq_to_hom_app, id_comp, assoc,
          μ_inv_hom_app],
      end,
    simp only [localization.lifting_comp_iso_hom, localization.lift_nat_trans'_id, comp_id],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    rw [localization.lift_nat_trans'_app, eq_to_hom_app, Heq (zero_add a), iso.trans_hom,
      nat_trans.comp_app, functor.right_unitor_hom_app, eq_to_iso.hom, eq_to_hom_app],
    erw id_comp,
    simpa only [eq_to_hom_map, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp,
      Comm_sq.refl_horiz_comp_iso, iso.hom_inv_id_app_assoc], },
  have right_unitality : ∀ (a : A), 𝟙 (F a) ◫ ε.hom ≫ (μ a 0).hom =
    eq_to_hom (by simpa only [add_zero]),
  { intro a,
    dsimp only [ε, μ],
    rw ← localization.lift_nat_trans'_id (H a) W,
    rw localization.lift_nat_iso'_hom,
    erw localization.lifting_comp_iso_nat_trans_compatibility (H a) H₀ (H (a + 0)) (H a) (H 0) (H (a + 0))
      ((functor.right_unitor _) ≪≫ e (add_zero a).symm) (shift_functor_add C a 0).symm W W
      (𝟙 _) (shift_functor_zero C A).inv (𝟙 _) begin
        ext X,
        dsimp,
        simp only [ε_app_obj, eq_to_iso.inv, functor.map_id, assoc, comp_id, μ_inv_hom_app, eq_to_hom_app, id_comp,
          eq_to_hom_map],
      end,
    simp only [localization.lifting_comp_iso_hom, localization.lift_nat_trans'_id, comp_id],
    refine localization.nat_trans_ext L W _ _ (λ X, _),
    rw [localization.lift_nat_trans'_app, eq_to_hom_app, Heq (add_zero a), iso.trans_hom,
      nat_trans.comp_app, functor.right_unitor_hom_app, eq_to_iso.hom, eq_to_hom_app],
    erw id_comp,
    simpa only [eq_to_hom_map, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp,
      Comm_sq.horiz_comp_refl_iso, iso.hom_inv_id_app_assoc], },
  exact has_shift_mk D A
  { F := F,
    ε := ε,
    μ := μ,
    associativity := λ a₁ a₂ a₃ X, begin
      have h := congr_app (associativity a₁ a₂ a₃) X,
      simp only [nat_trans.comp_app, nat_trans.hcomp_app, eq_to_hom_app, eq_to_hom_refl,
        nat_trans.id_app, id_comp, functor.map_id, comp_id] at h,
      erw id_comp at h,
      exact h,
    end,
    left_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, nat_trans.hcomp_id_app,
      iso.refl_hom] using congr_app (left_unitality a) X,
    right_unitality := λ a X, by simpa only [iso.trans_hom, nat_trans.comp_app,
      eq_to_iso.hom, eq_to_hom_app, nat_iso.hcomp, iso.refl_hom,
      nat_trans.id_hcomp_app] using congr_app (right_unitality a) X, },
end

omit L

instance : has_shift W.localization A := shift.localization W.Q W A

variable {A}

@[simp]
def localization_comm_shift (a : A) :
  shift_functor C a ⋙ L ≅ L ⋙ @shift_functor D A _ _ (shift.localization L W A) a :=
(localization.fac _ _ _).symm

end shift

namespace pretriangulated

variables {C D : Type*} [category C] [category D]
  [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ n : ℤ, functor.additive (shift_functor C n)] [hC : pretriangulated C]
  [∀ n : ℤ, functor.additive (shift_functor D n)]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  [W.compatible_with_shift ℤ] [functor.additive L]
  [L.has_comm_shift ℤ]
  [left_calculus_of_fractions W] [right_calculus_of_fractions W]
  [hW₆ : W.compatible_with_triangulation]

include L

namespace localization

@[simps]
def functor : triangulated_functor_struct C D :=
{ comm_shift := L.comm_shift_iso 1,
  .. L }

@[simps]
def functor_iso_L : (functor L).to_functor ≅ L :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

instance : functor.additive (functor L).to_functor := { }

include hC
@[simp]
def distinguished_triangles : set (triangle D) :=
λ T, ∃ (T' : triangle C) (e : T ≅ (functor L).map_triangle.obj T'), T' ∈ dist_triang C

lemma isomorphic_distinguished {T₁ T₂ : triangle D} (e : T₂ ≅ T₁)
  (h : T₁ ∈ distinguished_triangles L) : T₂ ∈ distinguished_triangles L :=
by { rcases h with ⟨T', e', hT'⟩, exact ⟨T', e ≪≫ e',  hT'⟩, }

include W

lemma contractible_distinguished (X : D) : contractible_triangle X ∈ distinguished_triangles L :=
begin
  haveI := localization.ess_surj L W,
  let e := ((contractible_triangle_functor D).map_iso
    (L.obj_obj_preimage_iso X)),
  refine ⟨contractible_triangle (L.obj_preimage X), _, contractible_distinguished _⟩,
  { refine e.symm ≪≫ triangle.mk_iso _ _ (iso.refl _) (iso.refl _) L.map_zero_object.symm _ _ _,
    tidy, },
end

lemma rotate_distinguished_triangle (T : triangle D) :
  T ∈ distinguished_triangles L ↔ T.rotate ∈ distinguished_triangles L :=
begin
  split,
  { intro h,
    rcases h with ⟨T', e', hT'⟩,
    refine ⟨T'.rotate, (rotate D).map_iso e' ≪≫
      ((map_triangle_rotate (functor L)).app T'),
      pretriangulated.rot_of_dist_triangle C T' hT'⟩, },
  { intro h,
    rcases h with ⟨T', e', hT'⟩,
    refine ⟨T'.inv_rotate, ((triangle_rotation D).unit_iso.app T) ≪≫
        (inv_rotate D).map_iso e' ≪≫
        (map_triangle_inv_rotate (functor L)).app T' ,
      pretriangulated.inv_rot_of_dist_triangle C T' hT'⟩, },
end

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
  ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor D (1 : ℤ)).obj X),
    triangle.mk f g h ∈ localization.distinguished_triangles L :=
begin
  let f' := left_calculus_of_fractions.lift_map L W f,
  rcases pretriangulated.distinguished_cocone_triangle _ _ f' with ⟨Z, g, h, H⟩,
  refine ⟨L.obj Z, (left_calculus_of_fractions.lift_map_iso₂ L W f).hom ≫ L.map g,
    L.map h ≫ (L.comm_shift_iso 1).hom.app _ ≫ (shift_functor D (1 : ℤ)).map
      (left_calculus_of_fractions.lift_map_iso₁ L W f).inv, triangle.mk f' g h, _, H⟩,
  dsimp,
  refine triangle.mk_iso _ _ (left_calculus_of_fractions.lift_map_iso₁ L W f)
    (left_calculus_of_fractions.lift_map_iso₂ L W f) (iso.refl _)
      (left_calculus_of_fractions.lift_map_fac L W f) (comp_id _) _,
  dsimp,
  rw [assoc, assoc, id_comp, ← functor.map_comp, iso.inv_hom_id, functor.map_id, comp_id],
end

include hW₆

lemma complete_distinguished_triangle_morphism (T₁ T₂ : triangle D)
  (hT₁ : T₁ ∈ distinguished_triangles L)
  (hT₂ : T₂ ∈ distinguished_triangles L)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ (shift_functor D 1).map a = c ≫ T₂.mor₃ :=
begin
  suffices : ∀ (T'₁ T'₂ : triangle C) (h₁ : T'₁ ∈ dist_triang C) (h₂ : T'₂ ∈ dist_triang C)
    (a : L.obj (T'₁.obj₁) ⟶ L.obj (T'₂.obj₁)) (b : L.obj (T'₁.obj₂) ⟶ L.obj (T'₂.obj₂))
    (fac : L.map T'₁.mor₁ ≫ b = a ≫ L.map T'₂.mor₁),
    ∃ (c : L.obj T'₁.obj₃ ⟶ L.obj T'₂.obj₃), L.map T'₁.mor₂ ≫ c = b ≫ L.map T'₂.mor₂ ∧
      L.map T'₁.mor₃ ≫ (L.comm_shift_iso 1).hom.app _ ≫ (shift_functor D (1 : ℤ)).map a ≫
        (L.comm_shift_iso 1).inv.app _
        = c ≫ L.map T'₂.mor₃,
  { rcases hT₁ with ⟨T'₁, e₁, hT'₁⟩,
    rcases hT₂ with ⟨T'₂, e₂, hT'₂⟩,
    have comm₁ := e₁.inv.comm₁,
    have comm₂ := e₂.hom.comm₁,
    have comm₃ := e₁.hom.comm₂,
    have comm₄ := e₂.hom.comm₂,
    have comm₅ := e₂.inv.comm₃,
    have comm₆ := e₁.hom.comm₃,
    dsimp at comm₁ comm₂ comm₃ comm₄ comm₅ comm₆,
    rcases this T'₁ T'₂ hT'₁ hT'₂ (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁)
      (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by rw [reassoc_of comm₁, reassoc_of fac, assoc, assoc, comm₂])
      with ⟨c, ⟨hc₁, hc₂⟩⟩,
    refine ⟨e₁.hom.hom₃ ≫ c ≫ e₂.inv.hom₃, ⟨_, _⟩⟩,
    { simp only [reassoc_of comm₃, reassoc_of hc₁, ← reassoc_of comm₄,
        triangle.hom_inv_id_hom₃, comp_id, triangle.hom_inv_id_hom₂_assoc], },
    { simp only [assoc, ← comm₅, ← reassoc_of hc₂, (L.comm_shift_iso (1 : ℤ)).inv_hom_id_app_assoc,
      ← functor.map_comp, triangle.hom_inv_id_hom₁, comp_id, ← reassoc_of comm₆,
      triangle.hom_inv_id_hom₁_assoc], }, },
  clear fac a b hT₁ hT₂ T₁ T₂,
  intros T'₁ T'₂ hT'₁ hT'₂ a b fac,
  rcases left_calculus_of_fractions.L_map_fac L W a with ⟨za, hza⟩,
  rcases left_calculus_of_fractions.ex za.s za.hs T'₂.mor₁ with ⟨sq⟩,
  rcases left_calculus_of_fractions.L_map_fac L W (b ≫ L.map sq.s') with ⟨zb, hzb⟩,
  simp only [left_calculus_of_fractions.map_roof] at hza hzb,
  have hsq := L.congr_map sq.fac,
  simp only [L.map_comp] at hsq,
  haveI := localization.inverts L W zb.s zb.hs,
  rcases (left_calculus_of_fractions.L_map_eq_iff L W (za.f ≫ sq.g ≫ zb.s) (T'₁.mor₁ ≫ zb.f)).mp
    (by simp only [← cancel_mono (inv (L.map zb.s)), assoc, L.map_comp, ← hzb,
        is_iso.hom_inv_id, comp_id, reassoc_of fac, hsq, reassoc_of hza,
        is_iso.inv_hom_id_assoc]) with ⟨Y₃, s, hs, fac'⟩,
  simp only [assoc] at fac',
  rcases pretriangulated.distinguished_cocone_triangle _ _ (sq.g ≫ zb.s ≫ s)
    with ⟨Z₃, g₃, h₃, H₃⟩,
  let T'₃ := triangle.mk (sq.g ≫ zb.s ≫ s) g₃ h₃,
  have comm : T'₂.mor₁ ≫ sq.s' ≫ zb.s ≫ s = za.s ≫ sq.g ≫ zb.s ≫ s,
  { dsimp, rw ← reassoc_of sq.fac, },
  have h₂ : W (sq.s' ≫ zb.s ≫ s) := left_calculus_of_fractions.comp _ _ _ sq.hs'
    (left_calculus_of_fractions.comp _ _ _ zb.hs hs),
  rcases morphism_property.compatible_with_triangulation.condition T'₂ T'₃ hT'₂ H₃
    za.s (sq.s' ≫ zb.s ≫ s) za.hs h₂ comm with ⟨α, hα₀, ⟨hα₁, hα₂⟩⟩,
  let φ : T'₂ ⟶ T'₃ := triangle_morphism.mk za.s (sq.s' ≫ zb.s ≫ s) α comm hα₁ hα₂,
  let F := (functor L),
  haveI := localization.inverts L W _ za.hs,
  haveI := localization.inverts L W _ h₂,
  haveI := localization.inverts L W _ hα₀,
  rcases pretriangulated.complete_distinguished_triangle_morphism T'₁ T'₃ hT'₁ H₃ za.f
    (zb.f ≫ s) fac'.symm with ⟨c, ⟨hc₁, hc₂⟩⟩,
  refine ⟨L.map c ≫ inv (L.map α), ⟨_, _⟩⟩,
  { simp only [← cancel_mono (L.map α), assoc, is_iso.inv_hom_id, comp_id, ← L.map_comp, hα₁, hc₁],
    simp only [L.map_comp, reassoc_of hzb, is_iso.inv_hom_id_assoc], },
  { simp only [hza, functor.map_comp, assoc],
    erw ← (L.comm_shift_iso (1 : ℤ)).hom.naturality_assoc,
    dsimp,
    simp only [← L.map_comp_assoc, hc₂, assoc,
      ← cancel_mono ((L.comm_shift_iso (1 : ℤ)).hom.app T'₂.obj₁), iso.inv_hom_id_app_assoc,
      ← cancel_mono ((shift_functor D (1 : ℤ)).map (L.map za.s))],
    simp only [← functor.map_comp, is_iso.inv_hom_id, functor.map_id, comp_id],
    erw ← (L.comm_shift_iso (1 : ℤ)).hom.naturality,
    erw ← L.map_comp_assoc,
    simp only [hα₂, L.map_comp, assoc, is_iso.inv_hom_id_assoc], },
end

end localization

include hW₆

@[derive category, derive preadditive, derive has_zero_object]
def localization := D

instance : has_shift (localization L W) ℤ := (infer_instance : has_shift D ℤ)

instance (n : ℤ) : functor.additive (shift_functor (localization L W) n) :=
by { dsimp [localization], apply_instance, }

instance : pretriangulated (localization L W) :=
{ distinguished_triangles := localization.distinguished_triangles L,
  isomorphic_distinguished := λ T₁ hT₁ T₂ e,
    localization.isomorphic_distinguished L e hT₁,
  contractible_distinguished := localization.contractible_distinguished L W,
  distinguished_cocone_triangle := λ X Y f, localization.distinguished_cocone_triangle L W f,
  rotate_distinguished_triangle := localization.rotate_distinguished_triangle L W,
  complete_distinguished_triangle_morphism :=
    localization.complete_distinguished_triangle_morphism L W, }

instance [is_triangulated C] : is_triangulated (localization L W) :=
is_triangulated.mk'
(λ X₁' X₂' X₃' u₁₂' u₂₃', begin
  haveI := localization.ess_surj L W,
  let Y₁' := L.obj_preimage X₁',
  let X₂ := L.obj_preimage X₂',
  let Y₃' := L.obj_preimage X₃',
  let e₁ : L.obj Y₁' ≅ X₁' := functor.obj_obj_preimage_iso L X₁',
  let e₂ : L.obj X₂ ≅ X₂' := functor.obj_obj_preimage_iso L X₂',
  let e₃ : L.obj Y₃' ≅ X₃' := functor.obj_obj_preimage_iso L X₃',
  let y₁₂' : L.obj Y₁' ⟶ L.obj X₂ := e₁.hom ≫ u₁₂' ≫ e₂.inv,
  let y₂₃' : L.obj X₂ ⟶ L.obj Y₃' := e₂.hom ≫ u₂₃' ≫ e₃.inv,
  obtain ⟨⟨X₁, s₁, u₁₂, hs₁⟩, hz₁⟩ := right_calculus_of_fractions.L_map_fac L W y₁₂',
  obtain ⟨⟨X₃, u₂₃, s₂, hs₂⟩, hz₂⟩ := left_calculus_of_fractions.L_map_fac L W y₂₃',
  haveI := localization.inverts L W _ hs₁,
  haveI := localization.inverts L W _ hs₂,
  dsimp [right_calculus_of_fractions.map_roof] at hz₁,
  dsimp [left_calculus_of_fractions.map_roof] at hz₂,
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := pretriangulated.distinguished_cocone_triangle _ _ u₁₂,
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := pretriangulated.distinguished_cocone_triangle _ _ u₂₃,
  obtain ⟨Z₁₃, v₁₃, w₁₃, h₁₃⟩ := pretriangulated.distinguished_cocone_triangle _ _ (u₁₂ ≫ u₂₃),
  let H := (is_triangulated.octahedron_axiom rfl h₁₂ h₂₃ h₁₃).some,
  refine ⟨L.obj X₁, L.obj X₂, L.obj X₃, L.obj Z₁₂, L.obj Z₂₃, L.obj Z₁₃,
    L.map u₁₂, L.map u₂₃, e₁.symm ≪≫ (as_iso (L.map s₁)).symm, e₂.symm,
    e₃.symm ≪≫ (as_iso (L.map s₂)), _, _, _, _, ⟨_, by refl, h₁₂⟩,
    _, _, ⟨_, by refl, h₂₃⟩,
    L.map v₁₃, L.map w₁₃ ≫ (L.comm_shift_iso 1).hom.app X₁,
      ⟨_, _, h₁₃⟩, _⟩,
  { dsimp,
    rw [assoc, ← hz₁, e₁.inv_hom_id_assoc], },
  { dsimp,
    rw [← cancel_mono (inv (L.map s₂)), assoc, assoc, assoc, is_iso.hom_inv_id, comp_id, ← hz₂,
      e₂.inv_hom_id_assoc], },
  { refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
    { dsimp, simp only [comp_id, functor.map_comp, id_comp], },
    { dsimp, simp only [comp_id, id_comp], },
    { dsimp, simp only [functor.map_id, comp_id, id_comp], }, },
  have comm₁₂ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₁.comm₂,
  have comm₁₃ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₁.comm₃,
  have comm₂₂ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₂.comm₂,
  have comm₂₃ := congr_arg (λ (f : _ ⟶ _), L.map f) H.triangle_morphism₂.comm₃,
  dsimp at comm₁₂ comm₁₃ comm₂₂ comm₂₃,
  simp only [L.map_comp, functor.map_id, id_comp, comp_id] at comm₁₂ comm₁₃ comm₂₂ comm₂₃,
  refine ⟨⟨L.map H.m₁, L.map H.m₃, comm₁₂, _, comm₂₂, _, _⟩⟩,
  { dsimp,
    rw reassoc_of comm₁₃, },
  { dsimp,
    rw [← reassoc_of comm₂₃, assoc],
    erw ← nat_trans.naturality,
    refl, },
  refine ⟨_, _, H.mem⟩,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
  { dsimp, simp only [comp_id, id_comp], },
  { dsimp, simp only [comp_id, id_comp], },
  { dsimp, simp only [assoc, functor.map_id, comp_id, functor.map_comp, id_comp],
    erw ← nat_trans.naturality, refl, },
end)

include W

def localization_functor : triangulated_functor C (localization L W) :=
{ map_distinguished' := λ T hT, ⟨T, iso.refl _, hT⟩,
  .. localization.functor L }

variables [morphism_property.stable_under_finite_products W] [has_finite_products C]

omit L
include hC

instance additive_shift_localization (n : ℤ) :
  functor.additive (shift_functor W.localization n) := infer_instance

instance W_Q_has_comm_shift : W.Q.has_comm_shift ℤ := sorry
--  (shift.localization_comm_shift W.Q W (1 : ℤ))))

instance localization_pretriangulated : pretriangulated W.localization :=
(infer_instance : pretriangulated (localization W.Q W))

instance localization_triangulated [is_triangulated C] : is_triangulated W.localization :=
(infer_instance : is_triangulated (localization W.Q W))

end pretriangulated

end category_theory
