import for_mathlib.category_theory.localization.preadditive
import category_theory.triangulated.pretriangulated
import for_mathlib.category_theory.localization.calculus_of_fractions

noncomputable theory

namespace category_theory

open category limits triangulated

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
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (ha : W a) (hb : W b),
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (hc : W c),
  (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃))

namespace shift

variables {C D : Type*} [category C] [category D]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  {A : Type*} [add_monoid A] [has_shift C A] [W.compatible_with_shift A]

variable (C)

local attribute [reducible] discrete.add_monoidal

variable {C}

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

variable {A}

@[simp]
def localization_comm_shift (a : A) :
  shift_functor C a ⋙ L ≅ L ⋙ @shift_functor D A _ _ (shift.localization L W A) a :=
(localization.fac _ _ _).symm

/- show that the localized shift functors are additive if `A` is an add_comm_group
  and D has finite products: this is because these functors are equivalences of categories. -/

end shift

namespace triangulated

open pretriangulated

section

variables (C : Type*) [category C] [has_shift C ℤ] [has_zero_object C] [has_zero_morphisms C]

@[simps]
def contractible_triangle_functor : C ⥤ triangle C :=
{ obj := λ X, contractible_triangle C X,
  map := λ X Y f,
  { hom₁ := f,
    hom₂ := f,
    hom₃ := 0, }, }

variable {C}

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

@[simps]
def map_triangle_rotate [preadditive C] [∀ n : ℤ, functor.additive (shift_functor C n)]
  {D : Type*} [category D] [has_zero_object D] [preadditive D] [has_shift D ℤ]
  [∀ n : ℤ, functor.additive (shift_functor D n)]
  (F : triangulated_functor_struct C D) [functor.additive F.to_functor] :
  F.map_triangle ⋙ rotate D ≅ rotate C ⋙ F.map_triangle :=
nat_iso.of_components (λ T, triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
  (F.comm_shift.app _).symm (by tidy) (by tidy) begin
    dsimp,
    simp only [functor.map_id, preadditive.neg_comp, comp_id, functor.map_neg,
      preadditive.comp_neg, neg_inj],
    erw F.comm_shift.hom.naturality,
    rw F.comm_shift.inv_hom_id_app_assoc,
    refl,
  end)
(λ T₁ T₂ f, begin
  ext,
  { tidy, },
  { tidy, },
  { apply F.comm_shift.inv.naturality, },
end)

@[simps]
def map_triangle_inv_rotate [preadditive C] [∀ n : ℤ, functor.additive (shift_functor C n)]
  {D : Type*} [category D] [has_zero_object D] [preadditive D] [has_shift D ℤ]
  [∀ n : ℤ, functor.additive (shift_functor D n)]
  (F : triangulated_functor_struct C D) [functor.additive F.to_functor] :
  F.map_triangle ⋙ inv_rotate D ≅ inv_rotate C ⋙ F.map_triangle :=
begin
  calc F.map_triangle ⋙ inv_rotate D ≅ _ : (functor.left_unitor _).symm
  ... ≅ _ : iso_whisker_right (triangle_rotation C).counit_iso.symm _
  ... ≅ _ : functor.associator _ _ _
  ... ≅ _ : iso_whisker_left _ (functor.associator _ _ _).symm
  ... ≅ _ : iso_whisker_left _ (iso_whisker_right (map_triangle_rotate F).symm _)
  ... ≅ _ : iso_whisker_left _ (functor.associator _ _ _)
  ... ≅ _ : iso_whisker_left _ (iso_whisker_left _ (triangle_rotation D).unit_iso.symm)
  ... ≅ _: iso_whisker_left _ (functor.right_unitor _),
end

end

variables {C D : Type*} [category C] [category D]
  [has_zero_object C] [has_shift C ℤ] [preadditive C]
  [has_zero_object D] [has_shift D ℤ] [preadditive D]
  [∀ n : ℤ, functor.additive (shift_functor C n)] [hC : pretriangulated C]
  [∀ n : ℤ, functor.additive (shift_functor D n)]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W]
  [W.compatible_with_shift ℤ] [functor.additive L]
  (comm_shift : shift_functor C (1 : ℤ) ⋙ L ≅ L ⋙ shift_functor D (1 : ℤ))
  [left_calculus_of_fractions W] [right_calculus_of_fractions W]
  [hW₆ : W.compatible_with_triangulation]

include L comm_shift

namespace localization

@[simps]
def functor : triangulated_functor_struct C D :=
{ comm_shift := comm_shift,
  .. L }

instance : functor.additive (functor L comm_shift).to_functor := { }

include hC
@[simp]
def distinguished_triangles : set (triangle D) :=
λ T, ∃ (T' : triangle C) (e : T ≅ (functor L comm_shift).map_triangle.obj T'), T' ∈ dist_triang C

lemma isomorphic_distinguished {T₁ T₂ : triangle D} (e : T₂ ≅ T₁)
  (h : T₁ ∈ distinguished_triangles L comm_shift) : T₂ ∈ distinguished_triangles L comm_shift :=
by { rcases h with ⟨T', e', hT'⟩, exact ⟨T', e ≪≫ e',  hT'⟩, }

include W

lemma contractible_distinguished (X : D) : contractible_triangle D X ∈ distinguished_triangles L comm_shift :=
begin
  haveI := localization.ess_surj L W,
  let e := ((contractible_triangle_functor D).map_iso
    (L.obj_obj_preimage_iso X)),
  refine ⟨contractible_triangle C (L.obj_preimage X), _, contractible_distinguished _⟩,
  { refine e.symm ≪≫ triangle.mk_iso _ _ (iso.refl _) (iso.refl _) L.map_zero_object.symm _ _ _,
    tidy, },
end

lemma rotate_distinguished_triangle (T : triangle D) :
  T ∈ distinguished_triangles L comm_shift ↔ T.rotate ∈ distinguished_triangles L comm_shift :=
begin
  split,
  { intro h,
    rcases h with ⟨T', e', hT'⟩,
    refine ⟨T'.rotate, (rotate D).map_iso e' ≪≫
      ((map_triangle_rotate (functor L comm_shift)).app T'),
      pretriangulated.rot_of_dist_triangle C T' hT'⟩, },
  { intro h,
    rcases h with ⟨T', e', hT'⟩,
    refine ⟨T'.inv_rotate, ((triangle_rotation D).unit_iso.app T) ≪≫
        (inv_rotate D).map_iso e' ≪≫
        (map_triangle_inv_rotate (functor L comm_shift)).app T' ,
      pretriangulated.inv_rot_of_dist_triangle C T' hT'⟩, },
end

lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
  ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ (shift_functor D (1 : ℤ)).obj X),
    triangle.mk D f g h ∈ localization.distinguished_triangles L comm_shift :=
begin
  let f' := left_calculus_of_fractions.lift_map L W f,
  rcases pretriangulated.distinguished_cocone_triangle _ _ f' with ⟨Z, g, h, H⟩,
  refine ⟨L.obj Z, (left_calculus_of_fractions.lift_map_iso₂ L W f).hom ≫ L.map g,
    L.map h ≫ comm_shift.hom.app _ ≫ (shift_functor D (1 : ℤ)).map
      (left_calculus_of_fractions.lift_map_iso₁ L W f).inv, triangle.mk C f' g h, _, H⟩,
  dsimp,
  refine triangle.mk_iso _ _ (left_calculus_of_fractions.lift_map_iso₁ L W f)
    (left_calculus_of_fractions.lift_map_iso₂ L W f) (iso.refl _)
      (left_calculus_of_fractions.lift_map_fac L W f) (comp_id _) _,
  dsimp,
  rw [assoc, assoc, id_comp, ← functor.map_comp, iso.inv_hom_id, functor.map_id, comp_id],
end

lemma complete_distinguished_triangle_morphism (T₁ T₂ : triangle D)
  (hT₁ : T₁ ∈ distinguished_triangles L comm_shift)
  (hT₂ : T₂ ∈ distinguished_triangles L comm_shift)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ (shift_functor D 1).map a = c ≫ T₂.mor₃ :=
begin
  suffices : ∀ (T'₁ T'₂ : triangle C) (h₁ : T'₁ ∈ dist_triang C) (h₂ : T'₂ ∈ dist_triang C)
    (a : L.obj (T'₁.obj₁) ⟶ L.obj (T'₂.obj₁)) (b : L.obj (T'₁.obj₂) ⟶ L.obj (T'₂.obj₂))
    (fac : L.map T'₁.mor₁ ≫ b = a ≫ L.map T'₂.mor₁),
    ∃ (c : L.obj T'₁.obj₃ ⟶ L.obj T'₂.obj₃), L.map T'₁.mor₂ ≫ c = b ≫ L.map T'₂.mor₂ ∧
      L.map T'₁.mor₃ ≫ comm_shift.hom.app _ ≫ (shift_functor D (1 : ℤ)).map a ≫ comm_shift.inv.app _
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
    { simp only [assoc, ← comm₅, ← reassoc_of hc₂, comm_shift.inv_hom_id_app_assoc,
      ← functor.map_comp, triangle.hom_inv_id_hom₁, comp_id, ← reassoc_of comm₆,
      triangle.hom_inv_id_hom₁_assoc], }, },
  clear fac a b hT₁ hT₂ T₁ T₂,
  intros T'₁ T'₂ hT'₁ hT'₂ a b fac,
  rcases left_calculus_of_fractions.L_map_fac L W a with ⟨za, hza⟩,
  rcases left_calculus_of_fractions.ex za.s za.hs T'₂.mor₁ with ⟨sq⟩,
  rcases left_calculus_of_fractions.L_map_fac L W (b ≫ L.map sq.s') with ⟨zb, hzb⟩,
  simp only [left_calculus_of_fractions.map_zigzag] at hza hzb,
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
  let T'₃ := triangle.mk C (sq.g ≫ zb.s ≫ s) g₃ h₃,
  rcases pretriangulated.complete_distinguished_triangle_morphism T'₂ T'₃ hT'₂ H₃ za.s
    (sq.s' ≫ zb.s ≫ s) (by { dsimp, rw ← reassoc_of sq.fac, }),
  all_goals { sorry, },
end

end localization

def localization [pretriangulated C] : pretriangulated D :=
{ distinguished_triangles := localization.distinguished_triangles L comm_shift,
  isomorphic_distinguished := λ T₁ hT₁ T₂ e,
    localization.isomorphic_distinguished L comm_shift e hT₁,
  contractible_distinguished := localization.contractible_distinguished L W comm_shift,
  distinguished_cocone_triangle := λ X Y f, localization.distinguished_cocone_triangle L W comm_shift f,
  rotate_distinguished_triangle := localization.rotate_distinguished_triangle L W comm_shift,
  complete_distinguished_triangle_morphism := localization.complete_distinguished_triangle_morphism L W comm_shift, }

include W

def localization_functor [pretriangulated C] :
  @triangulated_functor C _ _ _ _ _ D _ _ _ _ _ _ (triangulated.localization L W comm_shift) :=
{ map_distinguished' := λ T hT, ⟨T, iso.refl _, hT⟩,
  .. localization.functor L comm_shift}

end triangulated

end category_theory
