import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma.cofibrant_object
import for_mathlib.category_theory.localization.equivalence

noncomputable theory

open category_theory category_theory.limits category_theory.category category_theory

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

namespace cofibrant_replacement

def obj (X : C) : cofibrant_object C :=
cofibrant_object.mk (CM5b.obj (initial.to X))

def app (X : C) : (obj X).obj ⟶ X := CM5b.p (initial.to X)

def app' (X : cofibrant_object C) : obj X.obj ⟶ X := app X.obj

instance (X : C) : fibration (app X) := by { dsimp [app], apply_instance, }
instance (X : C) : weak_eq (app X) := by { dsimp [app], apply_instance, }

def map' {X Y : C} (f : X ⟶ Y) : obj X ⟶ obj Y :=
begin
  have sq : comm_sq (initial.to (obj Y).obj) (initial.to (obj X).obj) (app Y) (app X ≫ f) :=
    by tidy,
  exact sq.lift,
end

@[reassoc]
lemma fac {X Y : C} (f : X ⟶ Y) : (cofibrant_object.forget C).map (map' f) ≫ app Y =
  app X ≫ f :=
by apply comm_sq.fac_right

lemma fac' {X Y : cofibrant_object C} (f : X ⟶ Y) :
  map' ((cofibrant_object.forget C).map f) ≫ app' Y = app' X ≫ f :=
by apply fac

def map {X Y : C} (f : X ⟶ Y) : cofibrant_object.homotopy_category.Q.obj (obj X) ⟶
  cofibrant_object.homotopy_category.Q.obj (obj Y) :=
  cofibrant_object.homotopy_category.Q.map (map' f)

lemma map_eq {X Y : C} (f : X ⟶ Y) (f' : obj X ⟶ obj Y)
  (sq : comm_sq (app X) ((cofibrant_object.forget C).map f') f (app Y)) :
  map f = cofibrant_object.homotopy_category.Q.map f' :=
begin
  apply category_theory.quotient.sound,
  apply cofibrant_object.right_homotopy.trans_closure.mk,
  let Cyl := cylinder.some (obj X).obj,
  suffices : left_homotopy Cyl.pre (map' f) f',
  { exact cofibrant_object.right_homotopy.mk (path_object.some (obj Y).obj)
      (this.to_right_homotopy _), },
  have sq' : comm_sq (coprod.desc ((cofibrant_object.forget C).map (map' f)) f') Cyl.ι
    (app Y) (Cyl.σ ≫ app X ≫ f),
  { refine comm_sq.mk _,
    ext,
    { simpa only [precylinder.ι, cofibrant_object.forget_map, coprod.desc_comp,
        coprod.inl_desc, coprod.desc_comp_assoc, precylinder.σd₀, id_comp] using fac f, },
    { simpa only [precylinder.ι, coprod.desc_comp, coprod.inr_desc, coprod.desc_comp_assoc,
        precylinder.σd₁, id_comp] using sq.w.symm, }, },
  exact
  { h := sq'.lift,
    h₀' := by simpa using congr_arg (λ f, limits.coprod.inl ≫ f) sq'.fac_left,
    h₁' := by simpa using congr_arg (λ f, limits.coprod.inr ≫ f) sq'.fac_left, },
end

end cofibrant_replacement

variable (C)

@[simps]
def cofibrant_replacement : C ⥤ cofibrant_object.homotopy_category C :=
{ obj := λ X, cofibrant_object.homotopy_category.Q.obj (cofibrant_replacement.obj X),
  map := λ X Y f, cofibrant_replacement.map f,
  map_id' := λ X, begin
    rw [cofibrant_replacement.map_eq _ (𝟙 _), cofibrant_object.homotopy_category.Q.map_id],
    exact comm_sq.mk (by erw [id_comp, comp_id]),
  end,
  map_comp' := λ X Y Z f g, begin
    rw [cofibrant_replacement.map_eq (f ≫ g)
      (cofibrant_replacement.map' f ≫ cofibrant_replacement.map' g), functor.map_comp],
    { refl, },
    { refine comm_sq.mk _,
      rw [functor.map_comp, assoc, cofibrant_replacement.fac g,
        cofibrant_replacement.fac_assoc f], },
  end, }

namespace cofibrant_replacement

variable {C}

lemma weq_iff {X Y : C} (f : X ⟶ Y) (f' : obj X ⟶ obj Y)
  (sq : comm_sq (app X) ((cofibrant_object.forget C).map f') f (app Y)) :
  weq f ↔ cofibrant_object.weq f' :=
begin
  split,
  { intro hf,
    have h : weq (app X ≫ f) := CM2.of_comp (app X) f weak_eq.property hf,
    rw sq.w at h,
    exact CM2.of_comp_right _ _ weak_eq.property h, },
  { intro hf',
    have h : weq (app X ≫ f),
    { rw sq.w,
      exact CM2.of_comp _ _ hf' weak_eq.property, },
    exact CM2.of_comp_left _ _ weak_eq.property h, },
end

lemma weq_eq_inverse_image_homotopy_category_weq :
  model_category.weq =
cofibrant_object.homotopy_category.weq.inverse_image (cofibrant_replacement C) :=
begin
  ext X Y f,
  dsimp only [morphism_property.inverse_image, cofibrant_replacement, map],
  rw cofibrant_object.homotopy_category.weq_Q_map_iff,
  exact weq_iff _ _ (comm_sq.mk (fac f).symm),
end

variables {Hocof : Type*} [category Hocof] (Lcof : cofibrant_object C ⥤ Hocof)
  [Lcof.is_localization cofibrant_object.weq]

include Lcof

@[simps]
def π : cofibrant_object.homotopy_category C ⥤ Hocof :=
category_theory.quotient.lift _ Lcof (λ (X Y : cofibrant_object C), begin
  let Y' : cofibrant_object C := cofibrant_object.mk (CM5a.obj (terminal.from Y.obj)),
  let φ : Y ⟶ Y' := CM5a.i (terminal.from Y.obj),
  intros f₁ f₂ h,
  haveI : is_iso (Lcof.map φ) := localization.inverts_W Lcof cofibrant_object.weq φ
    weak_eq.property,
  simp only [← cancel_mono (Lcof.map φ), ← Lcof.map_comp],
  induction h with g₁ g₂ h g₁ g₂ g₃ H₁₂ H₂₃ h₁₂ h₂₃,
  { rcases h.comp_right φ with ⟨P, H⟩,
    let Cyl := cylinder.some X.obj,
    let I' := cofibrant_object.mk Cyl.I,
    let s : I' ⟶ X := Cyl.σ,
    haveI : is_iso (Lcof.map s) := localization.inverts_W Lcof cofibrant_object.weq s
      weak_eq.property,
    let h' := H.some.to_left_homotopy Cyl,
    let ψ : I' ⟶ Y' := h'.h,
    let d₀ : X ⟶ I' := Cyl.d₀,
    let d₁ : X ⟶ I' := Cyl.d₁,
    have eq₀ : d₀ ≫ ψ = g₁ ≫ φ := h'.h₀,
    have eq₁ : d₁ ≫ ψ = g₂ ≫ φ := h'.h₁,
    simp only [← eq₀, ← eq₁, Lcof.map_comp],
    congr' 1,
    simp only [← cancel_mono (Lcof.map s), ← Lcof.map_comp],
    congr' 1,
    exact Cyl.σd₀.trans Cyl.σd₁.symm, },
  { exact h₁₂.trans h₂₃, },
end)

lemma π_inverts_weq : cofibrant_object.homotopy_category.weq.is_inverted_by (π Lcof) := λ X Y f hf,
begin
  rcases cofibrant_object.homotopy_category.Q_map_surjective _ _ f with ⟨g, hg⟩,
  dsimp only at hg,
  subst hg,
  simp only [cofibrant_object.homotopy_category.Q_map, quotient.functor_map,
    π_map, quot.lift_on_mk],
  apply localization.inverts_W Lcof cofibrant_object.weq g,
  exact (cofibrant_object.homotopy_category.weq_Q_map_iff g).mp hf,
end

omit Lcof

variables {Ho : Type*} [category Ho] (L : C ⥤ Ho) [L.is_localization weq]

lemma forget_comp_L_inverts_weq :
  cofibrant_object.weq.is_inverted_by (cofibrant_object.forget C ⋙ L) :=
λ X Y f hf, begin
  dsimp only [functor.comp_map],
  exact localization.inverts_W L weq ((cofibrant_object.forget C).map f) hf,
end

def R : C ⥤ Hocof := cofibrant_replacement C ⋙ π Lcof

lemma R_inverts_weq : weq.is_inverted_by (R Lcof) := λ X Y f hf,
begin
  dsimp only [R, functor.comp_map],
  exact (π_inverts_weq Lcof) _
    (by simpa only [weq_eq_inverse_image_homotopy_category_weq] using hf),
end

lemma forget_comp_R_iso : cofibrant_object.forget C ⋙ R Lcof ≅ Lcof :=
nat_iso.of_components (λ X, localization.iso_of_W Lcof cofibrant_object.weq (app' X)
  (by { dsimp [app'], exact weak_eq.property, }))
(λ X Y f, begin
  simp only [functor.comp_map, cofibrant_object.forget_map, localization.iso_of_W_hom],
  rw [← Lcof.map_comp, ← fac' f, Lcof.map_comp],
  refl,
end)

def R_comp_I'_iso {I' : Hocof ⥤ Ho} (sq : Comm_sq (cofibrant_object.forget C) Lcof L I') :
  R Lcof ⋙ I' ≅ L :=
nat_iso.of_components (λ X, sq.iso.app _ ≪≫
  localization.iso_of_W L model_category.weq (app X) weak_eq.property)
(λ X Y f, begin
  simp only [functor.comp_map, iso.trans_hom, iso.app_hom, localization.iso_of_W_hom, assoc,
    ← L.map_comp],
  simp only [← fac, L.map_comp, ← assoc],
  congr' 1,
  apply sq.iso.hom.naturality,
end)

def is_equivalence (I' : Hocof ⥤ Ho)
  (sq : Comm_sq (cofibrant_object.forget C) Lcof L I') : is_equivalence I' :=
localization.lifting_is_equivalence sq cofibrant_object.weq model_category.weq
  (R Lcof) (localization.lift (R Lcof) (R_inverts_weq Lcof) L)
  (R_comp_I'_iso Lcof L sq) (forget_comp_R_iso Lcof)

end cofibrant_replacement

end model_category

end algebraic_topology
