import for_mathlib.algebraic_topology.homotopical_algebra.bifibrant_object
import for_mathlib.category_theory.localization.equivalence

noncomputable theory

open category_theory category_theory.limits category_theory.category category_theory

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

namespace bifibrant_replacement

def obj (X : cofibrant_object C) : bifibrant_object C :=
bifibrant_object.mk (CM5a.obj (terminal.from X.obj))

def app (X : cofibrant_object C) : X ⟶ cofibrant_object.mk (obj X).obj :=
CM5a.i (terminal.from X.obj)

instance (X : cofibrant_object C) : cofibration ((cofibrant_object.forget C).map (app X)) :=
by { dsimp [app], apply_instance, }
instance weak_eq_forget_map_app (X : cofibrant_object C) : weak_eq ((cofibrant_object.forget C).map (app X)) :=
by { dsimp [app], apply_instance, }

def app' (X : bifibrant_object C) : X ⟶ obj (cofibrant_object.mk X.obj) :=
app (cofibrant_object.mk X.obj)

def map' {X Y : cofibrant_object C} (f : X ⟶ Y) : obj X ⟶ obj Y :=
begin
  have sq : comm_sq ((cofibrant_object.forget C).map (f ≫ app Y))
    ((cofibrant_object.forget C).map (app X))
      (terminal.from (obj Y).obj) (terminal.from (obj X).obj) := by tidy,
  exact sq.lift,
end

instance (X : bifibrant_object C) : weak_eq ((bifibrant_object.forget C).map (app' X)) :=
begin
  change weak_eq ((cofibrant_object.forget C).map (app ((bifibrant_object.forget_fib C).obj X))),
  apply_instance,
end

@[reassoc]
lemma fac {X Y : cofibrant_object C} (f : X ⟶ Y) :
  app X ≫ (bifibrant_object.forget_fib C).map (map' f) = f ≫ app Y :=
by apply comm_sq.fac_left

lemma fac' {X Y : bifibrant_object C} (f : X ⟶ Y) :
  app' X ≫ map' ((bifibrant_object.forget_fib C).map f) = f ≫ app' Y :=
by apply fac

def map {X Y : cofibrant_object C} (f : X ⟶ Y) :
  bifibrant_object.homotopy_category.Q.obj (obj X) ⟶
  bifibrant_object.homotopy_category.Q.obj (obj Y) :=
bifibrant_object.homotopy_category.Q.map (map' f)

lemma map_eq {X Y : cofibrant_object C} (f : X ⟶ Y) (f' : obj X ⟶ obj Y)
  (sq : comm_sq (app X) f ((bifibrant_object.forget_fib C).map f') (app Y)) :
  map f = bifibrant_object.homotopy_category.Q.map f' :=
begin
  dsimp only [map],
  let P := path_object.some (obj Y).obj,
  rw bifibrant_object.homotopy_category.Q_map_eq_iff' P,
  have sq : comm_sq ((cofibrant_object.forget C).map (f ≫ app Y) ≫ P.σ)
    ((cofibrant_object.forget C).map (app X)) P.π
    (prod.lift ((bifibrant_object.forget C).map (map' f))
      ((bifibrant_object.forget C).map f')),
  { refine comm_sq.mk _,
    ext,
    { simpa only [pre_path_object.π, cofibrant_object.forget_map, assoc, pre_path_object.d₀σ,
        comp_id, prod.lift_fst, bifibrant_object.forget_map] using (fac f).symm, },
    { simpa only [pre_path_object.π, cofibrant_object.forget_map, assoc, comp_id,
        pre_path_object.d₁σ, prod.lift_snd, bifibrant_object.forget_map] using sq.w.symm, }, },
  exact nonempty.intro
  { h := sq.lift,
    h₀' := by simpa using congr_arg (λ f, f ≫ limits.prod.fst) sq.fac_right,
    h₁' := by simpa using congr_arg (λ f, f ≫ limits.prod.snd) sq.fac_right, },
end

end bifibrant_replacement

variable (C)

@[simps]
def bifibrant_replacement : cofibrant_object C ⥤ bifibrant_object.homotopy_category C :=
{ obj := λ X, bifibrant_object.homotopy_category.Q.obj (bifibrant_replacement.obj X),
  map := λ X Y f, bifibrant_replacement.map f,
  map_id' := λ X, begin
    rw [bifibrant_replacement.map_eq _ (𝟙 _), bifibrant_object.homotopy_category.Q.map_id],
    exact comm_sq.mk (by { simpa only [bifibrant_object.forget_fib_map, id_comp] using comp_id _,})
  end,
  map_comp' := λ X Y Z f g, begin
    rw [bifibrant_replacement.map_eq (f ≫ g)
      (bifibrant_replacement.map' f ≫ bifibrant_replacement.map' g), functor.map_comp],
    { refl, },
    { refine comm_sq.mk _,
      rw [functor.map_comp, assoc, bifibrant_replacement.fac_assoc f,
        bifibrant_replacement.fac g], },
  end, }

namespace bifibrant_replacement

variables {C} {Hocof : Type*} [category Hocof] (Lcof : cofibrant_object C ⥤ Hocof)
  [Lcof.is_localization cofibrant_object.weq]
  {Hobif : Type*} [category Hobif] (Lbif : bifibrant_object C ⥤ Hobif)
  [Lbif.is_localization bifibrant_object.weq]

@[simps]
def π : bifibrant_object.homotopy_category C ⥤ Hobif :=
bifibrant_object.homotopy_category.lift Lbif (localization.inverts_W Lbif bifibrant_object.weq)

lemma forget_comp_Lcof_inverts_weq :
  bifibrant_object.weq.is_inverted_by (bifibrant_object.forget_fib C ⋙ Lcof) :=
λ X Y f hf, by convert localization.inverts_W Lcof cofibrant_object.weq f hf

def R : cofibrant_object C ⥤ Hobif := bifibrant_replacement C ⋙ π Lbif

lemma R_inverts_weq : cofibrant_object.weq.is_inverted_by (R Lbif) := λ X Y f hf,
begin
  dsimp only [R, functor.comp_map],
  haveI : is_iso ((bifibrant_replacement C).map f),
  { dsimp only [bifibrant_replacement],
    apply bifibrant_object.homotopy_category.Q_inverts_weq,
    change model_category.weq ((bifibrant_object.forget C).map (map' f)),
    have h : weq ((cofibrant_object.forget C).map f ≫ (cofibrant_object.forget C).map (app Y)) :=
      CM2.of_comp _ _ hf weak_eq.property,
    have eq := (cofibrant_object.forget C).congr_map (fac f),
    simp only [functor.map_comp] at eq,
    rw ← eq at h,
    exact CM2.of_comp_left _ _ weak_eq.property h, },
  apply_instance,
end

lemma forget_comp_R_iso : bifibrant_object.forget_fib C ⋙ R Lbif ≅ Lbif :=
begin
  symmetry,
  refine nat_iso.of_components (λ X, localization.iso_of_W Lbif bifibrant_object.weq
    ((bifibrant_object.forget C).map (app' X)) weak_eq.property) (λ X Y f, begin
    simp only [bifibrant_object.forget_map, localization.iso_of_W_hom,
      bifibrant_object.forget_fib_map],
    rw [← Lbif.map_comp, ← fac', Lbif.map_comp],
    refl,
  end),
end

def R_comp_I'_iso {I' : Hobif ⥤ Hocof} (sq : Comm_sq (bifibrant_object.forget_fib C) Lbif Lcof I') :
  R Lbif ⋙ I' ≅ Lcof :=
begin
  symmetry,
  exact nat_iso.of_components (λ X, localization.iso_of_W Lcof cofibrant_object.weq
    (app X) weak_eq.property ≪≫ sq.iso.symm.app _) (λ X Y f, begin
    simp only [iso.trans_hom, localization.iso_of_W_hom, iso.app_hom, iso.symm_hom,
      functor.comp_map, assoc, ← Lcof.map_comp_assoc],
    simp only [← fac, functor.map_comp, assoc],
    congr' 1,
    apply sq.iso.inv.naturality,
  end),
end

/- make sq an instance parameter -/
def is_equivalence (I' : Hobif ⥤ Hocof)
  (sq : Comm_sq (bifibrant_object.forget_fib C) Lbif Lcof I') : is_equivalence I' :=
localization.lifting_is_equivalence sq bifibrant_object.weq cofibrant_object.weq
  (R Lbif) (localization.lift (R Lbif) (R_inverts_weq Lbif) Lcof)
  (R_comp_I'_iso Lcof Lbif sq) (forget_comp_R_iso Lbif)

end bifibrant_replacement

end model_category

end algebraic_topology
