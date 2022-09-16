import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma.bifibrant_object
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

instance (X : cofibrant_object C): cofibration ((cofibrant_object.forget C).map (app X)) :=
by { dsimp [app], apply_instance, }
instance (X : cofibrant_object C): weak_eq ((cofibrant_object.forget C).map (app X)) :=
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

variables {C}

variables {Hocof : Type*} [category Hocof] (Lcof : cofibrant_object C ⥤ Hocof)
  [Lcof.is_localization cofibrant_object.weq]
  {Hobif : Type*} [category Hobif] (Lbif : bifibrant_object C ⥤ Hobif)
  [Lbif.is_localization bifibrant_object.weq]

include Lbif

--@[simps]
--def π : bifibrant_object.homotopy_category C ⥤ Hobif :=
--category_theory.quotient.lift _ Lbif (λ (X Y : bifibrant_object C), begin
--  sorry,
--end)

end model_category

end algebraic_topology
