import for_mathlib.algebraic_topology.homotopical_algebra.fundamental_lemma.cofibrant_object

noncomputable theory

open category_theory category_theory.limits category_theory.category

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [M : model_category C]
include M

namespace cofibrant_replacement

def obj (X : C) : cofibrant_object C :=
begin
  haveI := cofibration.mk (CM5b (initial.to X)).some_spec.some_spec.some,
  haveI := is_cofibrant.mk (CM5b (initial.to X)).some_spec.some initial_is_initial,
  exact cofibrant_object.mk (CM5b (initial.to X)).some,
end

def app (X : C) : (obj X).obj ⟶ X := (CM5b (initial.to X)).some_spec.some_spec.some_spec.some

instance (X : C) : fibration (app X) :=
fibration.mk (CM5b (initial.to X)).some_spec.some_spec.some_spec.some_spec.some.1

instance (X : C) : weak_eq (app X) :=
weak_eq.mk (CM5b (initial.to X)).some_spec.some_spec.some_spec.some_spec.some.2

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
  have sq : comm_sq (coprod.desc ((cofibrant_object.forget C).map (map' f)) f') Cyl.ι
    (app Y) (Cyl.σ ≫ app X ≫ f),
  { refine comm_sq.mk _,
    ext,
    { simpa only [precylinder.ι, cofibrant_object.forget_map, coprod.desc_comp,
        coprod.inl_desc, coprod.desc_comp_assoc, precylinder.σd₀, id_comp] using fac f, },
    { simpa only [precylinder.ι, coprod.desc_comp, coprod.inr_desc, coprod.desc_comp_assoc,
        precylinder.σd₁, id_comp] using sq.w.symm, }, },
  exact
  { h := sq.lift,
    h₀' := by simpa using congr_arg (λ f, limits.coprod.inl ≫ f) sq.fac_left,
    h₁' := by simpa using congr_arg (λ f, limits.coprod.inr ≫ f) sq.fac_left, },
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

end cofibrant_replacement

end model_category

end algebraic_topology
