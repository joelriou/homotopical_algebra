import for_mathlib.algebraic_topology.homotopical_algebra.bifibrant_replacement
import for_mathlib.algebraic_topology.homotopical_algebra.cofibrant_replacement

noncomputable theory

open category_theory category_theory.limits category_theory.category category_theory

namespace algebraic_topology

namespace model_category

variables {C : Type*} [category C] [model_category C]

variables {Hcof : Type*} [category Hcof] (Lcof : cofibrant_object C ⥤ Hcof)
  [Lcof.is_localization cofibrant_object.weq]

lemma Lcof_map_surjective_both_fibrant (X Y : cofibrant_object C)
  [is_fibrant X.obj] [is_fibrant Y.obj] :
  function.surjective (@category_theory.functor.map _ _ _ _ Lcof X Y) := λ f,
begin
  unfreezingI { rcases X with ⟨X, Xcof⟩, rcases Y with ⟨Y, Ycof⟩, },
  let X' := bifibrant_object.mk X,
  let Y' := bifibrant_object.mk Y,
  let f' : (bifibrant_object.forget_fib C ⋙ Lcof).obj X' ⟶
    (bifibrant_object.forget_fib C ⋙ Lcof).obj Y' := f,
  refine ⟨(bifibrant_object.forget_fib C).map
    ((bifibrant_object.forget_fib C ⋙ Lcof).preimage f'), _⟩,
  rw [← functor.comp_map, functor.image_preimage],
end

lemma Lcof_map_eq_iff_bifibrant_Q_map_eq {X Y : bifibrant_object C} (f₁ f₂ : X ⟶ Y) :
  Lcof.map ((bifibrant_object.forget_fib C).map f₁) =
    Lcof.map ((bifibrant_object.forget_fib C).map f₂) ↔
  bifibrant_object.homotopy_category.Q.map f₁ = bifibrant_object.homotopy_category.Q.map f₂ :=
begin
  erw ← functor.map_eq_iff_of_nat_iso (Lbif_comp_Hobif_to_Hocof_iso Lcof
    bifibrant_object.homotopy_category.Q),
  dsimp only [functor.comp_map],
  apply (Hobif_to_Hocof Lcof bifibrant_object.homotopy_category.Q).map_eq_iff,
end

lemma Lcof_map_surjective (X Y : cofibrant_object C) [is_fibrant Y.obj] :
  function.surjective (@category_theory.functor.map _ _ _ _ Lcof X Y) := λ g,
begin
  let X' := cofibrant_object.mk (CM5a.obj (terminal.from X.obj)),
  let f : X ⟶ X' := CM5a.i (terminal.from X.obj),
  have hf : cofibrant_object.weq f,
  { change model_category.weq (CM5a.i (terminal.from X.obj)),
    exact weak_eq.property, },
  haveI : is_iso (Lcof.map f) := is_iso_Lcof_map' Lcof f hf,
  rcases Lcof_map_surjective_both_fibrant Lcof _ _ (inv (Lcof.map f) ≫ g) with ⟨φ, hφ⟩,
  exact ⟨f ≫ φ, by rw [Lcof.map_comp, hφ, is_iso.hom_inv_id_assoc]⟩,
end

lemma Lcof_map_eq_iff'_both_fibrant {X Y : cofibrant_object C} [is_fibrant X.obj] [is_fibrant Y.obj]
  (P : path_object Y.obj) (f₁ f₂ : X ⟶ Y) :
  Lcof.map f₁ = Lcof.map f₂ ↔ nonempty (model_category.right_homotopy P.pre f₁ f₂) :=
begin
  unfreezingI { rcases X with ⟨X, Xcof⟩, rcases Y with ⟨Y, Ycof⟩, },
  let g₁ : bifibrant_object.mk X ⟶ bifibrant_object.mk Y := f₁,
  let g₂ : bifibrant_object.mk X ⟶ bifibrant_object.mk Y := f₂,
  let P' : path_object (bifibrant_object.mk Y).obj := P,
  erw ← bifibrant_object.homotopy_category.Q_map_eq_iff' P' g₁ g₂,
  erw ← functor.map_eq_iff_of_nat_iso (Lbif_comp_Hobif_to_Hocof_iso Lcof
    bifibrant_object.homotopy_category.Q) g₁ g₂,
  dsimp only [functor.comp_map],
  apply (Hobif_to_Hocof Lcof bifibrant_object.homotopy_category.Q).map_eq_iff,
end

lemma Lcof_map_eq_iff' {X Y : cofibrant_object C} [is_fibrant Y.obj] (P : path_object Y.obj)
  (f₁ f₂ : X ⟶ Y) :
  Lcof.map f₁ = Lcof.map f₂ ↔ nonempty (model_category.right_homotopy P.pre f₁ f₂) :=
begin
  split,
  { intro h,
    let X' := CM5a.obj (terminal.from X.obj),
    let i : X.obj ⟶ X' := CM5a.i (terminal.from X.obj),
    have sq₁ : comm_sq ((cofibrant_object.forget C).map f₁) i (terminal.from Y.obj) (terminal.from X') := by tidy,
    have sq₂ : comm_sq ((cofibrant_object.forget C).map f₂) i (terminal.from Y.obj) (terminal.from X') := by tidy,
    let g₁ : cofibrant_object.mk X' ⟶ Y := sq₁.lift,
    let g₂ : cofibrant_object.mk X' ⟶ Y := sq₂.lift,
    have eq : Lcof.map g₁ = Lcof.map g₂,
    { let j : X ⟶ cofibrant_object.mk X' := i,
      haveI : weak_eq ((cofibrant_object.forget C).map j) := by { dsimp [j], apply_instance, },
      haveI := is_iso_Lcof_map Lcof j,
      simp only [← cancel_epi (Lcof.map j), ← functor.map_comp],
      convert h,
      exacts [sq₁.fac_left, sq₂.fac_left], },
    rw Lcof_map_eq_iff'_both_fibrant Lcof P g₁ g₂ at eq,
    convert nonempty.intro (eq.some.comp_left i),
    exacts [sq₁.fac_left.symm, sq₂.fac_left.symm], },
  { intro h,
    change (cofibrant_replacement.π Lcof).map (cofibrant_object.homotopy_category.Q.map f₁) =
      (cofibrant_replacement.π Lcof).map (cofibrant_object.homotopy_category.Q.map f₂),
    congr' 1,
    apply category_theory.quotient.sound,
    exact cofibrant_object.right_homotopy.trans_closure.mk
      (cofibrant_object.right_homotopy.mk P h.some), },
end

lemma Lcof_map_eq_iff {X Y : cofibrant_object C} [is_fibrant Y.obj] (Cyl : cylinder X.obj)
  (f₁ f₂ : X ⟶ Y) :
  Lcof.map f₁ = Lcof.map f₂ ↔ nonempty (left_homotopy Cyl.pre f₁ f₂) :=
begin
  let P := path_object.some Y.obj,
  rw Lcof_map_eq_iff' Lcof P,
  split,
  { exact λ h, nonempty.intro (h.some.to_left_homotopy Cyl), },
  { exact λ h, nonempty.intro (h.some.to_right_homotopy P), },
end

namespace fundamental_lemma

variables {Ho : Type*} [category Ho] (L : C ⥤ Ho) [L.is_localization weq] (C)

variables {C}

lemma map_surjective (X Y : C) [is_cofibrant X] [is_fibrant Y] :
  function.surjective (@category_theory.functor.map _ _ _ _ L X Y) :=
begin
  let Y' := CM5b.obj (initial.to Y),
  suffices : function.surjective (@category_theory.functor.map _ _ _ _ L X Y'),
  { intro g,
    let p : Y' ⟶ Y := CM5b.p (initial.to Y),
    haveI := localization.inverts L weq p weak_eq.property,
    rcases this (g ≫ inv (L.map p)) with ⟨φ, hφ⟩,
    exact ⟨φ ≫ p, by rw [L.map_comp, hφ, assoc, is_iso.inv_hom_id, comp_id]⟩, },
  suffices : ∀ (A B : cofibrant_object C) [is_fibrant B.obj], function.surjective
    (@category_theory.functor.map _ _ _ _ (cofibrant_object.forget C ⋙ L) A B),
  { exact this (cofibrant_object.mk X) (cofibrant_object.mk Y'), },
  simp only [← functor.function_surjective_map_iff_of_iso (Lcof_comp_Hocof_to_Ho_iso Lcof' L)],
  introsI A B hB,
  exact function.surjective.comp (Hocof_to_Ho Lcof' L).map_surjective
    (Lcof_map_surjective Lcof' A B),
end

instance {X Y : C} (f : X ⟶ Y) [weak_eq f] : is_iso (L.map f) :=
localization.inverts L weq f weak_eq.property

lemma map_eq_of_left_homotopy {X Y : C} {f₁ f₂ : X ⟶ Y} {P : precylinder X}
  (h : left_homotopy P f₁ f₂) : L.map f₁ = L.map f₂ :=
begin
  simp only [← h.h₀, ← h.h₁, L.map_comp],
  congr' 1,
  simp only [← cancel_mono (L.map P.σ), ← L.map_comp, P.σd₀, P.σd₁],
end

lemma map_eq_iff {X Y : C} [is_cofibrant X] [is_fibrant Y] (Cyl : cylinder X) (f₁ f₂ : X ⟶ Y) :
  L.map f₁ = L.map f₂ ↔ nonempty (left_homotopy Cyl.pre f₁ f₂) :=
begin
  split,
  { intro h,
    let Y' := CM5b.obj (initial.to Y),
    let i : Y' ⟶ Y := CM5b.p (initial.to Y),
    have sq₁ : comm_sq (initial.to Y') (initial.to X) i f₁ := by tidy,
    have sq₂ : comm_sq (initial.to Y') (initial.to X) i f₂ := by tidy,
    let g₁ : cofibrant_object.mk X ⟶ cofibrant_object.mk Y' := sq₁.lift,
    let g₂ : cofibrant_object.mk X ⟶ cofibrant_object.mk Y' := sq₂.lift,
    haveI := localization.inverts L weq i weak_eq.property,
    rw [← sq₁.fac_right, ← sq₂.fac_right, L.map_comp, L.map_comp,
      cancel_mono] at h,
    change (cofibrant_object.forget C ⋙ L).map g₁ =
      (cofibrant_object.forget C ⋙ L).map g₂ at h,
    rw ← functor.map_eq_iff_of_nat_iso (Lcof_comp_Hocof_to_Ho_iso Lcof' L) at h,
    have h' := (Hocof_to_Ho Lcof' L).map_injective h,
    let Cyl' : cylinder (cofibrant_object.mk X).obj := Cyl,
    rw Lcof_map_eq_iff Lcof' Cyl' g₁ g₂ at h',
    rw [← sq₁.fac_right, ← sq₂.fac_right],
    exact nonempty.intro (h'.some.comp_right i), },
  { intro h,
    exact map_eq_of_left_homotopy L h.some, },
end

lemma map_eq_iff' {X Y : C} [is_cofibrant X] [is_fibrant Y] (P : path_object Y) (f₁ f₂ : X ⟶ Y) :
  L.map f₁ = L.map f₂ ↔ nonempty (right_homotopy P.pre f₁ f₂) :=
begin
  let Cyl := cylinder.some X,
  rw map_eq_iff L Cyl f₁ f₂,
  split,
  { exact λ h, nonempty.intro (h.some.to_right_homotopy P), },
  { exact λ h, nonempty.intro (h.some.to_left_homotopy Cyl), },
end

end fundamental_lemma

end model_category

end algebraic_topology
