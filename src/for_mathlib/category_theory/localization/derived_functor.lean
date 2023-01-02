import for_mathlib.category_theory.localization.predicate
import category_theory.adjunction.limits

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace functor

variables {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃]
  (F : C₁ ⥤ C₂)

instance [is_equivalence F] :
  is_equivalence ((whiskering_left _ _ C₃).obj F) := sorry

end functor

namespace structured_arrow

variables {C₀ C₁ C₂ C₃ : Type*} [category C₀] [category C₁] [category C₂] [category C₃]
  (X₃ X₃' : C₃) (f : X₃' ⟶ X₃) (F : C₁ ⥤ C₂) (eF : C₁ ≌ C₂)
  (G G' G'' : C₂ ⥤ C₃) (τ τ' : G ⟶ G') (τ'' : G' ⟶ G'') (eG : G ≅ G')

@[simps]
def whiskering_left : structured_arrow X₃ (F ⋙ G) ⥤ structured_arrow X₃ G :=
{ obj := λ X₂, mk X₂.hom,
  map := λ X₂ X₂' φ, hom_mk (F.map φ.right) (w φ), }

def whiskering_left_equivalence :
equivalence (structured_arrow X₃ (eF.functor ⋙ G)) (structured_arrow X₃ G) :=
{ functor := whiskering_left X₃ eF.functor G,
  inverse := begin
    refine _ ⋙ whiskering_left X₃ eF.inverse (eF.functor ⋙ G),
    sorry,
  end,
  unit_iso := sorry,
  counit_iso := sorry, }

instance [is_equivalence F] : is_equivalence (whiskering_left X₃ F G) :=
is_equivalence.of_equivalence (whiskering_left_equivalence X₃ (functor.as_equivalence F) G)

variables {X₃ X₃'}

@[simps]
def precomp : structured_arrow X₃ G ⥤ structured_arrow X₃' G :=
{ obj := λ X₂, mk (f ≫ X₂.hom),
  map := λ X₂ X₂' φ, hom_mk φ.right (by tidy), }

--instance [is_iso f] : is_equivalence (precomp f G) := sorry

variables {G G'} (X₃)

@[simps]
def postcomp : structured_arrow X₃ G ⥤ structured_arrow X₃ G' :=
{ obj := λ X₂, mk (X₂.hom ≫ τ.app X₂.right),
  map := λ X₂ X₂' φ, hom_mk φ.right begin
    dsimp,
    simp only [assoc, ← τ.naturality, w_assoc φ],
  end, }

variable (G)

@[simps]
def postcomp_id : postcomp X₃ (𝟙 G) ≅ 𝟭 _ :=
nat_iso.of_components (λ X, structured_arrow.iso_mk (iso.refl _) (by tidy)) (by tidy)

variable {G}

@[simps]
def postcomp_comp : postcomp X₃ τ ⋙ postcomp X₃ τ'' ≅
  postcomp X₃ (τ ≫ τ'') :=
nat_iso.of_components (λ X, structured_arrow.iso_mk (iso.refl _) (by tidy)) (by tidy)

@[simps]
def postcomp_iso_of_eq (h : τ = τ') : postcomp X₃ τ ≅ postcomp X₃ τ' :=
nat_iso.of_components (λ X, structured_arrow.iso_mk (iso.refl _)
  (by { dsimp, rw [G'.map_id, comp_id, h], })) (by tidy)

@[simps]
def postcomp_iso : equivalence (structured_arrow X₃ G) (structured_arrow X₃ G') :=
{ functor := postcomp X₃ eG.hom,
  inverse := postcomp X₃ eG.inv,
  unit_iso := (postcomp_id X₃ G).symm ≪≫ postcomp_iso_of_eq X₃ _ _ eG.hom_inv_id.symm ≪≫
    (postcomp_comp _ _ _ _).symm,
  counit_iso := postcomp_comp _ _ _ _ ≪≫ postcomp_iso_of_eq X₃ _ _ eG.inv_hom_id ≪≫
    (postcomp_id X₃ G'), }

instance [is_iso τ] : is_equivalence (postcomp X₃ τ) :=
is_equivalence.of_equivalence (postcomp_iso X₃ (as_iso τ))

end structured_arrow

namespace functor

variables {C D H : Type*} [category C] [category D] [category H]
  (F : C ⥤ D) (L : C ⥤ H) (W : morphism_property C) [L.is_localization W]

class has_right_derived_functor : Prop :=
(has_initial' : limits.has_initial (structured_arrow F ((whiskering_left C _ D).obj W.Q)))

lemma has_right_derived_functor_iff :
  has_right_derived_functor F W ↔
    limits.has_initial (structured_arrow F ((whiskering_left C H D).obj L)) :=
begin
  let Φ :=
    structured_arrow.whiskering_left F ((whiskering_left _ _ _).obj
      (localization.equivalence_from_model L W).functor)
      ((whiskering_left C _ D).obj W.Q),
  let Φ' := structured_arrow.postcomp F ((whiskering_left _ _ D).map_iso
    (localization.Q_comp_equivalence_from_model_functor_iso L W)).inv,
  let e := as_equivalence (Φ' ⋙ Φ),
  split,
  { intro h,
    haveI := h.has_initial',
    exact adjunction.has_colimits_of_shape_of_equivalence (Φ' ⋙ Φ), },
  { introI,
    exact ⟨adjunction.has_colimits_of_shape_of_equivalence (inv (Φ' ⋙ Φ))⟩, },
end

lemma has_right_derived_functor.has_initial [has_right_derived_functor F W] :
  limits.has_initial (structured_arrow F ((whiskering_left C H D).obj L)) :=
(has_right_derived_functor_iff F L W).1 infer_instance

def has_right_derived_functor.initial [has_right_derived_functor F W] :
  (structured_arrow F ((whiskering_left C H D).obj L)) :=
begin
  haveI := has_right_derived_functor.has_initial F L W,
  exact limits.initial _,
end

def derived_functor [has_right_derived_functor F W] : H ⥤ D :=
(has_right_derived_functor.initial F L W).right

include L
def derived_functor_α [has_right_derived_functor F W] : F ⟶ L ⋙ F.derived_functor L W :=
(has_right_derived_functor.initial F L W).hom

end functor

end category_theory
