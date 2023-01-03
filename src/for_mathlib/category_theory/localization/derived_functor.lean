import for_mathlib.category_theory.localization.predicate
import category_theory.adjunction.limits
import category_theory.is_connected
import for_mathlib.category_theory.localization.products

noncomputable theory

open category_theory category_theory.category

namespace category_theory

@[simps]
instance localization.lifting.of_comp {C D E : Type*} [category C] [category D] [category E]
  (L : C ⥤ D) (W : morphism_property C) [L.is_localization W] (F : D ⥤ E) :
  localization.lifting L W (L ⋙ F) F := ⟨iso.refl _⟩

section

variables (C : Type*) [category C]

inductive obj_rel : C → C → Prop
| of_hom ⦃X Y : C⦄ (f : X ⟶ Y) : obj_rel X Y

def connected_components := quot (obj_rel C)

variable {C}

def to_connected_components (X : C) : connected_components C :=
quot.mk _ X

variable (C)

class is_preconnected' : Prop :=
(subsingleton_connected_components : subsingleton (connected_components C))

attribute [instance] is_preconnected'.subsingleton_connected_components

class is_connected' extends is_preconnected' C : Prop :=
[is_nonempty : nonempty C]

lemma connected_components.nat_trans_from_eq {D : Type*} [category D]
  (X Y : D) (α : (functor.const C).obj X ⟶ (functor.const C).obj Y)
  (j j' : C) (h : to_connected_components j = to_connected_components j') :
    α.app j = (α.app j' : X ⟶ Y) :=
begin
  let β : C → (X ⟶ Y) := λ j, α.app j,
  let l : connected_components C → (X ⟶ Y),
  { refine quot.lift β _,
    rintro x y ⟨f⟩,
    dsimp [β],
    have eq := α.naturality f,
    dsimp at eq,
    rw [id_comp, comp_id] at eq,
    rw eq, },
  have hl : ∀ (j : C), α.app j = l (to_connected_components j) := λ j, rfl,
  simp only [hl, h],
end

lemma nat_trans_from_is_preconnected' {D : Type*} [category D]
  [is_preconnected' C] (X Y : D) (α : (functor.const C).obj X ⟶ (functor.const C).obj Y)
  (j j' : C) : α.app j = (α.app j' : X ⟶ Y) :=
begin
  apply connected_components.nat_trans_from_eq,
  apply subsingleton.elim,
end

end

namespace morphism_property

variables {C : Type*} [category C] (W : morphism_property C)

class multiplicative : Prop :=
(contains_identities : W.contains_identities)
(comp [] : W.stable_under_composition)

section

variable [multiplicative W]

instance contains_identities_of_multiplicative : W.contains_identities :=
multiplicative.contains_identities

include W
@[protected, nolint unused_arguments]
structure category :=
(obj : C)

variable {W}

@[ext]
structure category.hom (X Y : W.category) :=
(f : X.obj ⟶ Y.obj)
(hf : W f)

@[simps]
instance : category W.category :=
{ hom := category.hom,
  id := λ X,
  { f := 𝟙 _,
    hf := contains_identities.id _ _, },
  comp := λ X Y Z φ φ',
  { f := φ.f ≫ φ'.f,
    hf := multiplicative.comp W φ.f φ'.f φ.hf φ'.hf, }, }

end

end morphism_property

namespace functor

variables (C₁ C₂ C₃ : Type*) [category C₁] [category C₂] [category C₃]
  (F : C₁ ⥤ C₂)

@[simps]
def whiskering_left_id : (whiskering_left C₁ C₁ C₃).obj (𝟭 C₁) ≅ 𝟭 _ :=
nat_iso.of_components (functor.left_unitor) (by tidy)

variables {C₁ C₂}

@[simps]
def equivalence_whiskering_left (e : C₁ ≌ C₂) : (C₂ ⥤ C₃) ≌ C₁ ⥤ C₃ :=
{ functor := (whiskering_left _ _ _).obj e.functor,
  inverse := (whiskering_left _ _ _).obj e.inverse,
  unit_iso := (whiskering_left_id _ _).symm ≪≫ (whiskering_left _ _ C₃).map_iso e.counit_iso.symm,
  counit_iso := (whiskering_left _ _ C₃).map_iso e.unit_iso.symm ≪≫ whiskering_left_id _ _,
  functor_unit_iso_comp' := λ F, begin
    ext X,
    dsimp,
    simp only [id_comp, comp_id, ← F.map_comp, equivalence.counit_inv_functor_comp, F.map_id],
  end, }

instance [is_equivalence F] :
  is_equivalence ((whiskering_left _ _ C₃).obj F) :=
is_equivalence.of_equivalence (equivalence_whiskering_left C₃ (as_equivalence F))

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
  {F : C ⥤ D} (RF : H ⥤ D) {L : C ⥤ H} (α : F ⟶ L ⋙ RF) (W : morphism_property C) [L.is_localization W]

class is_right_derived_functor : Prop :=
(is_initial [] : nonempty (limits.is_initial (structured_arrow.mk α :
  structured_arrow F ((whiskering_left C H D).obj L))))

namespace is_right_derived_functor

variables (RF₁ RF₂ : H ⥤ D) (α₁ : F ⟶ L ⋙ RF₁) (α₂ : F ⟶ L ⋙ RF₂)
  [RF₁.is_right_derived_functor α₁] [RF₂.is_right_derived_functor α₂]

def uniq' : (structured_arrow.mk α₁ :
  structured_arrow F ((whiskering_left C H D).obj L)) ≅ structured_arrow.mk α₂ :=
limits.is_colimit.cocone_point_unique_up_to_iso
    (is_right_derived_functor.is_initial α₁).some
    (is_right_derived_functor.is_initial α₂).some

/- It should be slightly better to define natural transformation `RF₁ ⟶ G` for any `G` equipped
with a nat_trans, and then construct the isomorphism `uniq` using universal properties for
both `RF₁` and `RF₂`. -/

def uniq : RF₁ ≅ RF₂ :=
(structured_arrow.proj _ _).map_iso (uniq' _ _ α₁ α₂)

@[simp]
def uniq_hom_app_comm (X : C) : α₁.app X ≫ (uniq _ _ α₁ α₂).hom.app (L.obj X) = α₂.app X :=
congr_app (structured_arrow.w (uniq' _ _ α₁ α₂).hom) X

@[simp]
def uniq_inv_app_comm (X : C) : α₂.app X ≫ (uniq _ _ α₁ α₂).inv.app (L.obj X) = α₁.app X :=
congr_app (structured_arrow.w (uniq' _ _ α₁ α₂).inv) X

end is_right_derived_functor

variables (F)

class has_right_derived_functor : Prop :=
(has_initial' : limits.has_initial (structured_arrow F ((whiskering_left C _ D).obj W.Q)))

variable (L)

lemma has_right_derived_functor_iff :
  has_right_derived_functor F W ↔
    limits.has_initial (structured_arrow F ((whiskering_left C H D).obj L)) :=
begin
  let Φ := structured_arrow.whiskering_left F ((whiskering_left _ _ _).obj
      (localization.equivalence_from_model L W).functor)
      ((whiskering_left C _ D).obj W.Q),
  let Φ' := structured_arrow.postcomp F ((whiskering_left _ _ D).map_iso
    (localization.Q_comp_equivalence_from_model_functor_iso L W)).inv,
  split,
  { intro h,
    haveI := h.has_initial',
    exact adjunction.has_colimits_of_shape_of_equivalence (Φ' ⋙ Φ), },
  { introI,
    exact ⟨adjunction.has_colimits_of_shape_of_equivalence (inv (Φ' ⋙ Φ))⟩, },
end

lemma is_right_derived_functor.has_right_derived_functor [RF.is_right_derived_functor α] :
  F.has_right_derived_functor W :=
begin
  rw F.has_right_derived_functor_iff L W,
  exact limits.is_initial.has_initial (is_right_derived_functor.is_initial α).some,
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

def right_derived_functor [has_right_derived_functor F W] : H ⥤ D :=
(has_right_derived_functor.initial F L W).right

def right_derived_functor_α [has_right_derived_functor F W] :
  F ⟶ L ⋙ F.right_derived_functor L W :=
(has_right_derived_functor.initial F L W).hom

instance right_derived_functor_is_right_derived_functor [has_right_derived_functor F W] :
  (F.right_derived_functor L W).is_right_derived_functor (F.right_derived_functor_α L W) :=
⟨⟨begin
  haveI := has_right_derived_functor.has_initial F L W,
  exact limits.is_initial.of_iso limits.initial_is_initial
    (structured_arrow.iso_mk (iso.refl _) (by tidy)),
end⟩⟩

end functor

section

variables {C D : Type*} [category C] [category D]
  (W : morphism_property C) (W' : morphism_property D)

structure localizor_morphism :=
(functor : C ⥤ D)
(mapW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), W' (functor.map f))

namespace localizor_morphism

variables {W W'} (Φ : localizor_morphism W W') [morphism_property.multiplicative W]
  [morphism_property.multiplicative W']

@[simps]
def induced_functor : W.category ⥤ W'.category :=
{ obj := λ X, ⟨Φ.functor.obj X.obj⟩,
  map := λ X Y φ,
  { f := Φ.functor.map φ.f,
    hf := Φ.mapW φ.f φ.hf, }, }

@[derive category]
def right_resolution (Y : D) := structured_arrow (⟨Y⟩ : W'.category) Φ.induced_functor

@[simps]
def right_resolution.mk {Y : D} (X : C) (f : Y ⟶ Φ.functor.obj X) (hf : W' f) :
  Φ.right_resolution Y :=
structured_arrow.mk (⟨f, hf⟩ : (⟨Y⟩ : W'.category) ⟶ Φ.induced_functor.obj ⟨X⟩)

end localizor_morphism

end

namespace right_derivability_structure

variables {C₀ C H : Type*} [category C] [category C₀] [category H]
  {W₀ : morphism_property C₀}
  {W : morphism_property C} (L : C ⥤ H) [L.is_localization W] (Φ : localizor_morphism W₀ W)
  [morphism_property.multiplicative W₀] [morphism_property.multiplicative W]

structure basic :=
(hL : (Φ.functor ⋙ L).is_localization W₀)
  -- hL should be a property of `Φ`, regardless of the choice of the localization functor `L`
(right_resolution_connected : ∀ (Y : C), is_connected' (Φ.right_resolution Y))
(nonempty_arrow_right_resolution :
  ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂), ∃ (X₁ : Φ.right_resolution Y₁) (X₂ : Φ.right_resolution Y₂)
  (f' : X₁.right.obj ⟶ X₂.right.obj), X₁.hom.1 ≫ Φ.functor.map f' = f ≫ X₂.hom.1)

namespace basic

variables {L Φ} (β : basic L Φ) {D : Type*} [category D]

def some_right_resolution (Y : C) : Φ.right_resolution Y :=
(β.right_resolution_connected Y).is_nonempty.some

variables {F : C ⥤ D} (hF : W₀.is_inverted_by (Φ.functor ⋙ F))

namespace existence_derived_functor

include β hF

def RF : H ⥤ D :=
begin
  haveI := β.hL,
  exact localization.lift (Φ.functor ⋙ F) hF (Φ.functor ⋙ L),
end

def ε : (Φ.functor ⋙ L) ⋙ RF β hF ≅ Φ.functor ⋙ F :=
begin
  haveI := β.hL,
  haveI : localization.lifting (Φ.functor ⋙ L) W₀ (Φ.functor ⋙ F) (RF β hF) :=
    localization.lifting_lift _ _ _,
  refine localization.lifting.iso (Φ.functor ⋙ L) W₀ _ _,
end

def α' (X : C) : (functor.const (Φ.right_resolution X)).obj (F.obj X) ⟶
  (functor.const (Φ.right_resolution X)).obj ((RF β hF).obj (L.obj X)) :=
{ app := λ X₀, F.map X₀.hom.1 ≫ (ε β hF).inv.app _ ≫
    (RF β hF).map (localization.iso_of_hom L W _ X₀.hom.2).inv,
  naturality' := λ X₀ X₀' φ, begin
    dsimp,
    simp only [functor.map_inv, id_comp, comp_id],
    have eq₁ := φ.w,
    have eq₂ := (ε β hF).inv.naturality φ.right.1,
    dsimp at eq₁ eq₂,
    rw id_comp at eq₁,
    rw eq₁,
    dsimp,
    rw [functor.map_comp, assoc, reassoc_of eq₂],
    congr' 2,
    simp only [functor.map_comp],
    erw is_iso.comp_inv_eq, -- should be tidied
    rw is_iso.inv_hom_id_assoc,
  end, }

def α_app (X : C) : F.obj X ⟶ (RF β hF).obj (L.obj X) :=
(α' β hF X).app (β.some_right_resolution X)

lemma α_app_eq {X : C} (X₀ : Φ.right_resolution X) :
  (α_app β hF) X = (α' β hF X).app X₀ :=
begin
  haveI := β.right_resolution_connected X,
  apply nat_trans_from_is_preconnected',
end

@[simps]
def α : F ⟶ L ⋙ RF β hF :=
{ app := λ X, (α_app β hF) X,
  naturality' := λ Y₁ Y₂ f, begin
    obtain ⟨X₁, X₂, f', fac⟩ := β.nonempty_arrow_right_resolution f,
    rw [α_app_eq β hF X₁, α_app_eq β hF X₂],
    dsimp [α'],
    have eq₁ := F.congr_map fac,
    have eq₂ := (ε β hF).inv.naturality f',
    simp only [functor.map_comp] at eq₁,
    dsimp at eq₂,
    simp only [assoc, ← reassoc_of eq₁, reassoc_of eq₂, ← functor.map_comp],
    congr' 3,
    rw [is_iso.eq_inv_comp, ← L.map_comp_assoc, fac, L.map_comp, assoc,
      is_iso.hom_inv_id, comp_id],
  end, }

instance (X₀ : C₀) : is_iso ((α β hF).app (Φ.functor.obj X₀)) :=
begin
  let X₀' := localizor_morphism.right_resolution.mk Φ X₀ (𝟙 _)
    (morphism_property.contains_identities.id W _),
  dsimp [α],
  rw α_app_eq β hF (localizor_morphism.right_resolution.mk Φ X₀ (𝟙 _)
    (morphism_property.contains_identities.id W _)),
  dsimp [α'],
  simp only [functor.map_id, is_iso.inv_id, comp_id, id_comp],
  apply_instance,
end

@[simps]
def RF' : structured_arrow F ((whiskering_left C H D).obj L) :=
structured_arrow.mk (α β hF)

instance is_iso_RF'_hom_app (X₀ : C₀) :
  is_iso ((RF' β hF).hom.app (Φ.functor.obj X₀)) :=
(infer_instance : is_iso ((α β hF).app (Φ.functor.obj X₀)))

instance (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  subsingleton (RF' β hF ⟶ G) :=
⟨λ φ₁ φ₂, begin
  apply structured_arrow.ext,
  haveI := β.hL,
  apply localization.nat_trans_ext (Φ.functor ⋙ L) W₀,
  intro X₀,
  have eq₁ := congr_app φ₁.w (Φ.functor.obj X₀),
  have eq₂ := congr_app φ₂.w (Φ.functor.obj X₀),
  dsimp at eq₁ eq₂ ⊢,
  rw [id_comp] at eq₁ eq₂,
  rw [← cancel_epi ((α β hF).app (Φ.functor.obj X₀))],
  dsimp,
  rw [← eq₁, eq₂],
end⟩

def RF_τ' (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  RF β hF ⟶ G.right :=
begin
  haveI := β.hL,
  exact localization.lift_nat_trans (Φ.functor ⋙ L) W₀ _ _ _ _
    ((ε β hF).hom ≫ whisker_left _ G.hom ≫ (functor.associator _ _ _).inv),
end

@[simp]
lemma RF_τ'_app_eq (G : structured_arrow F ((whiskering_left C H D).obj L)) (X₀ : C₀) :
  (RF_τ' β hF G).app (L.obj (Φ.functor.obj X₀)) =
    (ε β hF).hom.app X₀ ≫ G.hom.app (Φ.functor.obj X₀) :=
begin
  haveI := β.hL,
  dsimp [RF_τ'],
  erw localization.lift_nat_trans_app,
  simp only [localization.lifting.of_comp_iso, iso.refl_hom, nat_trans.id_app,
    nat_trans.comp_app, whisker_left_app, functor.associator_inv_app,
    comp_id, iso.refl_inv, assoc],
  erw id_comp,
end

def RF_τ (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  RF' β hF ⟶ G :=
begin
  haveI := β.hL,
  refine structured_arrow.hom_mk (RF_τ' β hF G) _,
  ext X,
  let X₀ := β.some_right_resolution X,
  have eq := (RF_τ' β hF G).naturality (L.map X₀.hom.f),
  haveI : is_iso (L.map X₀.hom.f) := localization.inverts L W _ X₀.hom.hf,
  dsimp at ⊢ eq,
  simp only [← cancel_mono (G.right.map (L.map X₀.hom.f)), assoc, ← eq, RF_τ'_app_eq,
    α_app_eq β hF X₀, α', ← functor.map_comp_assoc],
  erw [is_iso.inv_hom_id, functor.map_id, id_comp, iso.inv_hom_id_app_assoc, G.hom.naturality],
  refl,
end

instance (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  unique (RF' β hF ⟶ G) :=
unique_of_subsingleton (RF_τ β hF G)

lemma is_initial_RF' : limits.is_initial (RF' β hF) := limits.is_initial.of_unique _

instance RF_is_right_derived_functor :
  (RF β hF).is_right_derived_functor (α _ _) :=
⟨⟨is_initial_RF' β hF⟩⟩

end existence_derived_functor

variable (F)

open existence_derived_functor

/-
The following lemma is a consequence of Lemma 6.5 of
_Structures de dérivabilité_ by Bruno Kahn, Georges Maltsiniotis,
Advances in mathematics 218 (2018).
-/

lemma existence_derived_functor : F.has_right_derived_functor W :=
functor.is_right_derived_functor.has_right_derived_functor F (RF β hF) L (α _ _) W

include β hF

lemma is_iso_app (F' : H ⥤ D) (α' : F ⟶ L ⋙ F') [F'.is_right_derived_functor α'] (X₀ : C₀) :
  is_iso (α'.app (Φ.functor.obj X₀)) :=
begin
  rw ← functor.is_right_derived_functor.uniq_hom_app_comm (RF β hF) F' (α β hF) α'
    (Φ.functor.obj X₀),
  apply_instance,
end

end basic

end right_derivability_structure

end category_theory
