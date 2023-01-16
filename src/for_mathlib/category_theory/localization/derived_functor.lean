import for_mathlib.category_theory.localization.predicate
import category_theory.adjunction.limits
import category_theory.is_connected
import for_mathlib.category_theory.localization.products
import for_mathlib.category_theory.localization.opposite

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace limits

def is_terminal.of_equivalence {C D : Type*} [category C] [category D] (e : C ≌ D) {X : C}
  (hX : is_terminal X) : is_terminal (e.functor.obj X) :=
begin
  change is_limit _,
  let e' : functor.empty C ⋙ e.functor ≅ functor.empty D := functor.empty_ext _ _,
  equiv_rw (is_limit.postcompose_inv_equiv e' _).symm,
  exact is_limit.of_iso_limit (is_limit_of_preserves e.functor hX)
    (cones.ext (iso.refl _) (by rintro ⟨⟨⟩⟩)),
end

end limits

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

@[simps]
def connected_components.op_equiv :
  connected_components C ≃ connected_components Cᵒᵖ :=
{ to_fun := quot.lift (λ X, to_connected_components (opposite.op X))
    (by { rintros X Y ⟨f⟩, symmetry, exact quot.sound ⟨f.op⟩, }),
  inv_fun := quot.lift (λ X, to_connected_components (opposite.unop X))
    (by { rintros X Y ⟨f⟩, symmetry, exact quot.sound ⟨f.unop⟩, }),
  left_inv := by { rintro ⟨X⟩, refl, },
  right_inv := by { rintro ⟨X⟩, refl, }, }

variables {C} {D E : Type*} [category D] [category E]

def connected_components.map (F : C ⥤ D) :
  connected_components C → connected_components D :=
quot.lift (λ X, to_connected_components (F.obj X))
  (by { rintros X Y ⟨f⟩, exact quot.sound ⟨F.map f⟩, })

@[simp]
lemma connected_components.map_id (C : Type*) [category C] :
  connected_components.map (𝟭 C) = id := by tidy

@[simp]
lemma connected_components.map_id_apply (x : connected_components C) :
  connected_components.map (𝟭 C) x = x :=
by simp only [connected_components.map_id, id.def]

@[simp]
lemma connected_components.map_comp (F : C ⥤ D) (G : D ⥤ E) :
  connected_components.map (F ⋙ G) =
    connected_components.map G ∘ connected_components.map F := by tidy

@[simp]
lemma connected_components.map_comp_apply (F : C ⥤ D) (G : D ⥤ E) (x : connected_components C) :
  connected_components.map (F ⋙ G) x =
  connected_components.map G (connected_components.map F x) :=
by simp only [connected_components.map_comp]

lemma connected_components.map_eq_of_nat_trans {F G : C ⥤ D} (τ : F ⟶ G) :
  connected_components.map F = connected_components.map G :=
by { ext ⟨X⟩, exact quot.sound ⟨τ.app X⟩, }

lemma connected_components.map_eq_of_nat_trans_apply {F G : C ⥤ D} (τ : F ⟶ G)
  (x : connected_components C):
  connected_components.map F x = connected_components.map G x :=
by rw connected_components.map_eq_of_nat_trans τ

@[simps]
def connected_components.equiv_of_equivalence (e : C ≌ D) :
  connected_components C ≃ connected_components D :=
{ to_fun := connected_components.map e.functor,
  inv_fun := connected_components.map e.inverse,
  left_inv := λ x, by simpa only [connected_components.map_comp_apply,
    connected_components.map_id_apply]
    using connected_components.map_eq_of_nat_trans_apply e.unit_iso.inv x,
  right_inv := λ x, by simpa only [connected_components.map_comp_apply,
    connected_components.map_id_apply]
    using connected_components.map_eq_of_nat_trans_apply e.counit_iso.hom x, }

lemma is_preconnected'.of_equivalence (e : C ≌ D) (h : is_preconnected' C) :
  is_preconnected' D :=
⟨⟨λ X Y, (connected_components.equiv_of_equivalence e).symm.injective (subsingleton.elim _ _)⟩⟩

lemma is_connected'.of_equivalence (e : C ≌ D) (h : is_connected' C) :
  is_connected' D :=
begin
  haveI : nonempty D := ⟨e.functor.obj h.is_nonempty.some⟩,
  haveI : is_preconnected' D := is_preconnected'.of_equivalence e h.1,
  constructor,
end

lemma is_preconnected'.op (h : is_preconnected' C) : is_preconnected' Cᵒᵖ :=
⟨⟨λ X Y, (connected_components.op_equiv C).symm.injective (subsingleton.elim _ _)⟩⟩

lemma is_preconnected'.unop (h : is_preconnected' Cᵒᵖ) : is_preconnected' C :=
⟨⟨λ X Y, (connected_components.op_equiv C).injective (subsingleton.elim _ _)⟩⟩

lemma is_connected'.op (h : is_connected' C) : is_connected' Cᵒᵖ :=
begin
  haveI : nonempty Cᵒᵖ := ⟨opposite.op h.is_nonempty.some⟩,
  haveI : is_preconnected' Cᵒᵖ := is_preconnected'.op infer_instance,
  constructor,
end

lemma is_connected'.unop (h : is_connected' Cᵒᵖ) : is_connected' C :=
begin
  haveI : nonempty C := ⟨opposite.unop h.is_nonempty.some⟩,
  haveI : is_preconnected' C := is_preconnected'.unop infer_instance,
  constructor,
end

end

namespace morphism_property

variables {C : Type*} [category C] (W : morphism_property C)

class multiplicative : Prop :=
(contains_identities [] : W.contains_identities)
(comp [] : W.stable_under_composition)

section

variable [multiplicative W]

instance contains_identities_of_multiplicative : W.contains_identities :=
multiplicative.contains_identities _

instance : multiplicative W.op :=
{ contains_identities := (multiplicative.contains_identities W).op,
  comp := (multiplicative.comp W).op, }

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

@[simps]
def category.mk_iso {X Y : W.category} (e : X.obj ≅ Y.obj) (h₁ : W e.hom) (h₂ : W e.inv) :
  X ≅ Y :=
{ hom := ⟨e.hom, h₁⟩,
  inv := ⟨e.inv, h₂⟩, }

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

variables {X₃ X₃'}

@[simps]
def precomp : structured_arrow X₃ G ⥤ structured_arrow X₃' G :=
{ obj := λ X₂, mk (f ≫ X₂.hom),
  map := λ X₂ X₂' φ, hom_mk φ.right (by tidy), }

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

variable (G)

@[simps]
def whiskering_left_equivalence :
equivalence (structured_arrow X₃ (eF.functor ⋙ G)) (structured_arrow X₃ G) :=
{ functor := whiskering_left X₃ eF.functor G,
  inverse := (postcomp_iso X₃ ((functor.left_unitor _).symm ≪≫
      iso_whisker_right eF.counit_iso.symm _≪≫ functor.associator _ _ _)).functor ⋙
    whiskering_left X₃ eF.inverse (eF.functor ⋙ G),
  unit_iso := nat_iso.of_components
    (λ Y, structured_arrow.iso_mk (eF.unit_iso.app _) begin
      dsimp,
      simp only [comp_id, id_comp],
      congr' 2,
      simpa only [← cancel_mono (eF.counit_iso.hom.app (eF.functor.obj Y.right)),
        equivalence.functor_unit_comp, iso.inv_hom_id_app],
    end) (by tidy),
  counit_iso := nat_iso.of_components
    (λ X, structured_arrow.iso_mk (eF.counit_iso.app _) begin
      dsimp,
      simp only [id_comp, assoc, ← G.map_comp, iso.inv_hom_id_app],
      dsimp,
      simp only [functor.map_id, comp_id],
    end) (by tidy), }

instance [is_equivalence F] : is_equivalence (whiskering_left X₃ F G) :=
is_equivalence.of_equivalence (whiskering_left_equivalence X₃ (functor.as_equivalence F) G)

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

variables {W W'} (Φ : localizor_morphism W W')

section

@[simps]
def op : localizor_morphism W.op W'.op :=
{ functor := Φ.functor.op,
  mapW := λ X Y f hf, Φ.mapW _ hf, }

variables [morphism_property.multiplicative W] [morphism_property.multiplicative W']

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

@[derive category]
def left_resolution (Y : D) := costructured_arrow Φ.induced_functor (⟨Y⟩ : W'.category)

@[simps]
def left_resolution.mk {Y : D} (X : C) (f : Φ.functor.obj X ⟶ Y) (hf : W' f) :
  Φ.left_resolution Y :=
costructured_arrow.mk (⟨f, hf⟩ : Φ.induced_functor.obj ⟨X⟩ ⟶ (⟨Y⟩ : W'.category))

variable {Φ}

@[simps]
def left_resolution.op {Y : D} (X : Φ.left_resolution Y) :
  Φ.op.right_resolution (opposite.op Y) :=
right_resolution.mk Φ.op (opposite.op X.left.1) X.hom.1.op X.hom.2

@[simps]
def right_resolution.unop {Y : D} (X : Φ.op.right_resolution (opposite.op Y)) :
  Φ.left_resolution Y :=
left_resolution.mk Φ (opposite.unop X.right.1) X.hom.1.unop X.hom.2

@[simps]
def left_resolution.unop_op {Y : D} (X : Φ.left_resolution Y) :
  X.op.unop ≅ X :=
costructured_arrow.iso_mk
  (morphism_property.category.mk_iso (iso.refl _)
    (morphism_property.contains_identities.id _ _)
    (morphism_property.contains_identities.id _ _))
  (by { ext, dsimp, simp, })

@[simps]
def right_resolution.op_unop {Y : D} (X : Φ.op.right_resolution (opposite.op Y)) :
  X.unop.op ≅ X :=
structured_arrow.iso_mk
  (morphism_property.category.mk_iso (iso.refl _)
    (morphism_property.contains_identities.id _ _)
    (morphism_property.contains_identities.id _ _))
  (by { ext, dsimp, simp, })

variable (Φ)

@[simps]
def left_resolution.op_functor (Y : D) :
  Φ.left_resolution Y ⥤ (Φ.op.right_resolution (opposite.op Y))ᵒᵖ :=
{ obj := λ X, opposite.op (left_resolution.op X),
  map := λ X₁ X₂ f, quiver.hom.op (structured_arrow.hom_mk ⟨f.left.1.op, f.left.2⟩
    (by { ext, dsimp, simpa only [← costructured_arrow.w f], })), }

@[simps]
def right_resolution.unop_functor (Y : D) :
  (Φ.op.right_resolution (opposite.op Y))ᵒᵖ ⥤ Φ.left_resolution Y :=
{ obj := λ X, (opposite.unop X).unop,
  map := λ X₁ X₂ f, costructured_arrow.hom_mk ⟨f.unop.right.1.unop, f.unop.right.2⟩
    (by { ext, dsimp, simpa only [← structured_arrow.w f.unop], }), }

@[simps]
def left_resolution.op_equivalence (Y : D) :
  Φ.left_resolution Y ≌ (Φ.op.right_resolution (opposite.op Y))ᵒᵖ :=
{ functor := left_resolution.op_functor _ _,
  inverse := right_resolution.unop_functor _ _,
  unit_iso := nat_iso.of_components (λ X, X.unop_op.symm) (by tidy),
  counit_iso := nat_iso.of_components (λ X, ((opposite.unop X).op_unop).symm.op)
    (λ X Y f, quiver.hom.unop_inj (by tidy)),
  functor_unit_iso_comp' := λ X, quiver.hom.unop_inj (by tidy), }

end

variables {C' D' : Type*} [category C'] [category D'] (L₁ : C ⥤ C') (L₂ : D ⥤ D')
  [L₁.is_localization W] [L₂.is_localization W']

abbreviation lift_functor : C' ⥤ D' :=
localization.lift (Φ.functor ⋙ L₂)
  (λ X Y f (hf : W f),
    by { dsimp, exact localization.inverts L₂ W' _ (Φ.mapW f hf), }) L₁

def fac_functor : L₁ ⋙ Φ.lift_functor L₁ L₂ ≅ Φ.functor ⋙ L₂ :=
localization.fac _ _ _

class is_localization_equivalence : Prop :=
(nonempty_is_equivalence : nonempty (is_equivalence (Φ.lift_functor W.Q W'.Q)))

namespace is_localization_equivalence

lemma iff_aux (C'' D'' : Type*) [category C''] [category D''] (L₁' : C ⥤ C'') (L₂' : D ⥤ D'')
  [L₁'.is_localization W] [L₂'.is_localization W']
  (h : is_equivalence (Φ.lift_functor L₁ L₂)) : is_equivalence (Φ.lift_functor L₁' L₂') :=
begin
  let F₁ : C' ⥤ C'' := localization.lift L₁' (localization.inverts L₁' W) L₁,
  let F₂ : D' ⥤ D'' := localization.lift L₂' (localization.inverts L₂' W') L₂,
  have e : Φ.lift_functor L₁ L₂ ⋙ F₂ ≅ F₁ ⋙ Φ.lift_functor L₁' L₂' :=
    localization.lift_nat_iso L₁ W (L₁ ⋙ Φ.lift_functor L₁ L₂ ⋙ F₂)
      (L₁ ⋙ F₁ ⋙ Φ.lift_functor L₁' L₂') _ _ begin
      refine (functor.associator _ _ _).symm ≪≫ iso_whisker_right (Φ.fac_functor L₁ L₂) _ ≪≫
        functor.associator _ _ _ ≪≫ iso_whisker_left _ (localization.fac _ _ _) ≪≫
        (Φ.fac_functor L₁' L₂').symm ≪≫
        iso_whisker_right (localization.fac L₁' (localization.inverts L₁' W) L₁).symm _ ≪≫
        functor.associator _ _ _,
    end,
  exact is_equivalence.cancel_comp_left F₁ _ infer_instance
    (is_equivalence.of_iso e infer_instance),
end

lemma iff (F : C' ⥤ D') (e : L₁ ⋙ F ≅ Φ.functor ⋙ L₂) :
  Φ.is_localization_equivalence ↔ nonempty (is_equivalence F) :=
begin
  have h : nonempty (is_equivalence F) ↔ nonempty (is_equivalence (Φ.lift_functor L₁ L₂)),
  { letI : localization.lifting L₁ W (Φ.functor ⋙ L₂) F := ⟨e⟩,
    let e' : F ≅ Φ.lift_functor L₁ L₂ :=
      localization.lift_nat_iso L₁ W (Φ.functor ⋙ L₂) (Φ.functor ⋙ L₂) _ _ (iso.refl _),
    exact ⟨λ h₁, ⟨is_equivalence.of_iso e' h₁.some⟩,
      λ h₂, ⟨is_equivalence.of_iso e'.symm h₂.some⟩⟩, },
  rw h, clear h,
  split,
  { intro h,
    exact ⟨(iff_aux Φ _ _ _ _ _ _ h.nonempty_is_equivalence.some)⟩, },
  { intro h,
    exact ⟨⟨(iff_aux Φ _ _ _ _ _ _ h.some)⟩⟩, },
end

lemma iff_is_equivalence_lift_functor :
  Φ.is_localization_equivalence ↔ nonempty (is_equivalence (Φ.lift_functor L₁ L₂)) :=
is_localization_equivalence.iff Φ L₁ L₂ (Φ.lift_functor L₁ L₂) (Φ.fac_functor L₁ L₂)

lemma iff_is_localization :
  Φ.is_localization_equivalence ↔ (Φ.functor ⋙ L₂).is_localization W :=
begin
  split,
  { intro h,
    rw iff_is_equivalence_lift_functor Φ W.Q L₂ at h,
    letI := h.some,
    exact functor.is_localization.of_equivalence W.Q W (Φ.functor ⋙ L₂)
      (functor.as_equivalence (Φ.lift_functor W.Q L₂)) (Φ.fac_functor _ _), },
  { introI,
    rw iff_is_equivalence_lift_functor Φ (Φ.functor ⋙ L₂) L₂,
    exact ⟨is_equivalence.of_iso (localization.lifting.uniq (Φ.functor ⋙ L₂) W
      (Φ.functor ⋙ L₂) (𝟭 _) _) infer_instance⟩, },
end

instance [hΦ : Φ.is_localization_equivalence] :
  is_equivalence (Φ.lift_functor L₁ L₂) :=
((iff_is_equivalence_lift_functor Φ L₁ L₂).mp hΦ).some

instance is_localization_of_is_localization_equivalence [hΦ : Φ.is_localization_equivalence] :
  (Φ.functor ⋙ L₂).is_localization W :=
by simpa only [← iff_is_localization Φ L₂] using hΦ

instance op_is_localization_equivalence [hΦ : Φ.is_localization_equivalence] :
  Φ.op.is_localization_equivalence :=
begin
  rw iff_is_localization Φ W'.Q at hΦ,
  rw iff_is_localization Φ.op W'.Q.op,
  haveI := hΦ,
  change (Φ.functor ⋙ W'.Q).op.is_localization W.op,
  apply_instance,
end

end is_localization_equivalence

end localizor_morphism

end

namespace right_derivability_structure

variables {C₀ C H : Type*} [category C] [category C₀] [category H]
  {W₀ : morphism_property C₀}
  {W : morphism_property C} (Φ : localizor_morphism W₀ W)
  [localizor_morphism.is_localization_equivalence Φ]
  [morphism_property.multiplicative W₀] [morphism_property.multiplicative W]

structure basic :=
(right_resolution_connected : ∀ (Y : C), is_connected' (Φ.right_resolution Y))
(nonempty_arrow_right_resolution :
  ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂), ∃ (X₁ : Φ.right_resolution Y₁) (X₂ : Φ.right_resolution Y₂)
  (f' : X₁.right.obj ⟶ X₂.right.obj), X₁.hom.1 ≫ Φ.functor.map f' = f ≫ X₂.hom.1)

namespace basic

variables {Φ} (β : basic Φ) (L : C ⥤ H) [L.is_localization W]
  {D : Type*} [category D]

def some_right_resolution (Y : C) : Φ.right_resolution Y :=
(β.right_resolution_connected Y).is_nonempty.some

variables {F : C ⥤ D} (hF : W₀.is_inverted_by (Φ.functor ⋙ F))

namespace existence_derived_functor

include β hF

def RF : H ⥤ D :=
localization.lift (Φ.functor ⋙ F) hF (Φ.functor ⋙ L)

def ε : (Φ.functor ⋙ L) ⋙ RF β L hF ≅ Φ.functor ⋙ F :=
begin
  letI : localization.lifting (Φ.functor ⋙ L) W₀ (Φ.functor ⋙ F) (RF β L hF) :=
    localization.lifting_lift _ _ _,
  refine localization.lifting.iso (Φ.functor ⋙ L) W₀ _ _,
end

def α' (X : C) : (functor.const (Φ.right_resolution X)).obj (F.obj X) ⟶
  (functor.const (Φ.right_resolution X)).obj ((RF β L hF).obj (L.obj X)) :=
{ app := λ X₀, F.map X₀.hom.1 ≫ (ε β L hF).inv.app _ ≫
    (RF β L hF).map (localization.iso_of_hom L W _ X₀.hom.2).inv,
  naturality' := λ X₀ X₀' φ, begin
    dsimp,
    simp only [functor.map_inv, id_comp, comp_id],
    have eq₁ := φ.w,
    have eq₂ := (ε β L hF).inv.naturality φ.right.1,
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

def α_app (X : C) : F.obj X ⟶ (RF β L hF).obj (L.obj X) :=
(α' β L hF X).app (β.some_right_resolution X)

lemma α_app_eq {X : C} (X₀ : Φ.right_resolution X) :
  (α_app β L hF) X = (α' β L hF X).app X₀ :=
begin
  haveI := β.right_resolution_connected X,
  apply nat_trans_from_is_preconnected',
end

@[simps]
def α : F ⟶ L ⋙ RF β L hF :=
{ app := λ X, (α_app β L hF) X,
  naturality' := λ Y₁ Y₂ f, begin
    obtain ⟨X₁, X₂, f', fac⟩ := β.nonempty_arrow_right_resolution f,
    rw [α_app_eq β L hF X₁, α_app_eq β L hF X₂],
    dsimp [α'],
    have eq₁ := F.congr_map fac,
    have eq₂ := (ε β L hF).inv.naturality f',
    simp only [functor.map_comp] at eq₁,
    dsimp at eq₂,
    simp only [assoc, ← reassoc_of eq₁, reassoc_of eq₂, ← functor.map_comp],
    congr' 3,
    rw [is_iso.eq_inv_comp, ← L.map_comp_assoc, fac, L.map_comp, assoc,
      is_iso.hom_inv_id, comp_id],
  end, }

instance (X₀ : C₀) : is_iso ((α β L hF).app (Φ.functor.obj X₀)) :=
begin
  let X₀' := localizor_morphism.right_resolution.mk Φ X₀ (𝟙 _)
    (morphism_property.contains_identities.id W _),
  dsimp [α],
  rw α_app_eq β L hF (localizor_morphism.right_resolution.mk Φ X₀ (𝟙 _)
    (morphism_property.contains_identities.id W _)),
  dsimp [α'],
  simp only [functor.map_id, is_iso.inv_id, comp_id, id_comp],
  apply_instance,
end

@[simps]
def RF' : structured_arrow F ((whiskering_left C H D).obj L) :=
structured_arrow.mk (α β L hF)

instance is_iso_RF'_hom_app (X₀ : C₀) :
  is_iso ((RF' β L hF).hom.app (Φ.functor.obj X₀)) :=
(infer_instance : is_iso ((α β L hF).app (Φ.functor.obj X₀)))

instance (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  subsingleton (RF' β L hF ⟶ G) :=
⟨λ φ₁ φ₂, begin
  apply structured_arrow.ext,
  apply localization.nat_trans_ext (Φ.functor ⋙ L) W₀,
  intro X₀,
  have eq₁ := congr_app φ₁.w (Φ.functor.obj X₀),
  have eq₂ := congr_app φ₂.w (Φ.functor.obj X₀),
  dsimp at eq₁ eq₂ ⊢,
  rw [id_comp] at eq₁ eq₂,
  rw [← cancel_epi ((α β L hF).app (Φ.functor.obj X₀))],
  dsimp,
  rw [← eq₁, eq₂],
end⟩

def RF_τ' (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  RF β L hF ⟶ G.right :=
localization.lift_nat_trans (Φ.functor ⋙ L) W₀ _ _ _ _
  ((ε β L hF).hom ≫ whisker_left _ G.hom ≫ (functor.associator _ _ _).inv)

@[simp]
lemma RF_τ'_app_eq (G : structured_arrow F ((whiskering_left C H D).obj L)) (X₀ : C₀) :
  (RF_τ' β L hF G).app (L.obj (Φ.functor.obj X₀)) =
    (ε β L hF).hom.app X₀ ≫ G.hom.app (Φ.functor.obj X₀) :=
begin
  dsimp [RF_τ'],
  erw localization.lift_nat_trans_app,
  simp only [localization.lifting.of_comp_iso, iso.refl_hom, nat_trans.id_app,
    nat_trans.comp_app, whisker_left_app, functor.associator_inv_app,
    comp_id, iso.refl_inv, assoc],
  erw id_comp,
end

def RF_τ (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  RF' β L hF ⟶ G :=
begin
  refine structured_arrow.hom_mk (RF_τ' β L hF G) _,
  ext X,
  let X₀ := β.some_right_resolution X,
  have eq := (RF_τ' β L hF G).naturality (L.map X₀.hom.f),
  haveI : is_iso (L.map X₀.hom.f) := localization.inverts L W _ X₀.hom.hf,
  dsimp at ⊢ eq,
  simp only [← cancel_mono (G.right.map (L.map X₀.hom.f)), assoc, ← eq, RF_τ'_app_eq,
    α_app_eq β L hF X₀, α', ← functor.map_comp_assoc],
  erw [is_iso.inv_hom_id, functor.map_id, id_comp, iso.inv_hom_id_app_assoc, G.hom.naturality],
  refl,
end

instance (G : structured_arrow F ((whiskering_left C H D).obj L)) :
  unique (RF' β L hF ⟶ G) :=
unique_of_subsingleton (RF_τ β L hF G)

lemma is_initial_RF' : limits.is_initial (RF' β L hF) := limits.is_initial.of_unique _

instance RF_is_right_derived_functor :
  (RF β L hF).is_right_derived_functor (α _ _ _) :=
⟨⟨is_initial_RF' β L hF⟩⟩

end existence_derived_functor

variable (F)

open existence_derived_functor

/-
The following lemma is a consequence of Lemma 6.5 of
_Structures de dérivabilité_ by Bruno Kahn, Georges Maltsiniotis,
Advances in mathematics 218 (2018).
-/

lemma existence_derived_functor : F.has_right_derived_functor W :=
functor.is_right_derived_functor.has_right_derived_functor F (RF β W.Q hF) W.Q (α _ _ _) W

include β hF

lemma is_iso_app (F' : H ⥤ D) (α' : F ⟶ L ⋙ F') [F'.is_right_derived_functor α'] (X₀ : C₀) :
  is_iso (α'.app (Φ.functor.obj X₀)) :=
begin
  rw ← functor.is_right_derived_functor.uniq_hom_app_comm (RF β L hF) F' (α β L hF) α'
    (Φ.functor.obj X₀),
  apply_instance,
end

end basic

end right_derivability_structure

namespace functor

variables {C D H : Type*} [category C] [category D] [category H]
  {F : C ⥤ D} (LF : H ⥤ D) {L : C ⥤ H} (α : L ⋙ LF ⟶ F) (W : morphism_property C) [L.is_localization W]

class is_left_derived_functor : Prop :=
(is_terminal [] : nonempty (limits.is_terminal (costructured_arrow.mk α :
  costructured_arrow ((whiskering_left C H D).obj L) F)))

namespace is_left_derived_functor

variables (LF₁ LF₂ : H ⥤ D) (α₁ : L ⋙ LF₁ ⟶ F) (α₂ : L ⋙ LF₂ ⟶ F)
  [LF₁.is_left_derived_functor α₁] [LF₂.is_left_derived_functor α₂]

def uniq' : (costructured_arrow.mk α₁ :
  costructured_arrow ((whiskering_left C H D).obj L) F) ≅ costructured_arrow.mk α₂ :=
limits.is_limit.cone_point_unique_up_to_iso
    (is_left_derived_functor.is_terminal α₁).some
    (is_left_derived_functor.is_terminal α₂).some

def uniq : LF₁ ≅ LF₂ :=
(costructured_arrow.proj _ _).map_iso (uniq' _ _ α₁ α₂)

@[simp]
def uniq_hom_app_comm (X : C) : (uniq _ _ α₁ α₂).hom.app (L.obj X) ≫ α₂.app X = α₁.app X :=
congr_app (costructured_arrow.w (uniq' _ _ α₁ α₂).hom) X

@[simp]
def uniq_inv_app_comm (X : C) : (uniq _ _ α₁ α₂).inv.app (L.obj X) ≫ α₁.app X = α₂.app X :=
congr_app (costructured_arrow.w (uniq' _ _ α₁ α₂).inv) X

end is_left_derived_functor

variables (F L)

class has_left_derived_functor : Prop :=
(has_terminal' : limits.has_terminal (costructured_arrow ((whiskering_left C _ D).obj W.Q) F))

namespace costructured_arrow_equivalence_op

@[simps]
def functor : (costructured_arrow ((whiskering_left C H D).obj L) F) ⥤
    (structured_arrow F.op ((whiskering_left Cᵒᵖ Hᵒᵖ Dᵒᵖ).obj L.op))ᵒᵖ :=
{ obj := λ X, opposite.op (structured_arrow.mk
    (show F.op ⟶ ((whiskering_left Cᵒᵖ Hᵒᵖ Dᵒᵖ).obj L.op).obj X.left.op,
      by exact (functor.op_hom _ _).map X.hom.op)),
  map := λ X₁ X₂ f, quiver.hom.op
    (structured_arrow.hom_mk ((functor.op_hom H D).map (quiver.hom.op f.left))
      (by { rw ← costructured_arrow.w f, refl, })), }

@[simps]
def inverse : (structured_arrow F.op ((whiskering_left Cᵒᵖ Hᵒᵖ Dᵒᵖ).obj L.op))ᵒᵖ ⥤
    (costructured_arrow ((whiskering_left C H D).obj L) F) :=
{ obj := λ X, costructured_arrow.mk
      (show ((whiskering_left C H D).obj L).obj X.unop.right.unop ⟶ F,
        by exact ((functor.op_inv C D).map X.unop.hom).unop ≫ F.op_unop_iso.hom),
  map := λ X₁ X₂ f, costructured_arrow.hom_mk (((functor.op_inv _ _).map f.unop.right).unop)
      (by { rw ← structured_arrow.w f.unop, dsimp, ext, tidy, }), }

@[simps]
def unit_iso : 𝟭 _ ≅ functor F L ⋙ inverse F L :=
nat_iso.of_components (λ X, costructured_arrow.iso_mk (functor.op_unop_iso X.left).symm
    (by { ext, dsimp, tidy, })) (by tidy)

@[simps]
def counit_iso : inverse F L ⋙ functor F L ≅ 𝟭 _ :=
nat_iso.of_components (λ X, begin
  change opposite.op (opposite.unop _) ≅ opposite.op (opposite.unop _),
  apply iso.op,
  refine structured_arrow.iso_mk (functor.unop_op_iso _).symm _,
  ext, dsimp, tidy,
end) (λ X Y f, quiver.hom.unop_inj (by { dsimp, tidy, }))

end costructured_arrow_equivalence_op

def costructured_arrow_equivalence_op :
  (costructured_arrow ((whiskering_left C H D).obj L) F) ≌
    (structured_arrow F.op ((whiskering_left Cᵒᵖ Hᵒᵖ Dᵒᵖ).obj L.op))ᵒᵖ :=
{ functor := costructured_arrow_equivalence_op.functor _ _,
  inverse := costructured_arrow_equivalence_op.inverse _ _,
  unit_iso := costructured_arrow_equivalence_op.unit_iso _ _,
  counit_iso := costructured_arrow_equivalence_op.counit_iso _ _,
  functor_unit_iso_comp' := λ X, quiver.hom.unop_inj begin
    dsimp [structured_arrow.iso_mk, structured_arrow.hom_mk, comma.iso_mk],
    tidy,
  end, }

variable (L)

lemma has_left_derived_functor_iff_op :
  has_left_derived_functor F W ↔ has_right_derived_functor F.op W.op :=
begin
  have h : F.has_left_derived_functor W ↔
    limits.has_terminal (costructured_arrow ((whiskering_left C _ D).obj W.Q) F) :=
    ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  rw [h, has_right_derived_functor_iff F.op W.Q.op W.op],
  have e := costructured_arrow_equivalence_op F W.Q,
  split,
  { introI,
    haveI : limits.has_terminal
      (structured_arrow F.op ((whiskering_left Cᵒᵖ (W.localization)ᵒᵖ Dᵒᵖ).obj W.Q.op))ᵒᵖ :=
      adjunction.has_limits_of_shape_of_equivalence e.inverse,
    exact limits.has_initial_of_has_terminal_op, },
  { introI,
    exact adjunction.has_limits_of_shape_of_equivalence e.functor, },
end

lemma has_left_derived_functor_iff :
  has_left_derived_functor F W ↔
    limits.has_terminal (costructured_arrow ((whiskering_left C H D).obj L) F) :=
begin
  rw [has_left_derived_functor_iff_op, has_right_derived_functor_iff F.op L.op W.op],
  have e := costructured_arrow_equivalence_op F L,
  split,
  { introI,
    exact adjunction.has_limits_of_shape_of_equivalence e.functor, },
  { introI,
    haveI : limits.has_terminal
      (structured_arrow F.op ((whiskering_left Cᵒᵖ Hᵒᵖ Dᵒᵖ).obj L.op))ᵒᵖ :=
      adjunction.has_limits_of_shape_of_equivalence e.inverse,
    exact limits.has_initial_of_has_terminal_op, },
end

lemma is_left_derived_functor.has_left_derived_functor [LF.is_left_derived_functor α] :
  F.has_left_derived_functor W :=
begin
  rw F.has_left_derived_functor_iff L W,
  exact limits.is_terminal.has_terminal (is_left_derived_functor.is_terminal α).some,
end

variables {F L LF F α}

lemma is_left_derived_functor.op (hα : LF.is_left_derived_functor α) :
  @is_right_derived_functor _ _ _ _ _ _ F.op LF.op L.op ((functor.op_hom _ _).map α.op) :=
is_right_derived_functor.mk
  (nonempty.intro (limits.initial_unop_of_terminal
    (limits.is_terminal.of_equivalence (costructured_arrow_equivalence_op F L)
      hα.is_terminal.some)))

variables (F L LF F α)

lemma has_left_derived_functor.has_terminal [has_left_derived_functor F W] :
  limits.has_terminal (costructured_arrow ((whiskering_left C H D).obj L) F) :=
(has_left_derived_functor_iff F L W).1 infer_instance

def has_left_derived_functor.initial [has_left_derived_functor F W] :
  (costructured_arrow ((whiskering_left C H D).obj L) F) :=
begin
  haveI := has_left_derived_functor.has_terminal F L W,
  exact limits.terminal _,
end

def left_derived_functor [has_left_derived_functor F W] : H ⥤ D :=
(has_left_derived_functor.initial F L W).left

def left_derived_functor_α [has_left_derived_functor F W] :
  L ⋙ F.left_derived_functor L W ⟶ F :=
(has_left_derived_functor.initial F L W).hom

instance left_derived_functor_is_left_derived_functor [has_left_derived_functor F W] :
  (F.left_derived_functor L W).is_left_derived_functor (F.left_derived_functor_α L W) :=
⟨⟨begin
  haveI := has_left_derived_functor.has_terminal F L W,
  exact limits.is_terminal.of_iso limits.terminal_is_terminal
    (costructured_arrow.iso_mk (iso.refl _) (by tidy)),
end⟩⟩

end functor

namespace left_derivability_structure

variables {C₀ C H : Type*} [category C] [category C₀] [category H]
  {W₀ : morphism_property C₀}
  {W : morphism_property C} (L : C ⥤ H) [L.is_localization W] (Φ : localizor_morphism W₀ W)
  [localizor_morphism.is_localization_equivalence Φ]
  [morphism_property.multiplicative W₀] [morphism_property.multiplicative W]

structure basic :=
(left_resolution_connected : ∀ (Y : C), is_connected' (Φ.left_resolution Y))
(nonempty_arrow_left_resolution :
  ∀ ⦃Y₁ Y₂ : C⦄ (f : Y₁ ⟶ Y₂), ∃ (X₁ : Φ.left_resolution Y₁) (X₂ : Φ.left_resolution Y₂)
  (f' : X₁.left.obj ⟶ X₂.left.obj), Φ.functor.map f' ≫ X₂.hom.1 = X₁.hom.1 ≫ f)

namespace basic

variables {L Φ}

def op (β : basic  Φ) : right_derivability_structure.basic Φ.op :=
{ right_resolution_connected := λ Y, (is_connected'.of_equivalence
      (localizor_morphism.left_resolution.op_equivalence Φ (opposite.unop Y))
      (β.left_resolution_connected (opposite.unop Y))).unop,
  nonempty_arrow_right_resolution := λ Y₁ Y₂ f, begin
    obtain ⟨X₁, X₂, f', fac⟩ := β.nonempty_arrow_left_resolution f.unop,
    exact ⟨X₂.op, X₁.op, f'.op, quiver.hom.unop_inj fac⟩,
  end, }

variables (β : basic Φ) {D : Type*} [category D] (F : C ⥤ D)
  (hF : W₀.is_inverted_by (Φ.functor ⋙ F))

include β hF

lemma existence_derived_functor : F.has_left_derived_functor W :=
by simpa only [functor.has_left_derived_functor_iff_op]
  using β.op.existence_derived_functor F.op hF.op

lemma is_iso_app (F' : H ⥤ D) (α' : L ⋙ F' ⟶ F) [hα' : F'.is_left_derived_functor α'] (X₀ : C₀) :
  is_iso (α'.app (Φ.functor.obj X₀)) :=
begin
  suffices : is_iso (α'.app (Φ.functor.obj X₀)).op,
  { haveI := this,
    exact is_iso.of_iso ((as_iso (α'.app (Φ.functor.obj X₀)).op).unop), },
  let α'' : F.op ⟶ L.op ⋙ F'.op := (functor.op_hom C D).map α'.op,
  haveI : F'.op.is_right_derived_functor α'' := hα'.op,
  exact β.op.is_iso_app L.op F.op hF.op F'.op α'' (opposite.op X₀),
end

end basic

end left_derivability_structure

end category_theory
