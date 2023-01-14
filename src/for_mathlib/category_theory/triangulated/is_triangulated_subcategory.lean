import category_theory.triangulated.triangulated
import for_mathlib.category_theory.triangulated.triangulated_functor

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace set

open category_theory

class respects_iso {X : Type*} [category X] (A : set X) : Prop :=
(condition' : ∀ ⦃x y : X⦄ (e : x ≅ y) (hx : x ∈ A), y ∈ A)

lemma respects_iso.condition {X : Type*} [category X] (A : set X) [A.respects_iso]
  {x y : X} (e : x ≅ y) (hx : x ∈ A) : y ∈ A :=
respects_iso.condition' e hx

lemma respects_iso.mem_iff_of_iso {X : Type*} [category X] (A : set X) [A.respects_iso]
  {x y : X} (e : x ≅ y) : x ∈ A ↔ y ∈ A :=
begin
  split,
  { exact respects_iso.condition A e, },
  { exact respects_iso.condition A e.symm, },
end

end set

namespace category_theory

namespace triangulated

open pretriangulated

variables {C : Type*} [category C] [has_shift C ℤ] [preadditive C] [has_zero_object C]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

variable (S : set C)

class is_triangulated_subcategory : Prop :=
(zero [] : (0 : C) ∈ S)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ S), (shift_functor C n).obj X ∈ S)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ S)
  (h₃ : T.obj₃ ∈ S), T.obj₂ ∈ S)

namespace is_triangulated_subcategory

variables {S} [is_triangulated_subcategory S]

instance set_respects_iso : S.respects_iso :=
⟨λ X Y e hX, ext₂ _ (pretriangulated.isomorphic_distinguished _
  (pretriangulated.contractible_distinguished X) (triangle.mk e.hom (0 : Y ⟶ 0) 0)
  (triangle.mk_iso _ _ (iso.refl _) e.symm (iso.refl _) (by tidy) (by tidy) (by tidy))) hX
  (is_triangulated_subcategory.zero S)⟩

lemma ext₁
  (T : triangle C) (hT : T ∈ dist_triang C) (h₂ : T.obj₂ ∈ S) (h₃ : T.obj₃ ∈ S) :
  T.obj₁ ∈ S :=
ext₂ T.inv_rotate (pretriangulated.inv_rot_of_dist_triangle C T hT)
  (is_triangulated_subcategory.shift _ _ h₃) h₂

lemma ext₃
  (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ S) (h₂ : T.obj₂ ∈ S) :
  T.obj₃ ∈ S :=
ext₂ T.rotate (pretriangulated.rot_of_dist_triangle C T hT) h₂
  (is_triangulated_subcategory.shift _ _ h₁)

lemma shift_iff (X : C) (n : ℤ) : X ∈ S ↔ (shift_functor C n).obj X ∈ S :=
begin
  split,
  { intro h,
    exact is_triangulated_subcategory.shift _ _ h, },
  { intro h,
    exact set.respects_iso.condition S
      ((add_neg_equiv (shift_monoidal_functor C ℤ) n).unit_iso.symm.app X)
      (is_triangulated_subcategory.shift _ _ h), },
end

end is_triangulated_subcategory

class is_triangulated_subcategory' : Prop :=
(zero : ∃ (X : C) (hX₀ : is_zero X), X ∈ S)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ S), (shift_functor C n).obj X ∈ S)
(distinguished_cocone_triangle' : ∀ (X Y : C) (hX : X ∈ S) (hY : Y ∈ S) (f : X ⟶ Y),
  ∃ (Z : C) (hZ : Z ∈ S) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
    triangle.mk f g h ∈ dist_triang C)

@[priority 100]
instance is_triangulated_subcategory'_of_is_triangulated_subcategory
  [hS : is_triangulated_subcategory S] :
  is_triangulated_subcategory' S :=
{ zero := ⟨0, is_zero_zero _, hS.zero⟩,
  shift := hS.shift,
  distinguished_cocone_triangle' := λ X Y hX hY f, begin
    obtain ⟨Z, g, h, mem⟩ := pretriangulated.distinguished_cocone_triangle _ _ f,
    exact ⟨Z, hS.ext₂ _ (rot_of_dist_triangle _ _ mem) hY (hS.shift _ 1 hX), g, h, mem⟩,
  end, }

namespace is_triangulated_subcategory'

variable [hS : is_triangulated_subcategory' S]

include hS

instance : has_zero_object (full_subcategory S) :=
begin
  obtain ⟨X₀, hX₀, mem⟩ := hS.zero,
  refine ⟨⟨⟨X₀, mem⟩, _⟩⟩,
  rw limits.is_zero.iff_id_eq_zero,
  exact (full_subcategory_inclusion S).map_injective (is_zero.eq_of_src hX₀ _ _),
end

instance is_stable_by_shift : S.is_stable_by_shift ℤ :=
⟨λ a X hX, hS.shift X a hX⟩

instance shift_functor_additive (n : ℤ) :
  (category_theory.shift_functor (full_subcategory S) n).additive :=
⟨begin
  rintros ⟨K, hK⟩ ⟨L, hL⟩ f g,
  exact (full_subcategory_inclusion S).map_injective (category_theory.shift_functor C n).map_add,
end⟩

--instance full_subcategory_inclusion_has_comm_shift :
--  (full_subcategory_inclusion S).has_comm_shift ℤ := infer_instance

def distinguished_triangles : set (triangle (full_subcategory S)) :=
λ T, (full_subcategory_inclusion S).map_triangle.obj T ∈ dist_triang C

lemma isomorphic_distinguished (T₁ : triangle (full_subcategory S))
  (hT₁ : T₁ ∈ distinguished_triangles S) (T₂ : triangle (full_subcategory S)) (e : T₂ ≅ T₁) :
  T₂ ∈ distinguished_triangles S :=
pretriangulated.isomorphic_distinguished _ hT₁ _ ((full_subcategory_inclusion S).map_triangle.map_iso e)

lemma contractible_distinguished (X : full_subcategory S) :
  triangle.mk (𝟙 X) (0 : X ⟶ 0) 0 ∈ distinguished_triangles S :=
begin
  refine pretriangulated.isomorphic_distinguished _
    (pretriangulated.contractible_distinguished ((full_subcategory_inclusion S).obj X)) _ _,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _)
    (full_subcategory_inclusion S).map_zero_object _ _ _,
  tidy,
end

lemma rotate_distinguished_triangle (T : triangle (full_subcategory S)) :
  T ∈ distinguished_triangles S ↔
    T.rotate ∈ distinguished_triangles S :=
begin
  change ((full_subcategory_inclusion S).map_triangle.obj T ∈ dist_triang C) ↔
    ((full_subcategory_inclusion S).map_triangle.obj T.rotate ∈ dist_triang C),
  rw pretriangulated.rotate_distinguished_triangle,
  let e := (full_subcategory_inclusion S).map_triangle_rotate.app T,
  split,
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e.symm, },
  { exact λ h, pretriangulated.isomorphic_distinguished _ h _ e, },
end

lemma distinguished_cocone_triangle (X Y : full_subcategory S) (f : X ⟶ Y) :
  ∃ (Z : full_subcategory S) (g : Y ⟶ Z) (h : Z ⟶ (category_theory.shift_functor _ (1 : ℤ)).obj X),
    triangle.mk f g h ∈ distinguished_triangles S :=
begin
  obtain ⟨X, hX⟩ := X,
  obtain ⟨Y, hY⟩ := Y,
  obtain ⟨Z, hZ, g, h, mem⟩ := hS.distinguished_cocone_triangle' _ _ hX hY f,
  refine ⟨⟨Z, hZ⟩, g, h, pretriangulated.isomorphic_distinguished _ mem _ _⟩,
  refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy) _,
  { dsimp,
    simp only [functor.map_id, comp_id, id_comp],
    apply comp_id, },
end

lemma complete_distinguished_triangle_morphism (T₁ T₂ : triangle (full_subcategory S))
  (hT₁ : T₁ ∈ distinguished_triangles S) (hT₂ : T₂ ∈ distinguished_triangles S)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (h : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
  ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫
    (category_theory.shift_functor _ 1).map a = c ≫ T₂.mor₃ :=
begin
  obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := pretriangulated.complete_distinguished_triangle_morphism
    ((full_subcategory_inclusion S).map_triangle.obj T₁)
      ((full_subcategory_inclusion S).map_triangle.obj T₂)
    hT₁ hT₂ a b h,
  refine ⟨c, ⟨hc₁, _⟩⟩,
  dsimp at hc₂,
  erw [comp_id, comp_id] at hc₂,
  exact hc₂,
end

instance : pretriangulated (full_subcategory S) :=
{ distinguished_triangles := distinguished_triangles S,
  isomorphic_distinguished := isomorphic_distinguished S,
  contractible_distinguished := contractible_distinguished S,
  distinguished_cocone_triangle := distinguished_cocone_triangle S,
  rotate_distinguished_triangle := rotate_distinguished_triangle S,
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism S, }

instance [is_triangulated C] : is_triangulated (full_subcategory S) :=
⟨λ X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃, begin
  have comm' := (full_subcategory_inclusion S).congr_map comm,
  rw [functor.map_comp] at comm',
  have H := (is_triangulated.octahedron_axiom comm' h₁₂ h₂₃ h₁₃).some,
  obtain ⟨m₁, m₃, comm₁, comm₂, comm₃, comm₄, H'⟩ := H,
  refine nonempty.intro
  { m₁ := m₁,
    m₃ := m₃,
    comm₁ := comm₁,
    comm₂ := begin
      erw [comp_id, comp_id] at comm₂,
      exact comm₂,
    end,
    comm₃ := comm₃,
    comm₄ := begin
      erw [comp_id, comp_id] at comm₄,
      exact comm₄,
    end,
    mem := begin
      change _ ∈ dist_triang C,
      refine pretriangulated.isomorphic_distinguished _ H' _ _,
      refine triangle.mk_iso _ _ (iso.refl _) (iso.refl _) (iso.refl _) _ _ _,
      { dsimp,
        simp, },
      { dsimp,
        simp, },
      { dsimp,
        erw [functor.map_id, comp_id, comp_id, id_comp, comp_id],
        refl, },
    end, }
end⟩

instance full_subcategory_inclusion_is_triangulated :
  (full_subcategory_inclusion S).is_triangulated :=
{ map_distinguished' := λ T hT, hT, }

end is_triangulated_subcategory'

class saturated [is_triangulated_subcategory S] : Prop :=
(condition : ∀ ⦃X Y : C⦄ (i : Y ⟶ X) [hi : is_split_mono i] (hX : X ∈ S), Y ∈ S)

def left_orthogonal : set C :=
λ X, ∀ ⦃Y : C⦄ (f : X ⟶ Y) (hY : Y ∈ S), f = 0

def right_orthogonal : set C :=
λ Y, ∀ ⦃X : C⦄ (f : X ⟶ Y) (hX : X ∈ S), f = 0

instance [S.is_stable_by_shift ℤ] :
  is_triangulated_subcategory (left_orthogonal S) :=
{ zero := λ Y hY f, subsingleton.elim _ _,
  shift := λ X n hX Y f hY, begin
    let adj : shift_functor C n ⊣ shift_functor C (-n) :=
      (add_neg_equiv (shift_monoidal_functor C ℤ) n).to_adjunction,
    apply (adj.hom_equiv _ _).injective,
    simp only [adjunction.hom_equiv_unit, functor.map_zero, comp_zero],
    exact hX _ (set.is_stable_by_shift.condition (-n) Y hY),
  end,
  ext₂ := λ T hT h₁ h₃ Y f hY, begin
    obtain ⟨g, hg⟩ := contravariant_yoneda_exact₂ T hT f (h₁ _ hY),
    rw [hg, h₃ g hY, comp_zero],
  end, }

instance [S.is_stable_by_shift ℤ] :
  is_triangulated_subcategory (right_orthogonal S) :=
{ zero := λ X hX f, subsingleton.elim _ _,
  shift := λ Y n hY X f hX, begin
    let adj : shift_functor C (-n) ⊣ shift_functor C n :=
      (add_neg_equiv (shift_monoidal_functor C ℤ) n).symm.to_adjunction,
    apply (adj.hom_equiv _ _).symm.injective,
    simp only [adjunction.hom_equiv_counit, functor.map_zero, zero_comp],
    exact hY _ (set.is_stable_by_shift.condition (-n) X hX),
  end,
  ext₂ := λ T hT h₁ h₃ X f hX, begin
    obtain ⟨g, hg⟩ := covariant_yoneda_exact₂ T hT f (h₃ _ hX),
    rw [hg, h₁ g hX, zero_comp],
  end, }

instance left_orthogonal_saturated [S.is_stable_by_shift ℤ] :
  saturated (left_orthogonal S) :=
⟨λ X Y i hi hX Z f hZ, begin
  haveI := hi,
  rw [← cancel_epi (retraction i), comp_zero],
  exact hX _ hZ,
end⟩

instance right_orthogonal_saturated [S.is_stable_by_shift ℤ] :
  saturated (right_orthogonal S) :=
⟨λ X Y i hi hX Z f hZ, begin
  haveI := hi,
  rw [← cancel_mono i, zero_comp],
  exact hX _ hZ,
end⟩

end triangulated

end category_theory
