import for_mathlib.algebra.homology.trunc

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace category_theory

namespace triangulated

open pretriangulated

variables {C : Type*} [category C] [has_shift C ℤ] [preadditive C] [has_zero_object C]
  [∀ (n : ℤ), functor.additive (shift_functor C n)] [pretriangulated C]

variable (S : set C)

class is_triangulated_subcategory : Prop :=
(zero : (0 : C) ∈ S)
(shift : ∀ (X : C) (n : ℤ) (hX : X ∈ S), (shift_functor C n).obj X ∈ S)
(ext₂ : ∀ (T : triangle C) (hT : T ∈ dist_triang C) (h₁ : T.obj₁ ∈ S)
  (h₃ : T.obj₃ ∈ S), T.obj₂ ∈ S)

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

end is_triangulated_subcategory'

end triangulated

end category_theory

variables {C : Type*} [category C] [abelian C]

namespace derived_category

instance zero_is_le (n : ℤ) : (0 : derived_category C).is_le n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

instance zero_is_ge (n : ℤ) : (0 : derived_category C).is_ge n :=
⟨λ i hi, is_zero.of_iso (is_zero_zero _)
  (derived_category.homology_functor C i).map_zero_object⟩

def is_plus (K : derived_category C) : Prop := ∃ (n : ℤ), K.is_ge n

variable (C)
open category_theory.triangulated

instance plus_is_triangulated_subcategory :
  is_triangulated_subcategory (λ (K : derived_category C), K.is_plus) :=
{ zero := ⟨0, infer_instance⟩,
  shift := begin
    rintros K k ⟨n, hn⟩,
    haveI := hn,
    exact ⟨n-k, shift_is_ge K n k (n-k) (by linarith)⟩,
  end,
  ext₂ := begin
    rintros T hT ⟨n₁, hn₁⟩ ⟨n₃, hn₃⟩,
    exact ⟨min n₁ n₃,
      ⟨λ n hn, short_complex.exact.is_zero_of_both_zeros (homology_sequence.ex₂ hT n)
        (is_zero.eq_of_src (hn₁.is_zero' _ (lt_of_lt_of_le hn (min_le_left n₁ n₃))) _ _)
        (is_zero.eq_of_tgt (hn₃.is_zero' _ (lt_of_lt_of_le hn (min_le_right n₁ n₃))) _ _)⟩⟩,
  end, }

abbreviation plus := full_subcategory (λ (K : derived_category C), K.is_plus)

namespace plus

instance : pretriangulated (plus C) := infer_instance

def mk (K : derived_category C) (n : ℤ) [hn : K.is_ge n] :
  derived_category.plus C :=
⟨K, n, hn⟩

variable {C}

def ι : plus C ⥤ derived_category C :=
full_subcategory_inclusion _

end plus

end derived_category

namespace cochain_complex

def is_plus (K : cochain_complex C ℤ) : Prop :=
  ∃ (n : ℤ), K.is_strictly_ge n

instance zero_is_strictly_ge (n : ℤ) : is_strictly_ge (0 : cochain_complex C ℤ) n :=
⟨λ k hk, is_zero.of_iso (is_zero_zero _)
  (homological_complex.eval C (complex_shape.up ℤ) k).map_zero_object⟩

instance zero_is_strictly_le (n : ℤ) : is_strictly_le (0 : cochain_complex C ℤ) n :=
⟨λ k hk, is_zero.of_iso (is_zero_zero _)
  (homological_complex.eval C (complex_shape.up ℤ) k).map_zero_object⟩

lemma mapping_cone_is_strictly_le {K L : cochain_complex C ℤ} (f : K ⟶ L) (n k l : ℤ)
  [K.is_strictly_le k] [L.is_strictly_le l] (hk : k ≤ n+1) (hl : l ≤ n) :
  (mapping_cone f).is_strictly_le n :=
⟨λ i hi, begin
  simp only [mapping_cone.X_is_zero_iff],
  split,
  { exact is_strictly_le.is_zero K k (i+1) (by linarith), },
  { exact is_strictly_le.is_zero L l i (by linarith), },
end⟩

lemma mapping_cone_is_strictly_ge {K L : cochain_complex C ℤ} (f : K ⟶ L) (n k l : ℤ)
  [K.is_strictly_ge k] [L.is_strictly_ge l] (hk : n+1 ≤ k) (hl : n ≤ l) :
  (mapping_cone f).is_strictly_ge n :=
⟨λ i hi, begin
  simp only [mapping_cone.X_is_zero_iff],
  split,
  { exact is_strictly_ge.is_zero K k (i+1) (by linarith), },
  { exact is_strictly_ge.is_zero L l i (by linarith), },
end⟩

lemma mapping_cone_is_plus {K L : cochain_complex C ℤ} (f : K ⟶ L)
  (hK : K.is_plus) (hL : L.is_plus) : (mapping_cone f).is_plus :=
begin
  obtain ⟨k, hK⟩ := hK,
  obtain ⟨l, hL⟩ := hL,
  haveI := hK,
  haveI := hL,
  exact ⟨min (k-1) l, mapping_cone_is_strictly_ge f _ k l
    (by linarith [min_le_left (k-1) l]) (min_le_right _ _)⟩,
end

variable (C)
abbreviation plus :=
full_subcategory (λ (K : cochain_complex C ℤ), cochain_complex.is_plus K)

namespace plus

variable {C}

abbreviation ι : plus C ⥤ cochain_complex C ℤ :=
full_subcategory_inclusion _

variable (C)

def shift_functor (k : ℤ) : plus C ⥤ plus C :=
full_subcategory.lift _ (ι ⋙ shift_functor _ k) (λ K, begin
  obtain ⟨n, hn⟩ := K.2,
  haveI := hn,
  refine ⟨n-k, _⟩,
  dsimp,
  exact shift_is_strict_ge K.1 n k (n-k) (by linarith),
end)

instance : has_shift (plus C) ℤ :=
has_shift_of_fully_faithful ι (shift_functor C)
  (λ n, full_subcategory.lift_comp_inclusion _ _ _)

end plus

end cochain_complex

open category_theory.triangulated

namespace homotopy_category

variable (C)

def is_plus : set (homotopy_category C (complex_shape.up ℤ)) :=
λ K, cochain_complex.is_plus K.1

abbreviation plus :=
full_subcategory (homotopy_category.is_plus C)

instance plus_is_triangulated_subcategory' :
  category_theory.triangulated.is_triangulated_subcategory' (is_plus C) :=
{ zero := begin
    refine ⟨⟨0⟩, _, ⟨0, infer_instance⟩⟩,
    rw is_zero.iff_id_eq_zero,
    change (homotopy_category.quotient _ _).map (𝟙 0) = 0,
    simp only [id_zero, functor.map_zero],
  end,
  shift := begin
    rintro ⟨X⟩ n hX,
    exact ((cochain_complex.plus.shift_functor C n).obj ⟨X, hX⟩).2,
  end,
  distinguished_cocone_triangle' := begin
    rintro ⟨X⟩ ⟨Y⟩ hX hY ⟨f : X ⟶ Y⟩,
    refine ⟨_, _, _, _, ⟨_, _, f, ⟨iso.refl _⟩⟩⟩,
    exact cochain_complex.mapping_cone_is_plus f hX hY,
  end, }

namespace plus

variable {C}

abbreviation ι : plus C ⥤ homotopy_category C (complex_shape.up ℤ) :=
full_subcategory_inclusion _

variable (C)

def homology_functor (n : ℤ) : plus C ⥤ C :=
ι ⋙ homotopy_category.homology_functor C (complex_shape.up ℤ) n

def quasi_isomorphisms : morphism_property (plus C) :=
  λ K L φ, ∀ (n : ℤ), is_iso ((homology_functor C n).map φ)

end plus

end homotopy_category

namespace derived_category

namespace plus

def Qh : homotopy_category.plus C ⥤ derived_category.plus C :=
full_subcategory.lift _ (homotopy_category.plus.ι ⋙ Qh)
begin
  rintro ⟨⟨K⟩, n, hn⟩,
  refine ⟨n, (_ : (Q.obj K).is_ge n)⟩,
  rw ← cochain_complex.is_ge_iff_Q_obj_is_ge,
  dsimp at hn,
  haveI := hn,
  exact cochain_complex.is_ge_of_is_strictly_ge K n,
end

end plus

end derived_category
