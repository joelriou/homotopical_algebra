import for_mathlib.algebra.homology.trunc

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

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
