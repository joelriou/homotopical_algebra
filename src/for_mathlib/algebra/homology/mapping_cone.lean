import for_mathlib.algebra.homology.twist_cocycle
import algebra.homology.quasi_iso

noncomputable theory
open category_theory category_theory.category category_theory.limits

namespace cochain_complex

variables {C : Type*} [category C]

section preadditive

variables [preadditive C]
  {F G : cochain_complex C ℤ} [∀ p, has_binary_biproduct (F.X (p+1-(0 : ℤ))) (G.X p)]
  (φ : F ⟶ G)

def mapping_cone : cochain_complex C ℤ :=
hom_complex.twist (hom_complex.cocycle.of_hom φ)

def ι_mapping_cone : G ⟶ mapping_cone φ :=
hom_complex.cocycle.hom_of
  (hom_complex.twist.lift_cocycle (hom_complex.cocycle.of_hom φ) 0
    (hom_complex.cocycle.of_hom (𝟙 G)) (add_comm 0 1)
    (show (-1 : ℤ) + 1 = 0, by linarith) 1 (zero_add 1) (by simp))

end preadditive

section abelian

variables [abelian C] {S : short_complex (cochain_complex C ℤ)} (ex : S.short_exact)

instance (n : ℤ) :
  preserves_finite_limits (homological_complex.eval C (complex_shape.up ℤ) n) := sorry
instance (n : ℤ) :
  preserves_finite_colimits (homological_complex.eval C (complex_shape.up ℤ) n) := sorry

include ex


lemma degreewise_exact (n : ℤ) :
  (S.map (homological_complex.eval C (complex_shape.up ℤ) n)).short_exact :=
ex.map_of_exact (homological_complex.eval C (complex_shape.up ℤ) n)

def from_mapping_cone_of_ses : mapping_cone S.f ⟶ S.X₃ :=
hom_complex.cocycle.hom_of
  (hom_complex.twist.desc_cocycle _ (0 : hom_complex.cochain _ _ (-1))
    (hom_complex.cocycle.of_hom S.g) (by linarith) (add_zero 0).symm
      (by simp only [hom_complex.δ_zero, hom_complex.ε_0, hom_complex.cocycle.of_hom_coe,
        one_zsmul, ← hom_complex.cochain.of_hom_comp, S.zero, hom_complex.cochain.of_hom_zero]))

lemma from_mapping_cone_of_ses_quasi_iso : quasi_iso (from_mapping_cone_of_ses ex) :=
⟨λ n, begin
  sorry,
end⟩

end abelian

end cochain_complex
