import for_mathlib.category_theory.abelian.extensions
import for_mathlib.algebra.homology.double

noncomputable theory

open category_theory category_theory.limits category_theory.category derived_category

variables {C : Type*} [category C] [abelian C]

@[simps]
def category_theory.short_complex.short_exact.extension
  {S : short_complex C} (ex : S.short_exact) :
  category_theory.abelian.extension S.X₃ S.X₁ :=
{ X := S.X₂,
  i := S.f,
  p := S.g,
  w := S.zero,
  ex := begin
    refine (short_complex.short_exact.iff_of_iso _).1 ex,
    exact (short_complex.mk_iso (iso.refl _) (iso.refl _) (iso.refl _) (by tidy) (by tidy)),
  end, }

open category_theory category_theory.limits category_theory.category derived_category

namespace category_theory.abelian

namespace extension

variables {A B : C} (e : extension A B)

def σ := cochain_complex.double.σ (neg_add_self 1) e.w
def ι := cochain_complex.double.ι (neg_add_self 1) e.p
def σ' := cochain_complex.double.σ' (neg_add_self 1) e.w
def π := cochain_complex.double.π (neg_add_self 1) e.i

def homotopy_πσ'_σι : homotopy (e.π ≫ e.σ') (-e.σ ≫ e.ι)  :=
cochain_complex.double.homotopy_πσ'_σι (neg_add_self 1) e.w

instance : quasi_iso e.σ :=
cochain_complex.double.quasi_iso_σ (neg_add_self 1) e.w e.ex

instance : quasi_iso e.σ' :=
cochain_complex.double.quasi_iso_σ' (neg_add_self 1) e.w e.ex

def ext_class : (single_functor C 0).obj A ⟶ (single_functor C (-1)).obj B :=
inv (Q.map e.σ) ≫ Q.map e.π

lemma ext_class_eq : e.ext_class = inv (Q.map e.σ) ≫ Q.map e.π := rfl

lemma ext_class_eq' : e.ext_class = -Q.map e.ι ≫ inv (Q.map e.σ') :=
by simp only [ext_class, ← cancel_epi (Q.map e.σ), ← cancel_mono (Q.map e.σ'), assoc,
  is_iso.hom_inv_id_assoc, preadditive.comp_neg, preadditive.neg_comp, is_iso.inv_hom_id,
  comp_id, ← Q.map_comp, derived_category.Q_map_eq_of_homotopy _ _ e.homotopy_πσ'_σι,
  functor.map_neg]

lemma ext_class_eq'' : e.ext_class = (short_complex.short_exact.extension e.ex).ext_class := rfl

section naturality

variables {S₁ S₂ : short_complex C} (φ : S₁ ⟶ S₂)
  (ex₁ : S₁.short_exact) (ex₂ : S₂.short_exact)

include φ ex₁ ex₂

@[reassoc]
lemma σ_naturality :
  ex₁.extension.σ ≫ (homological_complex.single C _ 0).map φ.τ₃ =
    cochain_complex.double.map (neg_add_self 1) S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
      ex₂.extension.σ :=
begin
  refine cochain_complex.to_single_ext _ _ 0 _,
  { dsimp only [short_complex.short_exact.extension, extension.σ],
    simp only [homological_complex.comp_f, cochain_complex.double.σ_f₂,
      homological_complex.single_obj_X_self_inv, eq_to_hom_refl,
      comp_id, homological_complex.single_map_f_self, homological_complex.single_obj_X_self_hom,
      assoc, cochain_complex.double.map_f₂, iso.inv_hom_id_assoc, iso.cancel_iso_hom_left,
      φ.comm₂₃],
    erw id_comp, },
end

@[reassoc]
lemma π_naturality :
  ex₁.extension.π ≫ (homological_complex.single C _ (-1 : ℤ)).map φ.τ₁ =
    cochain_complex.double.map (neg_add_self 1) S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫
    ex₂.extension.π :=
begin
  refine cochain_complex.to_single_ext _ _ (-1) _,
  { dsimp only [short_complex.short_exact.extension, extension.π],
    simp only [homological_complex.comp_f, cochain_complex.double.π_f, eq_to_hom_refl,
      cochain_complex.double.desc.f₁, comp_id, homological_complex.single_map_f_self,
      homological_complex.single_obj_X_self_hom, homological_complex.single_obj_X_self_inv,
      cochain_complex.double.map_f₁, assoc, iso.inv_hom_id, iso.cancel_iso_hom_left],
    apply id_comp, },
end

lemma ext_class_naturality :
  ex₁.extension.ext_class ≫ (single_functor C (-1)).map φ.τ₁ =
    (single_functor C 0).map φ.τ₃ ≫ ex₂.extension.ext_class :=
begin
  dsimp only [extension.ext_class, single_functor, functor.comp_map],
  have hσ := Q.congr_map (σ_naturality φ ex₁ ex₂),
  have hπ := Q.congr_map (π_naturality φ ex₁ ex₂),
  simp only [Q.map_comp, ← cancel_mono (inv (Q.map ex₂.extension.σ)), assoc,
    is_iso.hom_inv_id, comp_id] at hσ,
  simp only [Q.map_comp] at hπ,
  simp only [← cancel_epi (Q.map ex₁.extension.σ), assoc, is_iso.hom_inv_id_assoc,
    hπ, ← hσ],
end

end naturality

end extension

namespace extensions

variables {A B : C} (e : extension A B)

lemma ext_class : extensions A B → ((single_functor C 0).obj A ⟶ (single_functor C (-1)).obj B) :=
quot.lift extension.ext_class begin
  rintros E₁ E₂ ⟨e⟩,
  have eq := extension.ext_class_naturality
    ((extension.to_short_exact_sequence_functor A B).map e.hom) E₁.ex E₂.ex,
  dsimp at eq,
  simpa only [category_theory.functor.map_id, id_comp, comp_id] using eq,
end

end extensions

end category_theory.abelian
