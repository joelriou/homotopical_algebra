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

def δ' : (single_functor C 0).obj A ⟶ (single_functor C (-1)).obj B :=
-inv (Q.map e.σ) ≫ Q.map e.π

lemma δ'_eq : e.δ' = -inv (Q.map e.σ) ≫ Q.map e.π := rfl

lemma δ'_eq' : e.δ' = Q.map e.ι ≫ inv (Q.map e.σ') :=
by simp only [δ', ← cancel_epi (Q.map e.σ), ← cancel_mono (Q.map e.σ'), assoc,
  is_iso.hom_inv_id_assoc, preadditive.comp_neg, preadditive.neg_comp, is_iso.inv_hom_id,
  comp_id, ← Q.map_comp, derived_category.Q_map_eq_of_homotopy _ _ e.homotopy_πσ'_σι,
  functor.map_neg, neg_neg]

lemma δ_eq'' : e.δ' = (short_complex.short_exact.extension e.ex).δ' := rfl

def δ : (single_functor C 0).obj A ⟶ ((single_functor C 0).obj B)⟦(1 : ℤ)⟧ :=
e.δ' ≫ (single_functor_shift_iso C 0 1 (-1) (neg_add_self 1)).symm.hom.app B

def triangle : pretriangulated.triangle (derived_category C) :=
pretriangulated.triangle.mk ((single_functor C 0).map e.i) ((single_functor C 0).map e.p) e.δ

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

@[reassoc]
lemma δ'_naturality :
  ex₁.extension.δ' ≫ (single_functor C (-1)).map φ.τ₁ =
    (single_functor C 0).map φ.τ₃ ≫ ex₂.extension.δ' :=
begin
  dsimp only [extension.δ', single_functor, functor.comp_map],
  have hσ := Q.congr_map (σ_naturality φ ex₁ ex₂),
  have hπ := Q.congr_map (π_naturality φ ex₁ ex₂),
  simp only [Q.map_comp, ← cancel_mono (inv (Q.map ex₂.extension.σ)), assoc,
    is_iso.hom_inv_id, comp_id] at hσ,
  simp only [Q.map_comp] at hπ,
  simp only [← cancel_epi (Q.map ex₁.extension.σ), assoc, is_iso.hom_inv_id_assoc,
    hπ, ← hσ, preadditive.comp_neg, preadditive.neg_comp],
end

@[reassoc]
lemma δ_naturality :
  ex₁.extension.δ ≫ ((single_functor C 0).map φ.τ₁)⟦1⟧' =
    (single_functor C 0).map φ.τ₃ ≫ ex₂.extension.δ :=
begin
  dsimp only [extension.triangle, pretriangulated.triangle.mk, extension.δ, iso.symm],
  simpa only [← δ'_naturality_assoc φ ex₁ ex₂, assoc, nat_trans.naturality],
end

lemma triangle_map : ex₁.extension.triangle ⟶ ex₂.extension.triangle :=
{ hom₁ := (single_functor C 0).map φ.τ₁,
  hom₂ := (single_functor C 0).map φ.τ₂,
  hom₃ := (single_functor C 0).map φ.τ₃,
  comm₁' := by simpa only [functor.map_comp] using (single_functor C 0).congr_map φ.comm₁₂.symm,
  comm₂' := by simpa only [functor.map_comp] using (single_functor C 0).congr_map φ.comm₂₃.symm,
  comm₃' := δ_naturality φ ex₁ ex₂, }

end naturality

end extension

namespace extensions

variables {A B : C} (e : extension A B)

def δ : extensions A B → ((single_functor C 0).obj A ⟶
  ((single_functor C 0).obj B)⟦(1 : ℤ)⟧) :=
quot.lift extension.δ begin
  rintros E₁ E₂ ⟨e⟩,
  have eq := extension.δ_naturality
    ((extension.to_short_exact_sequence_functor A B).map e.hom) E₁.ex E₂.ex,
  dsimp at eq,
  simpa only [category_theory.functor.map_id, id_comp, comp_id] using eq,
end

variable (C)

@[simps]
def δ_nat_trans : extensions_functor C ⟶
  ((single_functor C 0).op ⋙ (single_functor C 0 ⋙ shift_functor _ (1 : ℤ) ⋙ yoneda).flip).flip :=
{ app := λ B,
  { app := λ A, extensions.δ,
    naturality' := λ A₁ A₂ π, begin
      ext e,
      obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' e,
      have eq := extension.δ_naturality (E.pull_short_complex π.unop)
        ((E.pull π.unop).ex) E.ex,
      dsimp at eq,
      simpa only [category_theory.functor.map_id, comp_id] using eq,
    end, },
  naturality' := begin
    rintro B₁ B₂ ι,
    ext A e,
    induction A using opposite.rec,
    obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' e,
    have eq := extension.δ_naturality (E.push_short_complex ι) E.ex (E.push ι).ex,
    dsimp at eq,
    simpa only [category_theory.functor.map_id, id_comp] using eq.symm,
  end, }

end extensions

end category_theory.abelian
