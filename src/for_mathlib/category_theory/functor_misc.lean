import category_theory.functor.basic
import category_theory.eq_to_hom

namespace category_theory

open category

namespace functor

lemma congr_map_conjugate {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (h : F₁ = F₂) {X Y : C} (f : X ⟶ Y) :
  F₁.map f = eq_to_hom (by rw h) ≫ F₂.map f ≫ eq_to_hom (by rw h) :=
begin
  subst h,
  simp only [eq_to_hom_refl, comp_id, id_comp],
end

end functor

lemma is_iso_map_iff_of_nat_iso {C D : Type*} [category C] [category D]
  {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
  is_iso (F₁.map f) ↔ is_iso (F₂.map f) :=
begin
  revert F₁ F₂,
  suffices : ∀ {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) (hf : is_iso (F₁.map f)), is_iso (F₂.map f),
  { exact λ F₁ F₂ e, ⟨this e, this e.symm⟩, },
  introsI F₁ F₂ e hf,
  refine is_iso.mk ⟨e.inv.app Y ≫ category_theory.inv (F₁.map f) ≫ e.hom.app X, _, _⟩,
  { simp only [nat_trans.naturality_assoc, is_iso.hom_inv_id_assoc, iso.inv_hom_id_app], },
  { simp only [assoc, ← e.hom.naturality, is_iso.inv_hom_id_assoc, iso.inv_hom_id_app], },
end

end category_theory
