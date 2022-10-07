import category_theory.shift

noncomputable theory

namespace category_theory

open category

namespace monoidal_functor


variables {C D : Type*} [category C] [monoidal_category C]
  [category D] [monoidal_category D]
  (F : monoidal_functor C D) (comm : ∀ (X Y : C), X ⊗ Y ≅ Y ⊗ X)
  (commσ : ∀ (X Y Z : C), comm Z (X ⊗ Y) ≪≫ α_ X Y Z =
    (α_ Z X Y).symm ≪≫ (comm Z X ⊗ (iso.refl Y)) ≪≫ α_ X Z Y ≪≫ (iso.refl X ⊗ comm Z Y))

def associativity_iso_eq (X Y Z : C) :
  (F.μ_iso X Y ⊗ (iso.refl (F.obj Z))) ≪≫ F.μ_iso (X ⊗ Y) Z ≪≫
  F.map_iso (α_ X Y Z) =
    α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫
   (iso.refl (F.obj X) ⊗ (F.μ_iso Y Z)) ≪≫ F.μ_iso X (Y ⊗ Z) :=
begin
  ext,
  apply F.associativity
end

lemma apply_α (X Y Z : C) : F.map (α_ X Y Z).hom =
  (F.μ_iso (X ⊗ Y) Z).inv ≫ ((F.μ_iso X Y).inv ⊗ 𝟙 (F.obj Z)) ≫
  (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
  (𝟙 (F.obj X) ⊗ (F.μ_iso Y Z).hom) ≫ (F.μ_iso X (Y ⊗ Z)).hom :=
by simpa only [← cancel_epi ((F.μ_iso (X ⊗ Y) Z).hom),
    ← cancel_epi ((F.μ_iso X Y).hom ⊗ 𝟙 (F.obj Z)),
    iso.hom_inv_id_assoc, assoc, ← monoidal_category.tensor_comp_assoc,
    iso.hom_inv_id, id_comp, monoidal_category.tensor_id]
    using F.associativity X Y Z

lemma apply_α_inv (X Y Z : C) : F.map (α_ X Y Z).inv =
  (F.μ_iso X (Y ⊗ Z)).inv ≫ (𝟙 (F.obj X) ⊗ (F.μ_iso Y Z).inv) ≫
  (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
  ((F.μ_iso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫
  (F.μ_iso (X ⊗ Y) Z).hom :=
begin
  rw [← cancel_mono (F.map (α_ X Y Z).hom), ← F.map_comp, iso.inv_hom_id, F.map_id, apply_α],
  simp only [assoc, iso.hom_inv_id_assoc, ← monoidal_category.tensor_comp_assoc,
      iso.hom_inv_id, comp_id, monoidal_category.tensor_id, id_comp,
      iso.inv_hom_id_assoc, iso.inv_hom_id],
end

def comm' (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj Y ⊗ F.obj X :=
F.μ_iso X Y ≪≫ F.map_iso (comm X Y) ≪≫ (F.μ_iso Y X).symm

include commσ

lemma compatibility (X Y Z : C) :
  F.comm' comm Z (X ⊗ Y) ≪≫
    ((F.μ_iso X Y).symm ⊗ (iso.refl (F.obj Z))) ≪≫ α_ _ _ _ =
    (iso.refl (F.obj Z) ⊗ (F.μ_iso X Y).symm) ≪≫
    (α_ _ _ _).symm ≪≫
    (F.comm' comm Z X ⊗ iso.refl (F.obj Y)) ≪≫ α_ _ _ _ ≪≫
    (iso.refl (F.obj X) ⊗ F.comm' comm Z Y) :=
begin
  ext,
  have eq := (F.μ_iso Z (X ⊗ Y)).hom ≫=
    F.congr_map (congr_arg iso.hom (commσ X Y Z)),
  dsimp only [iso.trans, iso.symm, iso.refl, comm', functor.map_iso,
    tensor_iso_hom] at ⊢ eq,
  simp only [F.map_comp, assoc] at eq ⊢,
  simp only [F.apply_α X Y Z, ← cancel_mono ((F.μ_iso X (Y ⊗ Z)).inv), assoc,
    iso.hom_inv_id, comp_id,
    ← cancel_mono ((𝟙 (F.to_lax_monoidal_functor.to_functor.obj X) ⊗ (F.μ_iso Y Z).inv)),
    ← monoidal_category.tensor_comp, monoidal_category.tensor_id] at eq,
  rw eq, clear eq,
  rw F.apply_α_inv,
  simp only [assoc],
  erw iso.hom_inv_id_assoc,
  congr' 2,
  simp only [monoidal_category.comp_tensor_id, monoidal_category.id_tensor_comp, assoc],
  congr' 1,
  rw F.apply_α,
  simp only [← assoc],
  congr' 1,
  simp only [assoc],
  conv_lhs { rw [← assoc, ← assoc, ← assoc], },
  conv_rhs { rw ← assoc, },
  congr' 3,
  { simp only [μ_iso_hom, assoc, ← F.μ_natural_assoc, functor.map_id, μ_hom_inv_id, comp_id], },
  { simp only [μ_iso_hom, ← F.μ_natural_assoc, functor.map_id, μ_hom_inv_id, comp_id], },
end

end monoidal_functor

section

variables (C : Type*) [category C] {A : Type*} [add_comm_monoid A]
  [has_shift C A]

def shift_functor_add_comm (a₁ a₂ : A) :
  shift_functor C a₁ ⋙ shift_functor C a₂ ≅
  shift_functor C a₂ ⋙ shift_functor C a₁ :=
(shift_functor_add C a₁ a₂).symm ≪≫ eq_to_iso (by rw add_comm a₁ a₂) ≪≫ (shift_functor_add C a₂ a₁)

@[simp]
lemma shift_functor_add_comm_hom_app (a₁ a₂ : A) (X : C) :
  (shift_functor_add_comm C a₁ a₂).hom.app X  = (shift_functor_add C a₁ a₂).inv.app X ≫
  eq_to_hom (by rw add_comm a₁ a₂) ≫ (shift_functor_add C a₂ a₁).hom.app X :=
begin
  dsimp only [shift_functor_add_comm, iso.trans, eq_to_iso],
  simp only [iso.symm_hom, nat_trans.comp_app, eq_to_hom_app],
end

@[simp]
lemma shift_functor_add_comm_eq_refl (a : A) :
  shift_functor_add_comm C a a = iso.refl _ :=
begin
  ext X,
  dsimp only [shift_functor_add_comm, iso.trans, eq_to_iso, iso.symm, iso.refl],
  rw [eq_to_hom_refl, id_comp, iso.inv_hom_id],
end

local attribute [instance, reducible] endofunctor_monoidal_category
local attribute [reducible] discrete.add_monoidal

lemma shift_compatibility (a₁ a₂ a₃ : A) (X : C) :
  (shift_functor_add_comm C a₃ (a₁ + a₂)).hom.app X ≫
  (shift_functor C a₃).map ((shift_functor_add C a₁ a₂).app X).hom =
  (shift_functor_add C a₁ a₂).hom.app ((shift_functor C a₃).obj X) ≫
  (shift_functor C a₂).map ((shift_functor_add_comm C a₃ a₁).hom.app X) ≫
  (shift_functor_add_comm C a₃ a₂).hom.app ((shift_functor C a₁).obj X) :=
begin
  let Acomm : Π (a₁ a₂ : discrete A), a₁ ⊗ a₂ ≅ a₂ ⊗ a₁,
  { rintros ⟨a₁⟩ ⟨a₂⟩,
    refine eq_to_iso _,
    dsimp,
    rw add_comm, },
  have Acommeq : Π (a₁ a₂ : A) (X' : C),
    ((shift_monoidal_functor C A).comm' Acomm ⟨a₁⟩ ⟨a₂⟩).hom.app X' =
     (shift_functor_add_comm C a₁ a₂).hom.app X',
  { intros a₁ a₂ X',
    dsimp [shift_functor_add_comm, monoidal_functor.comm'],
    rw eq_to_hom_map, },
  have h₁ := (shift_monoidal_functor C A).compatibility
    Acomm (by tidy) ⟨a₁⟩ ⟨a₂⟩ ⟨a₃⟩, swap,
  have h₂ := congr_arg (λ (e : _ ≅ _), e.hom) h₁,
  have h₃ := congr_app h₂ X,
  clear h₁ h₂,
  dsimp [iso.trans] at h₃,
  simpa only [Acommeq, id_comp, comp_id, functor.map_id, assoc] using h₃,
end

end

end category_theory
