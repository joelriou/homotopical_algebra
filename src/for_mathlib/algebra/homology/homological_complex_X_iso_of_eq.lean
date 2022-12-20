import algebra.homology.homological_complex

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables (C : Type*) [category C] [preadditive C]

namespace homological_complex

section

variables {C} {ι : Type*} {c : complex_shape ι}

def X_iso_of_eq (K : homological_complex C c) {n n' : ι} (h : n = n') :
  K.X n ≅ K.X n' :=
eq_to_iso (by congr')

@[simp]
lemma X_iso_of_eq_refl (K : homological_complex C c) (n : ι) :
  K.X_iso_of_eq (rfl : n = n) = iso.refl _ :=
begin
  dsimp only [X_iso_of_eq],
  simp,
end

@[simp, reassoc]
lemma X_iso_of_eq_hom_comp_d (K : homological_complex C c) {n n' : ι} (h : n = n') (n'' : ι) :
  (K.X_iso_of_eq h).hom ≫ K.d n' n'' = K.d n n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_comp_d (K : homological_complex C c) {n n' : ι} (h : n = n') (n'' : ι) :
  (K.X_iso_of_eq h).inv ≫ K.d n n'' = K.d n' n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma d_comp_X_iso_of_eq_hom (K : homological_complex C c) (n : ι) {n' n'' : ι} (h : n' = n'') :
  K.d n n' ≫ (K.X_iso_of_eq h).hom = K.d n n'' :=
by { subst h, simp, }

@[simp, reassoc]
lemma d_comp_X_iso_of_eq_inv (K : homological_complex C c) (n : ι) {n' n'' : ι} (h : n' = n'') :
  K.d n n'' ≫ (K.X_iso_of_eq h).inv = K.d n n' :=
by { subst h, simp, }

@[reassoc]
lemma X_iso_of_eq_hom_naturality {K L : homological_complex C c} (φ : K ⟶ L) {n n' : ι}
  (h : n = n') :
  φ.f n ≫ (L.X_iso_of_eq h).hom = (K.X_iso_of_eq h).hom ≫ φ.f n' :=
by { subst h, simp, }

@[reassoc]
lemma X_iso_of_eq_inv_naturality {K L : homological_complex C c} (φ : K ⟶ L) {n n' : ι}
  (h : n = n') :
  φ.f n' ≫ (L.X_iso_of_eq h).inv = (K.X_iso_of_eq h).inv ≫ φ.f n :=
by { subst h, simp, }

@[simp, reassoc]
lemma X_iso_of_eq_hom_hom (K : homological_complex C c) {n n' n'' : ι} (h : n = n') (h' : n' = n'') :
  (K.X_iso_of_eq h).hom ≫ (K.X_iso_of_eq h').hom = (K.X_iso_of_eq (h.trans h')).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_hom_inv (K : homological_complex C c) {n n' n'' : ι} (h : n = n') (h' : n'' = n') :
  (K.X_iso_of_eq h).hom ≫ (K.X_iso_of_eq h').inv = (K.X_iso_of_eq (h.trans h'.symm)).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_hom (K : homological_complex C c) {n n' n'' : ι} (h : n' = n) (h' : n' = n'') :
  (K.X_iso_of_eq h).inv ≫ (K.X_iso_of_eq h').hom = (K.X_iso_of_eq (h.symm.trans h')).hom :=
by { substs h h', simp, }

@[simp, reassoc]
lemma X_iso_of_eq_inv_inv (K : homological_complex C c) {n n' n'' : ι} (h : n' = n) (h' : n'' = n') :
  (K.X_iso_of_eq h).inv ≫ (K.X_iso_of_eq h').inv = (K.X_iso_of_eq (h'.trans h)).inv :=
by { substs h h', simp, }

end

end homological_complex
