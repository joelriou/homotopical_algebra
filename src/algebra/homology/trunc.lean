import algebra.homology.homological_complex
import category_theory.limits.shapes.zero_objects

noncomputable theory
open_locale classical zero_object

open category_theory category_theory.limits category_theory.category

variables {V : Type*} [category V] [has_zero_morphisms V] [has_zero_object V]
variables {ι : Type*} (c : complex_shape ι)

namespace complex_shape

/-def trunc (ι' : set ι) : complex_shape ι' :=
{ rel := λ i j, c.rel i.1 j.1,
  next_eq := λ i j j' hj hj', by { ext, exact c.next_eq hj hj', },
  prev_eq := λ i i' j hi hi', by { ext, exact c.prev_eq hi hi', }, }-/

def pull {ι' : Type*} (f : ι' → ι) (hf : function.injective f) : complex_shape ι' :=
{ rel := λ i j, c.rel (f i) (f j),
  next_eq := λ i j j' hj hj', by { apply hf, exact c.next_eq hj hj', },
  prev_eq := λ i i' j hi hi', by { apply hf, exact c.prev_eq hi hi', }, }

structure hom {ι₁ ι₂ : Type*} (c₁ : complex_shape ι₁) (c₂ : complex_shape ι₂) :=
(f : ι₁ → ι₂)
(hf : ∀ (i j : ι₁), c₂.rel (f i) (f j) → c₁.rel i j)

def pull_hom {ι' : Type*} (f : ι' → ι) (hf : function.injective f) : hom (c.pull f hf) c :=
{ f := f,
  hf := λ i j h, h, }

end complex_shape

namespace homological_complex

def pull_homological_complex {ι₁ ι₂ : Type*} {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂}
  (φ : complex_shape.hom c₁ c₂) : homological_complex V c₂ ⥤ homological_complex V c₁ :=
{ obj := λ K,
  { X := λ i, K.X (φ.f i),
    d := λ i j, K.d (φ.f i) (φ.f j),
    shape' := λ i j hij, begin
      apply K.shape (φ.f i) (φ.f j),
      intro h,
      exact hij (φ.hf _ _ h),
    end,
    d_comp_d' := λ i j k hij hjk, K.d_comp_d _ _ _, },
  map := λ K L f, 
  { f := λ i, f.f (φ.f i),
    comm' := λ i j hij, f.comm _ _, },
  map_id' := λ K, rfl,
  map_comp' := λ K L M f g, rfl, }

variables {ι' : Type*} (f : ι' → ι) (hf : function.injective f)

namespace inclusion

@[simp]
def obj_X (K : homological_complex V (c.pull f hf)) (i : ι): V :=
begin
  by_cases ∃ (j : ι'), i = f j,
  { exact K.X h.some, },
  { exact 0, },
end

def obj_X_eq_X (K : homological_complex V (c.pull f hf)) (i : ι) (j : ι') (hij : i = f j) :
  obj_X c f hf K i = K.X j :=
begin
  dsimp,
  split_ifs,
  { congr,
    apply hf,
    symmetry,
    rw ← hij,
    exact h.some_spec, },
  { exfalso,
    apply h,
    use j,
    exact hij, },
end

def obj_X_eq_zero (K : homological_complex V (c.pull f hf)) (i : ι) (hi : ¬∃ (i' : ι'), i = f i') :
  obj_X c f hf K i = 0 :=
begin
  dsimp,
  split_ifs,
  { exfalso,
    exact hi h,},
  { refl, },
end

@[simp]
def obj_d (K : homological_complex V (c.pull f hf)) (i j : ι) :
  obj_X c f hf K i ⟶ obj_X c f hf K j :=
begin
  by_cases h : (∃ (i' : ι'), i = f i') ∧ (∃ (j' : ι'), j = f j'),
  { refine eq_to_hom (obj_X_eq_X c f hf K i h.1.some h.1.some_spec) ≫ K.d h.1.some h.2.some ≫
      eq_to_hom (obj_X_eq_X c f hf K j h.2.some h.2.some_spec).symm, },
  { exact 0, },
end

lemma obj_d_eq (K : homological_complex V (c.pull f hf)) (i j : ι) (i' j' : ι') (hi : i = f i') (hj : j = f j') :
  obj_d c f hf K i j = eq_to_hom (obj_X_eq_X _ _ _ _ _ _ hi) ≫ K.d i' j' ≫
    eq_to_hom (obj_X_eq_X _ _ _ _ _ _ hj).symm :=
begin
  dsimp only [obj_d],
  split_ifs,
  { subst hi,
    subst hj,
    have h₁ := hf h.1.some_spec.symm,
    have h₂ := hf h.2.some_spec.symm,
    congr', },
  { exfalso,
    apply h,
    exact ⟨⟨i', hi⟩, ⟨j', hj⟩⟩, },
end

lemma obj_d_eq_zero (K : homological_complex V (c.pull f hf)) (i j : ι)
  (hi : ¬∃ (i' : ι'), i = f i') : obj_d c f hf K i j = 0 :=
begin
  dsimp only [obj_d],
  split_ifs,
  { exfalso,
    exact hi h.1, },
  { refl, }
end

lemma obj_d_eq_zero' (K : homological_complex V (c.pull f hf)) (i j : ι)
  (hj : ¬∃ (j' : ι'), j = f j') : obj_d c f hf K i j = 0 :=
begin
  dsimp only [obj_d],
  split_ifs,
  { exfalso,
    exact hj h.2, },
  { refl, }
end

def obj (K : homological_complex V (c.pull f hf)) : homological_complex V c :=
{ X := obj_X c f hf K,
  d := obj_d c f hf K,
  shape' := λ i j hij, begin
    simp only [obj_d],
    split_ifs,
    { rw [h.1.some_spec] at hij,
      conv at hij { congr, congr, skip, skip, rw h.2.some_spec, },
      rw [K.shape h.1.some h.2.some hij, zero_comp, comp_zero], },
    { refl, },
  end,
  d_comp_d' := λ i j k hij hjk, begin
    by_cases hi : ∃ (i' : ι'), i = f i',
    { by_cases hj : ∃ (j' : ι'), j = f j',
      { by_cases hk : ∃ (k' : ι'), k = f k',
        { cases hi with i' hi',
          cases hj with j' hj',
          cases hk with k' hk',
          rw [obj_d_eq c f hf K i j i' j' hi' hj', obj_d_eq c f hf K j k j' k' hj' hk'],
          simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp, homological_complex.d_comp_d_assoc, zero_comp, comp_zero], },
        { rw [obj_d_eq_zero' c f hf K j k hk, comp_zero], }, },
      { rw [obj_d_eq_zero' c f hf K i j hj, zero_comp], }, },
    { rw [obj_d_eq_zero c f hf K i j hi, zero_comp], },
  end, }

@[simp]
def map_f {K L : homological_complex V (c.pull f hf)} (g : K ⟶ L) (i : ι) :
  obj_X c f hf K i ⟶ obj_X c f hf L i :=
begin
  by_cases ∃ (j : ι'), i = f j,
  { refine eq_to_hom (obj_X_eq_X c f hf K i h.some h.some_spec) ≫ g.f h.some ≫
      (eq_to_hom (obj_X_eq_X c f hf L i h.some h.some_spec).symm), },
  { exact 0, },
end

@[simp]
lemma map_f_eq {K L : homological_complex V (c.pull f hf)} (g : K ⟶ L) (i : ι) (i' : ι') (hi : i = f i') :
  map_f c f hf g i = eq_to_hom (obj_X_eq_X c f hf K i i' hi) ≫ g.f i' ≫
      (eq_to_hom (obj_X_eq_X c f hf L i i' hi).symm) :=
begin
  dsimp only [map_f],
  split_ifs,
  { have eq : h.some = i',
    { apply hf,
      rw ← hi,
      exact h.some_spec.symm, },
    congr', },
  { exfalso,
    apply h,
    exact ⟨i', hi⟩, },
end

@[simp]
lemma map_f_eq_zero {K L : homological_complex V (c.pull f hf)} (g : K ⟶ L) (i : ι) (hi : ¬∃ (i' : ι'), i = f i') :
  map_f c f hf g i = 0 :=
begin
  dsimp only [map_f],
  split_ifs,
  { exfalso,
    exact hi h, },
  { refl, },
end

@[simps]
def map {K L : homological_complex V (c.pull f hf)} (g : K ⟶ L) : obj c f hf K ⟶ obj c f hf L :=
{ f := map_f c f hf g,
  comm' := λ i j hij, begin
    by_cases hi : ∃ (i' : ι'), i = f i',
    { by_cases hj : ∃ (j' : ι'), j = f j',
      { cases hi with i' hi',
        cases hj with j' hj',
        dsimp only [obj],
        rw [map_f_eq c f hf g i i' hi', map_f_eq c f hf g j j' hj',
          obj_d_eq c f hf K i j i' j' hi' hj', obj_d_eq c f hf L i j i' j' hi' hj'],
        simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp, homological_complex.hom.comm_assoc], },
      { apply is_zero.eq_of_tgt,
        dsimp only [obj],
        rw obj_X_eq_zero c f hf L j hj,
        apply limits.is_zero_zero, }, },
    { apply is_zero.eq_of_src,
      dsimp only [obj],
      rw obj_X_eq_zero c f hf K i hi,
      apply limits.is_zero_zero, },  
  end }

end inclusion

def inclusion :
  homological_complex V (c.pull f hf) ⥤ homological_complex V c :=
{ obj := inclusion.obj c f hf,
  map := λ K L, inclusion.map c f hf,
  map_id' := λ K, begin
    ext i,
    dsimp only [inclusion.map],
    by_cases hi : ∃ (i' : ι'), i = f i',
    { cases hi with i' hi',
      simpa only [inclusion.map_f_eq c f hf _ i i' hi', homological_complex.id_f, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { apply is_zero.eq_of_src,
      rw inclusion.obj_X_eq_zero c f hf K i hi,
      apply limits.is_zero_zero, },   
  end,
  map_comp' := λ K L M g₁ g₂, begin
    ext i,
    simp only [homological_complex.comp_f],
    dsimp only [inclusion.map],
    by_cases hi : ∃ (i' : ι'), i = f i',
    { cases hi with i' hi',
      simp only [inclusion.map_f_eq c f hf _ i i' hi',
        homological_complex.comp_f, assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp], },
    { simp only [inclusion.map_f_eq_zero c f hf _ i hi, zero_comp], },
  end, }

end homological_complex

--def pull_homological_complex {ι₁ ι₂ : Type*} {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂}
--  (φ : complex_shape.hom c₁ c₂) : homological_complex V c₂ ⥤ homological_complex V c₁ :=


/-

lemma inclusion_comp_trunc (ι' : set ι) : inclusion V c ι' ⋙ functor V c ι' = 𝟭 _ :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    ext i,
    simp only [subtype.val_eq_coe, subtype.coe_prop, inclusion.map_f, functor.comp_map, functor_map_f, inclusion_map_f, dif_pos,
  functor.id_map, comp_f, eq_to_hom_f],
    have h : (⟨i.1, i.2⟩ : ι') = i,
    { simp only [subtype.val_eq_coe, subtype.coe_eta], },
    congr', },
  { intro K,
    apply homological_complex.ext,
    { intros i j hij,
      dsimp,
      have h : i.1 ∈ ι' ∧ j.1 ∈ ι' := ⟨i.2, j.2⟩,
      split_ifs with h',
      { rcases i with ⟨i, hi⟩,
        rcases j with ⟨j, hj⟩,
        simpa only [assoc, eq_to_hom_trans, eq_to_hom_refl, comp_id], },
      { exfalso,
        exact h' i.2, }, },
    { ext i,
      simp only [inclusion.obj_X, functor.comp_obj, functor_obj_X, subtype.val_eq_coe,
        inclusion_obj_X, subtype.coe_prop, subtype.coe_eta, dite_eq_ite, if_true,
          functor.id_obj], }, },
end-/

structure rebuild_preorder (c : complex_shape ι) (J : Type*) [preorder J] :=
(S : J → set ι) (hS₀ : monotone S)
(hS₁ : ∀ (n : ι), ∃ (j : J), n ∈ S j)
(hS₂ : ∀ (j₁ j₂ : J), ∃ (j₃ : J), j₁ ≤ j₃ ∧ j₂ ≤ j₃)

/-structure rebuild_datum {c : complex_shape ι} {J : Type*} [preorder J]
  (P : rebuild_preorder c J) :=
(K : Π (j : J), homological_complex V (c.trunc (P.S j)))
(hK : ∀ (j₁ j₂ : J) (hj₁j₂ : j₁ ≤ j₂), true)-/

end trunc

end homological_complex

