import algebra.homology.homological_complex

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

namespace hom

def pull_homological_complex {ι₁ ι₂ : Type*} {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂}
  (φ : hom c₁ c₂) : homological_complex V c₂ ⥤ homological_complex V c₁ :=
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

end hom

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

def obj_X_eq_zero (K : homological_complex V (c.pull f hf)) (i : ι) (hi : ∀ (j : ι'), i ≠ f j) :
  obj_X c f hf K i = 0 :=
begin
  dsimp,
  split_ifs,
  { exfalso,
    cases h with j hj,
    exact hi j hj, },
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
  obj_d c f hf K i j = eq_to_hom sorry ≫ K.d i' j' ≫ eq_to_hom sorry :=
begin
  sorry
end

@[simp]
def map_f {K L : homological_complex V (c.pull f hf)} (g : K ⟶ L) (i : ι) :
  obj_X c f hf K i ⟶ obj_X c f hf L i :=
begin
  by_cases ∃ (j : ι'), i = f j,
  { refine eq_to_hom (obj_X_eq_X c f hf K i h.some h.some_spec) ≫ g.f h.some ≫
      (eq_to_hom (obj_X_eq_X c f hf L i h.some h.some_spec).symm), },
  { exact 0, },
end

end inclusion

def inclusion :
  homological_complex V (c.pull f hf) ⥤ homological_complex V c :=
{ obj := λ K,
  { X := inclusion.obj_X c f hf K,
    d := inclusion.obj_d c f hf K,
    shape' := λ i j hij, begin
      simp only [inclusion.obj_d],
      split_ifs,
      { rw [h.1.some_spec] at hij,
        conv at hij { congr, congr, skip, skip, rw h.2.some_spec, },
        rw [K.shape h.1.some h.2.some hij, zero_comp, comp_zero], },
      { refl, },
    end,
    d_comp_d' := sorry, --λ i j k hij hjk, begin
  },
  map := sorry,
  map_id' := sorry,
  map_comp' := sorry, }
#exit


end complex_shape

namespace homological_complex

variables (V) (c)

namespace trunc

/-
@[simps]
def functor (ι' : set ι) : homological_complex V c ⥤ homological_complex V (c.trunc ι') :=
{ obj := λ K,
  { X := λ i, K.X i.1,
    d := λ i j, K.d i.1 j.1,
    shape' := λ i j hij, K.shape i.1 j.1 hij,
    d_comp_d' := λ i j k hij hjk, K.d_comp_d i.1 j.1 k.1, },
  map := λ K L f, 
  { f := λ i, f.f i.1,
    comm' := λ i j hij, f.comm i j, },
  map_id' := λ K, rfl,
  map_comp' := λ K L M f g, rfl, }-/

/-namespace inclusion

@[simp]
def obj_X (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i : ι) : V :=
begin
  by_cases hi : i ∈ ι',
  { exact K.X ⟨i, hi⟩, },
  { exact 0, },
end

def obj_X_eq_X (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i : ι) (hi : i ∈ ι') :
  obj_X V c ι' K i = K.X ⟨i, hi⟩ :=
by { dsimp, split_ifs, refl, }

def obj_X_eq_zero (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i : ι) (hi : ¬i ∈ ι') :
  obj_X V c ι' K i = 0 :=
by { dsimp, split_ifs, refl, }

@[simp]
def obj_d (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i j : ι) :
  obj_X V c ι' K i ⟶ obj_X V c ι' K j :=
begin
  by_cases h : (i ∈ ι') ∧ (j ∈ ι'),
  { exact eq_to_hom (obj_X_eq_X V c ι' K i h.1) ≫ K.d ⟨i, h.1⟩ ⟨j, h.2⟩ ≫ eq_to_hom (obj_X_eq_X V c ι' K j h.2).symm, },
  { exact 0, },
end

def obj_d_eq_d (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i j : ι) (hi : i ∈ ι') (hj : j ∈ ι') :
  obj_d V c ι' K i j = eq_to_hom (obj_X_eq_X V c ι' K i hi) ≫ K.d ⟨i, hi⟩ ⟨j, hj⟩ ≫ eq_to_hom (obj_X_eq_X V c ι' K j hj).symm :=
begin
  simp only [obj_d],
  split_ifs,
  { refl, },
  { exfalso,
    exact h ⟨hi, hj⟩,}
end

def obj_d_eq_zero (ι' : set ι) (K : homological_complex V (c.trunc ι')) (i j : ι) (hij : ¬(i ∈ ι' ∧ j ∈ ι')) :
  obj_d V c ι' K i j = 0 :=
by { simp only [obj_d], split_ifs, refl, }

@[simp]
def map_f (ι' : set ι) {K L : homological_complex V (c.trunc ι')} (f : K ⟶ L) (i : ι):
  obj_X V c ι' K i ⟶ obj_X V c ι' L i :=
begin
  by_cases i ∈ ι',
  { exact eq_to_hom (inclusion.obj_X_eq_X V c ι' K i h) ≫ f.f ⟨i, h⟩ ≫
      eq_to_hom (inclusion.obj_X_eq_X V c ι' L i h).symm, },
  { exact 0, },
end

lemma map_comm (ι' : set ι) {K L : homological_complex V (c.trunc ι')} (f : K ⟶ L) (i j : ι) (hij : c.rel i j) :
inclusion.map_f V c ι' f i ≫ obj_d V c ι' L i j = obj_d V c ι' K i j ≫ inclusion.map_f V c ι' f j :=
begin
  simp only [inclusion.obj_d, inclusion.map_f],
  by_cases hi : i ∈ ι',
  by_cases hj : j ∈ ι',
  { have hij : i ∈ ι' ∧ j ∈ ι' := ⟨hi, hj⟩,
    split_ifs,
    simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp, hom.comm_assoc], },
  { have hij : ¬(i ∈ ι' ∧ j ∈ ι'),
    { intro h,
      exact hj h.2, },
    split_ifs,
    simp only [comp_zero], },
  { have hij : ¬(i ∈ ι' ∧ j ∈ ι'),
    { intro h,
      exact hi h.1, },
    split_ifs,
    repeat { erw zero_comp, }, },
end

end inclusion

@[simps]
def inclusion (ι' : set ι) : homological_complex V (c.trunc ι') ⥤ homological_complex V c :=
{ obj := λ K,
  { X := inclusion.obj_X V c ι' K,
    d := inclusion.obj_d V c ι' K,
    shape' := λ i j hij, begin
      simp only [inclusion.obj_d],
      split_ifs,
      { rw [K.shape ⟨i, h.1⟩ ⟨j, h.2⟩ hij, zero_comp, comp_zero], },
      { refl, },
    end,
    d_comp_d' := λ i j k hij hjk, begin
      simp only [inclusion.obj_d],
      split_ifs,
      { simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp,
          d_comp_d_assoc, zero_comp, comp_zero], },
      all_goals { simp only [comp_zero, zero_comp], },
    end, },
  map := λ K L f,
  { f := λ i, inclusion.map_f V c ι' f i,
    comm' := λ i j hij, inclusion.map_comm _ _ _ _ _ _ hij, },
  map_id' := λ K, begin
    ext i,
    dsimp,
    split_ifs,
    { simp only [id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { apply is_terminal.hom_ext,
      split_ifs,
      exact has_zero_object.zero_is_terminal, },
  end,
  map_comp' := λ K L M f g, begin
    ext i,
    dsimp,
    split_ifs,
    { simp only [assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, id_comp], },
    { rw zero_comp, },
  end, }

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

