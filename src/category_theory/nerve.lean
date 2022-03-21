import algebraic_topology.simplicial_set
import category_theory.opposites
import category_theory.arrow_class

open category_theory
open category_theory.category
open opposite
open_locale simplicial

universes v u

lemma fin.eq_one_of_geq_one {i : fin 2} (hi : 1 ≤ i) : i = 1 := le_antisymm i.is_le hi

lemma fin.eq_one_of_neq_zero {i : fin 2} (hi : i ≠ 0) : i = 1 :=
begin
  apply fin.eq_one_of_geq_one,
  by_contradiction,
  apply hi,
  ext,
  simpa only [fin.le_iff_coe_le_coe, fin.coe_one, not_le, nat.lt_one_iff] using h,
end

namespace category_theory

namespace arrow

@[simps]
def composition {D : Type*} [category D] (w₁ w₂ : arrow D) (e : w₁.right = w₂.left) : arrow D :=
{ left := w₁.left,
  right := w₂.right,
  hom := w₁.hom ≫ eq_to_hom e ≫ w₂.hom }

@[simp]
lemma map_arrow_comp {D E : Type*} [category D] [category E] (F : D ⥤ E) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map_arrow.obj (arrow.mk (f ≫ g)) = composition (F.map_arrow.obj (arrow.mk f)) (F.map_arrow.obj (arrow.mk g)) rfl :=
begin
  ext,
  { simp only [functor.map_arrow_obj_hom, arrow.mk_hom, functor.map_comp, eq_to_hom_refl, composition_hom, id_comp, comp_id], },
  { refl, },
  { refl, },
end

@[simp]
lemma map_arrow_of_mk {D E : Type*} [category D] [category E] (F : D ⥤ E) {X Y : D} (f : X ⟶ Y) :
  F.map_arrow.obj (arrow.mk f) = arrow.mk (F.map f) := by refl

end arrow


def composable_morphisms (n : ℕ) (D : Type*) [category D] := fin (n+1) ⥤ D

namespace composable_morphisms

def mk_0 {D : Type*} [category D] (X : D) : composable_morphisms 0 D :=
{ obj := λ i, X,
  map := λ i j f, 𝟙 X }

@[simps]
def mk_1 {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : composable_morphisms 1 D :=
{ obj := λ i, if i = 0 then X₀ else X₁,
  map := λ i j g, begin
    split_ifs with hi hj hj,
    { exact 𝟙 X₀, },
    { exact f, },
    { exfalso,
      apply hi,
      ext,
      simpa only [hj, fin.le_iff_coe_le_coe, fin.coe_zero, nonpos_iff_eq_zero] using le_of_hom g, },
    { exact 𝟙 X₁, },
  end,
  map_id' := λ X, begin
    split_ifs,
    { subst h, refl, },
    { have h' := fin.eq_one_of_neq_zero h, subst h', refl, },
  end,
  map_comp' := λ i j k ij jk, begin
    split_ifs with hi,
    { subst hi,
      by_cases hj : j = 0,
      { subst hj,
        have hij : 𝟙 _ = ij  := hom_of_le_le_of_hom _,
        subst hij,
        erw id_comp,
        refl, },
      { have hj' := fin.eq_one_of_neq_zero hj,
        subst hj',
        have hk' := fin.eq_one_of_geq_one (le_of_hom jk),
        subst hk',
        exact (comp_id _).symm, }, },
    { have hi' := fin.eq_one_of_neq_zero hi,
      subst hi',
      have hj' := fin.eq_one_of_geq_one (le_of_hom ij),
      subst hj',
      have hk' := fin.eq_one_of_geq_one (le_of_hom jk),
      subst hk',
      have hij : 𝟙 _ = ij := hom_of_le_le_of_hom _,
      have hjk : 𝟙 _ = jk := hom_of_le_le_of_hom _,
      substs hij hjk,
      exact (id_comp (𝟙 _)).symm, }
  end, }

@[simp]
def left {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : D := F.obj 0
@[simp]
def right {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : D := F.obj (fin.last _)

@[simp]
lemma mk_1_left {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).left = X₀ := by refl
@[simp]
lemma mk_1_right {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).right = X₁ := by refl

@[simp]
def composition {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) : arrow D :=
arrow.mk (F.map (hom_of_le (fin.last _).zero_le))
@[simp]
lemma mk_1_composition {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).composition = arrow.mk f := by refl

@[simp]
def ith_arrow {n : ℕ} {D : Type*} [category D] (F : composable_morphisms n D) (i : fin n) : arrow D :=
arrow.mk (F.map (hom_of_le (show fin.cast_succ i ≤ i.succ,
by simp only [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.coe_succ, le_add_iff_nonneg_right, zero_le_one])))

namespace join

def obj {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₁+n₂+1)) : D :=
begin
  by_cases hi : (i : ℕ) ≤ n₁,
  { exact F₁.obj ⟨(i : ℕ), nat.lt_succ_iff.mpr hi⟩, },
  { refine F₂.obj ⟨(i : ℕ)-n₁, _⟩,
    cases nat.le.dest (le_of_not_ge hi) with k hk,
    simpa only [← hk, add_tsub_cancel_left, add_assoc, add_lt_add_iff_left n₁] using i.is_lt, },
end

@[simp]
def ι₁ {n₁ n₂ : ℕ} (i : fin (n₁+1)) : fin (n₁+n₂+1) := fin.cast_le (by { rw [add_assoc, add_comm n₂, ← add_assoc], exact le_self_add, }) i
@[simp]
def ι₂ {n₁ n₂ : ℕ} (i : fin (n₂+1)) : fin (n₁+n₂+1) := ⟨n₁+i, by { rw add_assoc, exact add_lt_add_left (i.is_lt) n₁, }⟩

def obj₁ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₁+1)) : obj F₁ F₂ e (ι₁ i) = F₁.obj i :=
begin
  have hi := i.is_le,
  dsimp [obj],
  split_ifs,
  congr,
  ext,
  simp only [ι₁, fin.eta],
end

def ρ₁ {n₁ n₂ : ℕ} (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : fin (n₁+1) := ⟨(i : ℕ), nat.lt_succ_iff.mpr hi⟩
def ρ₂ {n₁ n₂ : ℕ} (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : fin (n₂+1) := ⟨(i : ℕ)-n₁, begin 
  cases nat.le.dest (le_of_not_ge hi) with k hk,
  simpa only [← hk, add_tsub_cancel_left, add_assoc, add_lt_add_iff_left n₁] using i.is_lt,
end⟩

def obj₁' {n₁ n₂ : ℕ} {D : Type*} [category D] {F₁ : composable_morphisms n₁ D} {F₂ : composable_morphisms n₂ D}
  {e : F₁.right = F₂.left} (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : obj F₁ F₂ e i = F₁.obj (ρ₁ i hi) :=
begin
  rw ← obj₁ F₁ F₂ e,
  congr,
  simp only [ι₁, ρ₁, fin.cast_le_mk, fin.eta],
end

def obj₂ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin (n₂+1)) : obj F₁ F₂ e (ι₂ i) = F₂.obj i :=
begin
  dsimp [obj],
  split_ifs with hi,
  { simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hi,
    have hi' : i = 0 := by { ext, exact hi, },
    subst hi',
    exact e, },
  { congr,
    ext,
    simp only [add_tsub_cancel_left, fin.eta], },
end

def obj₂' {n₁ n₂ : ℕ} {D : Type*} [category D] {F₁ : composable_morphisms n₁ D} {F₂ : composable_morphisms n₂ D}
  {e : F₁.right = F₂.left} (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : obj F₁ F₂ e i = F₂.obj (ρ₂ i hi) :=
begin
  rw ← obj₂ F₁ F₂ e,
  congr,
  ext,
  simp only [ι₂, ρ₂, add_tsub_cancel_left, add_lt_add_iff_left, fin.coe_mk, add_comm n₁, nat.sub_add_cancel (le_of_not_ge hi)],
end

def map {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hij : i ≤ j) : obj F₁ F₂ e i ⟶ obj F₁ F₂ e j :=
begin
  by_cases hj : (j : ℕ) ≤ n₁,
  { have hi : (i : ℕ) ≤ n₁ := ((fin.coe_fin_le.mpr hij).trans hj),
    refine eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le _) ≫ eq_to_hom (obj₁' j hj).symm,
    simpa only [subtype.mk_le_mk, fin.coe_fin_le] using hij, },
  by_cases hi : (i : ℕ) ≤ n₁,
  { exact eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (fin.le_last _)) ≫ eq_to_hom e ≫ F₂.map (hom_of_le (fin.zero_le _)) ≫ eq_to_hom (obj₂' j hj).symm, },
  { refine eq_to_hom (obj₂' i hi) ≫ F₂.map (hom_of_le _) ≫ eq_to_hom (obj₂' j hj).symm,
    simp only [ρ₂, subtype.mk_le_mk, tsub_le_iff_right],
    rw nat.sub_add_cancel (le_of_not_ge hj),
    simpa only [fin.coe_fin_le] using hij, },
end

lemma map₁₁' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : (j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (by exact hij)) ≫ eq_to_hom (obj₁' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma hι₁ {n₁ : ℕ} (i : fin (n₁+1)) (n₂ : ℕ) : ((ι₁ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ := i.is_le
lemma hι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : ¬((ι₂ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ :=
begin
  simp only [ι₂, fin.coe_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero],
  intro h,
  apply hi,
  ext,
  exact h,
end

lemma ρ₁ι₁ {n₁ : ℕ} (i : fin (n₁+1)) (n₂ : ℕ) : i = ρ₁ (ι₁ i : fin (n₁+n₂+1)) (hι₁ i n₂) :=
by { ext, refl, }
lemma ρ₂ι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : i = ρ₂ (ι₂ i : fin (n₁+n₂+1)) (hι₂ i hi n₁) :=
begin
  ext,
  simp only [ρ₂, ι₂, fin.coe_mk, add_tsub_cancel_left],
end

lemma map₁₁ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+1)) (hij : (ι₁ i : fin (n₁+n₂+1)) ≤ ι₁ j) : map F₁ F₂ e (ι₁ i) (ι₁ j) hij =
eq_to_hom (obj₁ F₁ F₂ e i) ≫ F₁.map (hom_of_le hij) ≫ eq_to_hom (obj₁ F₁ F₂ e j).symm :=
begin
  have eqi := ρ₁ι₁ i n₁,
  have eqj := ρ₁ι₁ j n₁,
  convert map₁₁' F₁ F₂ e (ι₁ i) (ι₁ j) (hι₁ i n₂) (hι₁ j n₂) hij,
end

lemma map₁₂' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₁' i hi) ≫ F₁.map (hom_of_le (fin.le_last _)) ≫ eq_to_hom e ≫
  F₂.map (hom_of_le (fin.zero_le _)) ≫ eq_to_hom (obj₂' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma map₂₂' {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map F₁ F₂ e i j hij =
eq_to_hom (obj₂' i hi) ≫ F₂.map (hom_of_le begin
  dsimp [ρ₂],
  simpa only [subtype.mk_le_mk, tsub_le_iff_right, nat.sub_add_cancel (le_of_not_ge hj)] using fin.coe_fin_le.mpr hij,
end) ≫ eq_to_hom (obj₂' j hj).symm :=
begin
  dsimp only [map],
  split_ifs,
  tidy,
end

lemma monotone_ι₁ {n₁ n₂ : ℕ} : monotone (ι₁ : fin (n₁+1) → fin (n₁+n₂+1)) := λ x y h, h
lemma monotone_ι₂ {n₁ n₂ : ℕ} : monotone (ι₂ : fin (n₂+1) → fin (n₁+n₂+1)) := λ x y h,
begin
  rw fin.le_iff_coe_le_coe at h ⊢,
  cases nat.le.dest h with k hk,
  apply nat.le.intro,
  swap,
  { exact k, },
  { simp only [ι₂, fin.coe_mk, ← hk, add_assoc], },
end

lemma map₂₂ {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i j : fin (n₂+1)) (hij : i ≤ j) : map F₁ F₂ e (ι₂ i) (ι₂ j) (monotone_ι₂ hij) =
eq_to_hom (obj₂ F₁ F₂ e i) ≫ F₂.map (hom_of_le hij) ≫ eq_to_hom (obj₂ F₁ F₂ e j).symm :=
begin
  have H : ∀ (i : fin (n₂+1)), i ≠ 0 → ¬(((ι₂ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁),
  { intros i hi,
    by_contradiction,
    simp only [ι₂, fin.coe_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h,
    apply hi,
    ext,
    exact h, },
  by_cases hi : i ≠ 0,
  { have hj : j ≠ 0,
    { by_contradiction,
      apply hi,
      rw h at hij,
      exact le_antisymm hij (fin.zero_le i), },
    have eqi := ρ₂ι₂ i hi n₁,
    have eqj := ρ₂ι₂ j hj n₁,
    convert map₂₂' F₁ F₂ e (ι₂ i) (ι₂ j) (H i hi) (H j hj) (monotone_ι₂ hij), },
  { by_cases hj : j ≠ 0,
    { simp only [not_not] at hi,
      subst hi,
      erw join.map₁₂' F₁ F₂ e (ι₂ 0) (ι₂ j) rfl.le (H j hj) (monotone_ι₂ hij),
      erw [F₁.map_id, id_comp],
      slice_lhs 1 2 { erw [eq_to_hom_trans], },
      rw assoc,
      have eqj := (ρ₂ι₂ j hj n₁).symm,
      congr', },
    { simp only [not_not] at hi hj,
      substs hi hj,
      erw join.map₁₁' F₁ F₂ e (ι₂ 0) (ι₂ 0) rfl.le rfl.le  (monotone_ι₂ hij),
      erw [F₁.map_id, F₂.map_id],
      simp only [id_comp, eq_to_hom_trans], }, },
end

end join

@[simps]
def join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) :
  composable_morphisms (n₁+n₂) D :=
{ obj := join.obj F₁ F₂ e,
  map := λ i j ij, join.map F₁ F₂ e i j (le_of_hom ij),
  map_id' := λ i, begin
    by_cases hi : (i : ℕ) ≤ n₁,
    { erw [join.map₁₁' F₁ F₂ e i i hi hi rfl.le, F₁.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { erw [join.map₂₂' F₁ F₂ e i i hi hi rfl.le, F₂.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
  end,
  map_comp' := λ i j k ij jk, begin
    by_cases hk : (k : ℕ) ≤ n₁,
    { have hj : (j : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp (le_of_hom jk)) hk,
      have hi : (i : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp (le_of_hom ij)) hj,
      erw join.map₁₁' F₁ F₂ e i j hi hj (le_of_hom ij),
      erw join.map₁₁' F₁ F₂ e j k hj hk (le_of_hom jk),
      erw join.map₁₁' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
      slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
      erw id_comp,
      slice_rhs 2 3 { rw ← F₁.map_comp, },
      refl, },
    { by_cases hi : (i : ℕ) ≤ n₁,
      { by_cases hj : (j : ℕ) ≤ n₁,
        { erw join.map₁₁' F₁ F₂ e i j hi hj (le_of_hom ij),
          erw join.map₁₂' F₁ F₂ e j k hj hk (le_of_hom jk),
          erw join.map₁₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
          slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 2 3 { rw ← F₁.map_comp, },
          simpa only [assoc], },
        { erw join.map₁₂' F₁ F₂ e i j hi hj (le_of_hom ij),
          erw join.map₂₂' F₁ F₂ e j k hj hk (le_of_hom jk),
          erw join.map₁₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
          slice_rhs 5 6 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 4 5 { rw ← F₂.map_comp, },
          refl, }, },
      { have hj : ¬(j : ℕ) ≤ n₁,
        { simp only [not_le] at ⊢ hi,
          exact lt_of_lt_of_le hi (le_of_hom ij), },
        erw join.map₂₂' F₁ F₂ e i j hi hj (le_of_hom ij),
        erw join.map₂₂' F₁ F₂ e j k hj hk (le_of_hom jk),
        erw join.map₂₂' F₁ F₂ e i k hi hk (le_of_hom (ij ≫ jk)),
        slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
        erw id_comp,
        slice_rhs 2 3 { rw ← F₂.map_comp, },
        refl, }, },
  end }

def left_part {n₁ n₂ : ℕ} {D : Type*} [category D] (F : composable_morphisms (n₁+n₂) D) : composable_morphisms n₁ D :=
monotone.functor (join.monotone_ι₁) ⋙ F

def right_part {n₁ n₂ : ℕ} {D : Type*} [category D] (F : composable_morphisms (n₁+n₂) D) : composable_morphisms n₂ D :=
monotone.functor (join.monotone_ι₂) ⋙ F

lemma left_part_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) : (join F₁ F₂ e).left_part = F₁ :=
begin
  apply functor.ext,
  { intros i j ij,
    convert join.map₁₁ F₁ F₂ e i j (le_of_hom ij), },
end

lemma right_part_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) : (join F₁ F₂ e).right_part = F₂ :=
begin
  apply functor.ext,
  { intros i j ij,
    convert join.map₂₂ F₁ F₂ e i j (le_of_hom ij), },
end

lemma composition_is_comp_of_left_and_right_parts {n₁ n₂ : ℕ} {D : Type*} [category D] (F : composable_morphisms (n₁+n₂) D) :
  F.composition = arrow.composition F.left_part.composition F.right_part.composition rfl :=
begin
  let a : fin (n₁+n₂+1) := 0,
  let b : fin (n₁+n₂+1) := ⟨n₁, nat.lt_succ_iff.mpr le_self_add⟩,
  let c : fin (n₁+n₂+1) := fin.last _,
  have ab : a ≤ b := nat.zero_le _,
  have bc : b ≤ c := fin.le_last _,
  ext,
  { simp only [eq_to_hom_refl, arrow.composition_hom, id_comp, comp_id],
    exact F.map_comp (hom_of_le ab) (hom_of_le bc), },
  { refl, },
  { refl, },
end

lemma composition_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) : (join F₁ F₂ e).composition = arrow.composition F₁.composition F₂.composition e :=
begin
  convert composition_is_comp_of_left_and_right_parts _,
  { symmetry, apply left_part_of_join, },
  { symmetry, apply right_part_of_join, },
end

lemma i₁th_arrow {n₁ n₂ : ℕ} {D : Type*} [category D] (F : composable_morphisms (n₁+n₂) D) (i : fin n₁):
  F.ith_arrow (fin.cast_le le_self_add i) = F.left_part.ith_arrow i :=
begin
  dsimp only [left_part, ith_arrow, functor.comp, monotone.functor],
  simp only [← arrow.map_arrow_of_mk],
  congr';
  { ext,
    simp only [join.ι₁, fin.cast_le_succ], },
end

lemma i₁th_arrow_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin n₁) : (join F₁ F₂ e).ith_arrow (fin.cast_le le_self_add i) = F₁.ith_arrow i :=
begin
  convert i₁th_arrow (join F₁ F₂ e) i,
  { symmetry, apply left_part_of_join, },
end

lemma i₂th_arrow {n₁ n₂ : ℕ} {D : Type*} [category D] (F : composable_morphisms (n₁+n₂) D) (i : fin n₂):
  F.ith_arrow ⟨n₁+(i : ℕ), by { simpa only [add_lt_add_iff_left] using i.is_lt, }⟩ = F.right_part.ith_arrow i :=
begin
  dsimp only [right_part, ith_arrow, functor.comp, monotone.functor],
  simp only [← arrow.map_arrow_of_mk],
  congr';
  { ext,
    simp only [join.ι₂, fin.coe_mk, fin.coe_succ, add_assoc], },
end

lemma i₂th_arrow_of_join {n₁ n₂ : ℕ} {D : Type*} [category D] (F₁ : composable_morphisms n₁ D) (F₂ : composable_morphisms n₂ D)
  (e : F₁.right = F₂.left) (i : fin n₂) :
  (join F₁ F₂ e).ith_arrow ⟨n₁+(i : ℕ), by { simpa only [add_lt_add_iff_left] using i.is_lt, }⟩ = F₂.ith_arrow i :=
begin
  convert i₂th_arrow (join F₁ F₂ e) i,
  { symmetry, apply right_part_of_join, },
end

def last_arrow_of_join {n₁ : ℕ} {D : Type*} [category D] (F : composable_morphisms n₁ D) {Y Z : D} (f : Y ⟶ Z) (e : F.right = Y) :
  (F.join (mk_1 f) e).ith_arrow (fin.last _) = arrow.mk f :=
begin
  convert i₂th_arrow_of_join F (mk_1 f) e 0,
end

end composable_morphisms

def NonemptyFinLinOrd_to_Preorder : NonemptyFinLinOrd ⥤ Preorder :=
{ obj := λ X, ⟨X.α⟩,
  map := λ X Y f, f,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl, }

def to_Cat : simplex_category ⥤ Cat := simplex_category.skeletal_functor ⋙ NonemptyFinLinOrd_to_Preorder ⋙ Preorder_to_Cat

@[simps]
def nerve (C : Type u) [category.{v} C] : sSet := 
{ obj := λ Δ, (to_Cat.obj Δ.unop) ⥤ C,
  map := λ Δ₁ Δ₂ f, ((whiskering_left _ _ _).obj (to_Cat.map f.unop)).obj,
  map_id' := λ Δ, begin
    erw to_Cat.map_id,
    ext A,
    apply category_theory.functor.ext,
    { intros X Y f,
      erw [id_comp, comp_id],
      refl, },
    { intro X,
      refl, },
  end,
  map_comp' := λ Δ₁ Δ₂ Δ₃ f g, rfl }

instance (C : Type*) [category C] (Δ : simplex_categoryᵒᵖ) : category ((nerve C).obj Δ) := (infer_instance : category ((to_Cat.obj Δ.unop) ⥤ C))
  
namespace nerve

@[simps]
def functor : Cat ⥤ sSet :=
{ obj := λ C, nerve C,
  map := λ C C' F,
  { app := λ Δ, ((whiskering_right _ _ _).obj F).obj,
    naturality' := λ Δ₁ Δ₂ f, by { ext G, refl, }, },
  map_id' := λ C, begin
    ext Δ F,
    apply category_theory.functor.ext,
    { intros X Y f,
      erw [id_comp, comp_id],
      refl, },
    { intro X,
      refl, },
  end,
  map_comp' := λ C C' C'' F F', rfl, }

end nerve

@[derive category]
def composable_morphisms_new (n : ℕ) (C : Type u) [category.{v} C] := (nerve C).obj (op [n])

namespace composable_morphisms_new

variables {C : Type u} [category.{v} C] {n : ℕ} (M : composable_morphisms_new n C)

def ith_object (i : fin (n+1)) : C := M.obj (ulift.up i)

def left : C := M.ith_object 0
def right : C := M.ith_object (fin.last _)

@[simp]
def map_of_le {i j : fin (n+1)} (hij : i ≤ j) : M.ith_object i ⟶ M.ith_object j :=
M.map (hom_of_le hij)
def ith_map (i : fin n) : M.ith_object (i.cast_succ) ⟶ M.ith_object i.succ := M.map_of_le
begin 
  rw fin.le_iff_coe_le_coe,
  simp only [fin.coe_cast_succ, fin.coe_succ, le_add_iff_nonneg_right, zero_le'],
end
def comp : M.left ⟶ M.right := M.map_of_le (fin.le_last _)

@[simp]
def map_of_le_trans {i j k: fin (n+1)} (hij : i ≤ j) (hjk : j ≤ k) :
  M.map_of_le (hij.trans hjk) = M.map_of_le hij ≫ M.map_of_le hjk :=
by { simp only [map_of_le], erw M.map_comp, }  

def arrow_of_le {i j : fin (n+1)} (hij : i ≤ j) : arrow C := arrow.mk (M.map_of_le hij)
def ith_arrow (i : fin n) : arrow C := arrow.mk (M.ith_map i)
def arrow : arrow C := arrow.mk M.comp

def pullback {m n : ℕ} (f : fin (m+1) →o fin (n+1)) (M : composable_morphisms_new n C) : composable_morphisms_new m C :=
{ obj := λ i, M.ith_object (f (ulift.down i)),
  map := λ i j ij, M.map_of_le (f.monotone (show i.down ≤ j.down, by convert le_of_hom ij)),
  map_id' := λ i, by simpa only [map_of_le] using M.map_id _,
  map_comp' := λ i j k ij jk, by { simp only [map_of_le], erw M.map_comp, }, }

@[simps]
def mk_1 {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : composable_morphisms_new 1 D :=
{ obj := λ i, if ulift.down i = 0 then X₀ else X₁,
  map := begin
    rintros ⟨i⟩ ⟨j⟩ ij',
    split_ifs with hi hj hj,
    { exact 𝟙 X₀, },
    { exact f, },
    { exfalso,
      apply hi,
      ext,
      have ij : i ≤ j := by convert le_of_hom ij',
      simpa only [hj, fin.le_iff_coe_le_coe, fin.coe_zero, nonpos_iff_eq_zero] using ij, },
    { exact 𝟙 X₁, },
  end,
  map_id' := begin
    rintro ⟨i⟩,
    split_ifs; dsimp at h,
    { subst h,
      refl, },
    { have h' := fin.eq_one_of_neq_zero h,
      subst h',
      refl, },
  end,
  map_comp' := begin
    rintros ⟨i⟩ ⟨j⟩ ⟨k⟩ ij jk,
    split_ifs with hi; dsimp at hi,
    { subst hi,
      by_cases hj : j = 0,
      { subst hj,
        have hij : 𝟙 _ = ij := hom_of_le_le_of_hom _,
        subst hij,
        erw id_comp,
        refl, },
      { have hj' := fin.eq_one_of_neq_zero hj,
        subst hj',
        have hk' : k = 1 := fin.eq_one_of_geq_one (by convert le_of_hom jk),
        subst hk',
        exact (comp_id _).symm, }, },
    { have hi' := fin.eq_one_of_neq_zero hi,
      subst hi',
      have hj' : j = 1 := fin.eq_one_of_geq_one (by convert le_of_hom ij),
      subst hj',
      have hk' : k = 1 := fin.eq_one_of_geq_one (by convert le_of_hom jk),
      subst hk',
      have hij : 𝟙 _ = ij := hom_of_le_le_of_hom _,
      have hjk : 𝟙 _ = jk := hom_of_le_le_of_hom _,
      substs hij hjk,
      exact (id_comp (𝟙 _)).symm, }
  end, }

@[simp]
lemma mk_1_left {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).left = X₀ := by refl
@[simp]
lemma mk_1_right {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).right = X₁ := by refl
@[simp]
lemma mk_1_comp {D : Type*} [category D] {X₀ X₁ : D} (f : X₀ ⟶ X₁) : (mk_1 f).comp = f := by refl



variables {n₁ n₂ : ℕ} (M₁₂ : composable_morphisms_new (n₁+n₂) C)

namespace join

@[simp]
def ι₁ : fin (n₁+1) →o fin (n₁+n₂+1) := fin.cast_le (show n₁+1 ≤ n₁+n₂+1, by linarith)
@[simp]
def ι₂ : fin (n₂+1) →o fin (n₁+n₂+1) :=
order_hom.comp (fin.cast_le (show n₁+(n₂+1) ≤ n₁+n₂+1, by rw add_assoc)).to_order_hom
(@fin.nat_add n₁ (n₂+1)).to_order_hom

@[simp]
def ρ₁ (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : fin (n₁+1) := ⟨(i : ℕ), nat.lt_succ_iff.mpr hi⟩
@[simp]
def ρ₂ (i : fin (n₁+n₂+1)) (hi : n₁ ≤ (i : ℕ)) : fin (n₂+1) := ⟨(i : ℕ)-n₁, begin
  cases nat.le.dest hi with k hk,
  rw [← hk, add_tsub_cancel_left, ← add_lt_add_iff_left n₁, ← add_assoc, hk],
  exact i.is_lt,
end⟩
@[simp]
def ρ₂' (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : fin (n₂+1) := ρ₂ i (le_of_lt (not_le.mp hi))

/-lemma hι₁ (i : fin (n₁+1)) (n₂ : ℕ) : ((ι₁ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ := i.is_le
lemma hι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : ¬((ι₂ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ :=
begin
  simp only [ι₂, fin.coe_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero],
  intro h,
  apply hi,
  ext,
  exact h,
end

lemma ρ₁ι₁ {n₁ : ℕ} (i : fin (n₁+1)) (n₂ : ℕ) : i = ρ₁ (ι₁ i : fin (n₁+n₂+1)) (hι₁ i n₂) :=
by { ext, refl, }
lemma ρ₂ι₂ {n₂ : ℕ} (i : fin (n₂+1)) (hi : i ≠ 0) (n₁ : ℕ) : i = ρ₂ (ι₂ i : fin (n₁+n₂+1)) (hι₂ i hi n₁) :=
begin
  ext,
  simp only [ρ₂, ι₂, fin.coe_mk, add_tsub_cancel_left],
end-/


lemma hι₁ (i : fin (n₁+1)) : ((ι₁ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁ := i.is_le
lemma hι₂ (i : fin (n₂+1)) : n₁ ≤ (ι₂ i : fin (n₁+n₂+1)) :=
begin
  simp only [ι₂, order_hom.comp_coe, order_embedding.to_order_hom_coe, fin.coe_cast_le, fin.coe_nat_add,
  le_add_iff_nonneg_right, zero_le'],
end

lemma ρ₁ι₁ (i : fin (n₁+1)) : i = ρ₁ (ι₁ i : fin (n₁+n₂+1)) (hι₁ i) :=
by { ext, refl, }
lemma ρ₂ι₂ (i : fin (n₂+1)) : i = ρ₂ (ι₂ i : fin (n₁+n₂+1)) (hι₂ i) :=
by { simp only [ρ₂, ι₂, order_hom.comp_coe, order_embedding.to_order_hom_coe, fin.coe_cast_le, fin.coe_nat_add,
  add_tsub_cancel_left, fin.eta], }

variables (M₁ : composable_morphisms_new n₁ C) (M₂ : composable_morphisms_new n₂ C) (e : M₁.right = M₂.left)

include M₁ M₂ e

def obj (i : fin (n₁+n₂+1)) : C :=
begin
  by_cases hi : (i : ℕ) ≤ n₁,
  { exact M₁.ith_object (ρ₁ i hi), },
  { exact M₂.ith_object (ρ₂' i hi), },
end

lemma obj₁' (i : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) : obj M₁ M₂ e i = M₁.ith_object (ρ₁ i hi) :=
by { dsimp only [obj], split_ifs, refl, }

lemma obj₂' (i : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) : obj M₁ M₂ e i = M₂.ith_object (ρ₂' i hi) :=
by { dsimp only [obj], split_ifs, refl, }

lemma obj₁ (i : fin (n₁+1)) : obj M₁ M₂ e (ι₁ i) = M₁.ith_object i :=
begin
  convert obj₁' M₁ M₂ e (ι₁ i) (hι₁ i),
  apply ρ₁ι₁,
end

lemma obj₂ (i : fin (n₂+1)) : obj M₁ M₂ e (ι₂ i) = M₂.ith_object i :=
begin
  by_cases ¬((ι₂ i : fin (n₁+n₂+1)) : ℕ) ≤ n₁,
  { convert obj₂' M₁ M₂ e (ι₂ i) h,
    apply ρ₂ι₂, },
  { simp only [not_not] at h,
    have eq : i = 0,
    { simp only [ι₂, order_hom.comp_coe, order_embedding.to_order_hom_coe, fin.coe_cast_le, fin.coe_nat_add,
        add_le_iff_nonpos_right, le_zero_iff, not_not] at h,
      exact le_antisymm (by simpa only [fin.le_iff_coe_le_coe, h]) (fin.zero_le _), },
    subst eq,
    convert obj₁' M₁ M₂ e (ι₂ 0) h,
    exact e.symm, },
end

def map (i j : fin (n₁+n₂+1)) (hij : i ≤ j) : obj M₁ M₂ e i ⟶ obj M₁ M₂ e j :=
begin
  by_cases hj : (j : ℕ) ≤ n₁,
  { have hi : (i : ℕ) ≤ n₁ := ((fin.coe_fin_le.mpr hij).trans hj),
    exact eq_to_hom (obj₁' M₁ M₂ e i hi) ≫ M₁.map_of_le (by exact hij) ≫ eq_to_hom (obj₁' M₁ M₂ e j hj).symm, },
  by_cases hi : (i : ℕ) ≤ n₁,
  { refine eq_to_hom (obj₁' M₁ M₂ e i hi) ≫ M₁.map_of_le (fin.le_last _) ≫ eq_to_hom e ≫
      M₂.map_of_le (fin.zero_le _) ≫ eq_to_hom (obj₂' M₁ M₂ e j hj).symm, },
  { refine eq_to_hom (obj₂' M₁ M₂ e i hi) ≫ M₂.map_of_le _ ≫ eq_to_hom (obj₂' M₁ M₂ e j hj).symm,
    simp only [ρ₂', ρ₂, subtype.mk_le_mk, tsub_le_iff_right],
    rw nat.sub_add_cancel (le_of_not_ge hj),
    simpa only [fin.coe_fin_le] using hij, },
end

lemma map₁₁' (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : (j : ℕ) ≤ n₁) (hij : i ≤ j) : map M₁ M₂ e i j hij =
eq_to_hom (obj₁' M₁ M₂ e i hi) ≫ M₁.map_of_le (by exact hij) ≫ eq_to_hom (obj₁' M₁ M₂ e j hj).symm :=
by { dsimp only [map], split_ifs, refl, }
lemma map₁₂' (i j : fin (n₁+n₂+1)) (hi : (i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map M₁ M₂ e i j hij =
eq_to_hom (obj₁' M₁ M₂ e i hi) ≫ M₁.map_of_le (fin.le_last _) ≫ eq_to_hom e ≫
      M₂.map_of_le (fin.zero_le _) ≫ eq_to_hom (obj₂' M₁ M₂ e j hj).symm :=
by { dsimp only [map], split_ifs, refl, }
lemma map₂₂' (i j : fin (n₁+n₂+1)) (hi : ¬(i : ℕ) ≤ n₁) (hj : ¬(j : ℕ) ≤ n₁) (hij : i ≤ j) : map M₁ M₂ e i j hij =
eq_to_hom (obj₂' M₁ M₂ e i hi) ≫ M₂.map_of_le begin
  simp only [ρ₂', ρ₂, subtype.mk_le_mk, tsub_le_iff_right],
    rw nat.sub_add_cancel (le_of_not_ge hj),
    simpa only [fin.coe_fin_le] using hij,
end ≫ eq_to_hom (obj₂' M₁ M₂ e j hj).symm :=
by { dsimp only [map], split_ifs, refl, }

lemma map₁₁ (i : fin (n₁+1)) (j : fin (n₁+1)) (hij : (ι₁ i : fin (n₁+n₂+1)) ≤ ι₁ j) : map M₁ M₂ e (ι₁ i) (ι₁ j) hij =
eq_to_hom (obj₁ M₁ M₂ e i) ≫ M₁.map_of_le hij ≫ eq_to_hom (obj₁ M₁ M₂ e j).symm :=
begin
  have eqi := @ρ₁ι₁ n₁ n₂ i,
  have eqj := @ρ₁ι₁ n₁ n₂ j,
  convert map₁₁' M₁ M₂ e (ι₁ i) (ι₁ j) (hι₁ i) (hι₁ j) hij,
end

end join

def left_part := M₁₂.pullback join.ι₁
def right_part := M₁₂.pullback join.ι₂

variables (M₁ : composable_morphisms_new n₁ C) (M₂ : composable_morphisms_new n₂ C) (e : M₁.right = M₂.left)

@[simps]
def join : composable_morphisms_new (n₁+n₂) C :=
{ obj := λ i, join.obj M₁ M₂ e (ulift.down i),
  map := λ i j ij, join.map M₁ M₂ e (ulift.down i) (ulift.down j) (by convert le_of_hom ij),
  map_id' := begin
    rintro ⟨i⟩,
    by_cases hi : (i : ℕ) ≤ n₁,
    { erw [join.map₁₁' M₁ M₂ e i i hi hi rfl.le, map_of_le, M₁.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
    { erw [join.map₂₂' M₁ M₂ e i i hi hi rfl.le, map_of_le, M₂.map_id, id_comp, eq_to_hom_trans, eq_to_hom_refl], },
  end,
  map_comp' := begin
    rintros ⟨i⟩ ⟨j⟩ ⟨k⟩ ij' jk',
    have ij : i ≤ j := by convert le_of_hom ij',
    have jk : j ≤ k := by convert le_of_hom jk',
    by_cases hk : (k : ℕ) ≤ n₁,
    { have hj : (j : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp jk) hk,
      have hi : (i : ℕ) ≤ n₁ := le_trans (fin.le_iff_coe_le_coe.mp ij) hj,
      erw join.map₁₁' M₁ M₂ e i j hi hj ij,
      erw join.map₁₁' M₁ M₂ e j k hj hk jk,
      erw join.map₁₁' M₁ M₂ e i k hi hk (ij.trans jk),
      simp only [map_of_le],
      slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
      erw [id_comp],
      slice_rhs 2 3 { rw ← M₁.map_comp, },
      refl, },
    { by_cases hi : (i : ℕ) ≤ n₁,
      { by_cases hj : (j : ℕ) ≤ n₁,
        { erw join.map₁₁' M₁ M₂ e i j hi hj ij,
          erw join.map₁₂' M₁ M₂ e j k hj hk jk,
          erw join.map₁₂' M₁ M₂ e i k hi hk (ij.trans jk),
          simp only [map_of_le],
          slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 2 3 { rw ← M₁.map_comp, },
          simpa only [assoc], },
        { erw join.map₁₂' M₁ M₂ e i j hi hj ij,
          erw join.map₂₂' M₁ M₂ e j k hj hk jk,
          erw join.map₁₂' M₁ M₂ e i k hi hk (ij.trans jk),
          simp only [map_of_le],
          slice_rhs 5 6 { rw [eq_to_hom_trans, eq_to_hom_refl], },
          erw id_comp,
          slice_rhs 4 5 { rw ← M₂.map_comp, },
          refl, }, },
      have hj : ¬(j : ℕ) ≤ n₁,
        { simp only [not_le] at ⊢ hi,
          exact lt_of_lt_of_le hi ij, },
      erw join.map₂₂' M₁ M₂ e i j hi hj ij,
      erw join.map₂₂' M₁ M₂ e j k hj hk jk,
      erw join.map₂₂' M₁ M₂ e i k hi hk (ij.trans jk),
      slice_rhs 3 4 { rw [eq_to_hom_trans, eq_to_hom_refl], },
      erw id_comp,
      slice_rhs 2 3 { erw ← M₂.map_comp, },
      refl, },
  end, }

lemma test (a b : ℕ) (h : a<b) : a+1 ≤ b := nat.succ_le_iff.mpr h

@[ext]
lemma ext {n : ℕ} (M M' : composable_morphisms_new n C) (h₁ : M.ith_object = M'.ith_object)
  (h₂ : ∀ (i : fin n), M.ith_map i = eq_to_hom (by rw h₁) ≫  M'.ith_map i ≫ eq_to_hom (by rw h₁)) : M = M' :=
begin
  apply functor.ext,
  { suffices H : ∀ (j : ℕ) (hj : j < n+1) (i : fin (n+1)) (hij : i ≤ fin.mk j hj), M.map_of_le hij = eq_to_hom (by rw h₁)
    ≫ M'.map_of_le hij ≫ eq_to_hom (by rw h₁),
    { rintros ⟨a⟩ ⟨b⟩ ab,
      have ab' : a ≤ b := by convert le_of_hom ab,
      have eqb : b = ⟨b, b.is_lt⟩ := by simp only [fin.eta],
      have eqab : ab = hom_of_le ab' := by ext,
      convert H b b.is_lt a ab', },
    intro j,
    induction j with j hj,
    { intros hj i hij,
      have hi : i = 0 := le_antisymm hij (fin.zero_le _),
      subst hi,
      simp only [map_of_le],
      erw [M.map_id, M'.map_id, id_comp, eq_to_hom_trans],
      refl, },
    { intros hj' i hij,
      have hj'' : j < n+1 := lt_trans (lt_add_one j) hj',
      by_cases i ≤ fin.mk j hj'',
      { have hj''' : fin.mk j hj'' ≤ fin.mk j.succ hj' := nat.le_succ j,
        have eq : hij = h.trans hj''' := rfl,
        erw [eq, M.map_of_le_trans, M'.map_of_le_trans, hj hj'' i h],
        have eq' := h₂ (fin.mk j (by simpa only [nat.succ_eq_add_one, add_lt_add_iff_right] using hj')),
        simp only [ith_map] at eq',
        erw eq',
        slice_lhs 3 4 { erw [eq_to_hom_trans, eq_to_hom_refl], },
        erw [id_comp, assoc],
        refl, },
      { have hi' : i = ⟨j.succ, hj'⟩,
        { apply le_antisymm hij,
          simpa only [fin.le_iff_coe_le_coe, fin.mk_eq_subtype_mk, not_le, fin.lt_iff_coe_lt_coe, ← nat.succ_le_iff] using h, },
        subst hi',
        simp only [map_of_le],
        erw [M.map_id, M'.map_id, id_comp, eq_to_hom_trans],
        refl, }, }, },
  { rintro ⟨i⟩,
    convert congr_fun h₁ i, },
end


lemma left_part_of_join : (join M₁ M₂ e).left_part = M₁ := sorry

end composable_morphisms_new

end category_theory
