--import algebra.category.Module.abelian
--import algebra.category.Module.subobject
import algebra.homology.short_complex.homology
import algebra.homology.short_complex.preadditive
import algebra.homology.short_complex.abelian
import linear_algebra.quotient
import algebra.category.Group.abelian

noncomputable theory

open category_theory category_theory.category AddCommGroup category_theory.limits

universes u

instance : category_with_homology (AddCommGroup.{u}) := infer_instance

lemma AddCommGroup.is_zero_iff (M : AddCommGroup.{u}) : is_zero M ↔ ∀ (x : M), x = 0 :=
begin
  rw is_zero.iff_id_eq_zero,
  split,
  { intros h x,
    change (𝟙 M : M → M) x = 0,
    simp only [h, AddCommGroup.zero_apply], },
  { intro h,
    ext x,
    exact h x, },
end

namespace category_theory

namespace short_complex

variables (S : short_complex (AddCommGroup.{u}))

lemma AddCommGroup_image_le_kernel : add_monoid_hom.range S.f ≤ add_monoid_hom.ker S.g :=
begin
  rintros x₂ ⟨x₁, h⟩,
  simp only [add_monoid_hom.mem_ker, ← h, ← comp_apply, S.zero, add_monoid_hom.zero_apply],
end

def AddCommGroup_f' : S.X₁ ⟶ of (add_monoid_hom.ker S.g) :=
add_monoid_hom.cod_restrict S.f _ (λ x, S.AddCommGroup_image_le_kernel (by simp))

def AddCommGroup_homology := of ((add_monoid_hom.ker S.g) ⧸ add_monoid_hom.range S.AddCommGroup_f')

def AddCommGroup_homology_π' : of (add_monoid_hom.ker S.g) ⟶ S.AddCommGroup_homology :=
quotient_add_group.mk' (add_monoid_hom.range S.AddCommGroup_f')

@[simp, reassoc, elementwise]
lemma AddCommGroup_f'_comp_homology_π' : S.AddCommGroup_f' ≫ S.AddCommGroup_homology_π' = 0 :=
begin
  ext,
  dsimp [AddCommGroup_f', AddCommGroup_homology_π'],
  simp only [comp_apply, quotient_add_group.mk'_apply, quotient_add_group.eq_zero_iff,
    add_monoid_hom.mem_range, exists_apply_eq_apply],
end

namespace AddCommGroup_left_homology_data

def i : AddCommGroup.of (add_monoid_hom.ker S.g) ⟶ S.X₂ :=
(add_monoid_hom.ker S.g).subtype

lemma wi : i S ≫ S.g = 0 := by { ext x₂, exact x₂.2, }

@[simps]
def _root_.AddCommGroup.kernel_cone {X Y : AddCommGroup.{u}} (f : X ⟶ Y) :
  kernel_fork f := @kernel_fork.of_ι _ _ _ _ _ f (AddCommGroup.of _) (add_monoid_hom.ker f).subtype
    (by tidy)

def _root_.AddCommGroup.kernel_is_limit {X Y : AddCommGroup.{u}} (f : X ⟶ Y) :
  is_limit (AddCommGroup.kernel_cone f) :=
limits.kernel_fork.is_limit.of_ι _ _
  (λ A x hx,
    { to_fun := λ a, ⟨x a, by rw [add_monoid_hom.mem_ker, ← comp_apply, hx, zero_apply]⟩,
      map_zero' := by tidy,
      map_add' := by tidy, })
  (λ A x hx, begin
    ext,
    refl,
  end)
  (λ A x hx b hb, begin
    ext x,
    convert congr_arg (λ (φ : A →+ X), φ x) hb,
  end)

def hi : is_limit (kernel_fork.of_ι (i S) (wi S)) := AddCommGroup.kernel_is_limit S.g

lemma f'_eq_AddCommGroup_f' : (hi S).lift (kernel_fork.of_ι S.f S.zero) = S.AddCommGroup_f' := rfl

lemma wπ : (hi S).lift (kernel_fork.of_ι S.f S.zero) ≫ S.AddCommGroup_homology_π' = 0 :=
by simp only [f'_eq_AddCommGroup_f', AddCommGroup_f'_comp_homology_π']

@[simps]
def _root_.AddCommGroup.cokernel_cocone {X Y : AddCommGroup.{u}} (f : X ⟶ Y) :
  cokernel_cofork f :=
@cokernel_cofork.of_π _ _ _ _ _ f (AddCommGroup.of (Y ⧸ add_monoid_hom.range f))
    (quotient_add_group.mk' (add_monoid_hom.range f)) (by tidy)

def _root_.AddCommGroup.cokernel_is_colimit {X Y : AddCommGroup.{u}} (f : X ⟶ Y) :
  is_colimit (AddCommGroup.cokernel_cocone f) :=
limits.cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, quotient_add_group.lift _ x (λ y hy, begin
    obtain ⟨z, rfl⟩ := hy,
    rw [← comp_apply, hx, zero_apply],
  end))
  (λ A x hx, by { ext, refl, })
  (λ A x hx b hb, begin
    ext y,
    obtain ⟨z, rfl⟩ := quotient_add_group.mk'_surjective _ y,
    simpa only [← comp_apply, hb],
  end)

def hπ : is_colimit (cokernel_cofork.of_π _ (wπ S)) :=
is_colimit.of_iso_colimit (AddCommGroup.cokernel_is_colimit S.AddCommGroup_f')
  (cofork.ext (iso.refl _) (by tidy))

end AddCommGroup_left_homology_data

@[simps]
def AddCommGroup_left_homology_data : S.left_homology_data :=
{ K := AddCommGroup.of (add_monoid_hom.ker S.g),
  H := AddCommGroup.of S.AddCommGroup_homology,
  i := AddCommGroup_left_homology_data.i S,
  π := S.AddCommGroup_homology_π',
  wi := AddCommGroup_left_homology_data.wi S,
  hi := AddCommGroup_left_homology_data.hi S,
  wπ := AddCommGroup_left_homology_data.wπ S,
  hπ := AddCommGroup_left_homology_data.hπ S, }

@[simp]
lemma AddCommGroup_left_homology_data_f' :
  S.AddCommGroup_left_homology_data.f' = S.AddCommGroup_f' := rfl

def AddCommGroup_homology_iso : S.homology ≅ S.AddCommGroup_homology :=
S.AddCommGroup_left_homology_data.homology_iso

lemma AddCommGroup_bijective_homology_iso_inv :
  function.bijective S.AddCommGroup_homology_iso.inv :=
concrete_category.bijective_of_is_iso ((forget AddCommGroup).map S.AddCommGroup_homology_iso.inv)

lemma AddCommGroup_bijective_homology_iso_hom :
  function.bijective S.AddCommGroup_homology_iso.hom :=
concrete_category.bijective_of_is_iso ((forget AddCommGroup).map S.AddCommGroup_homology_iso.hom)

def AddCommGroup_homology_π : of (add_monoid_hom.ker S.g) ⟶ S.homology :=
S.AddCommGroup_homology_π' ≫ S.AddCommGroup_homology_iso.inv

@[simp, reassoc, elementwise]
lemma AddCommGroup_homology_π'_comp_homology_iso_inv :
  S.AddCommGroup_homology_π' ≫ S.AddCommGroup_homology_iso.inv = S.AddCommGroup_homology_π := rfl

@[simp, reassoc, elementwise]
lemma AddCommGroup_f'_comp_homology_π : S.AddCommGroup_f' ≫ S.AddCommGroup_homology_π = 0 :=
begin
  ext,
  dsimp only [AddCommGroup_homology_π],
  rw [AddCommGroup_f'_comp_homology_π'_assoc, zero_comp],
end

lemma AddCommGroup_surjective_homology_π' : function.surjective S.AddCommGroup_homology_π' :=
quotient_add_group.mk'_surjective _

lemma AddCommGroup_surjective_homology_π : function.surjective S.AddCommGroup_homology_π  :=
function.surjective.comp S.AddCommGroup_bijective_homology_iso_inv.2
  S.AddCommGroup_surjective_homology_π'

lemma AddCommGroup_ker_homology_π'_eq_range_f' :
  add_monoid_hom.ker S.AddCommGroup_homology_π' = add_monoid_hom.range S.AddCommGroup_f' :=
quotient_add_group.ker_mk _

lemma AddCommGroup_homology_π'_eq_zero_iff (z : add_monoid_hom.ker S.g) :
  S.AddCommGroup_homology_π' z = 0 ↔ z.1 ∈ (add_monoid_hom.range S.f) :=
begin
  change z ∈ add_monoid_hom.ker S.AddCommGroup_homology_π' ↔ _,
  rw AddCommGroup_ker_homology_π'_eq_range_f',
  split,
  { rintro ⟨x₁, hx₁⟩,
    rw ← hx₁,
    exact ⟨x₁, rfl⟩, },
  { rintro ⟨x₁, hx₁⟩,
    exact ⟨x₁, by { ext, exact hx₁, }⟩, },
end

lemma AddCommGroup_ker_homology_π_eq_ker_homology_π' :
  add_monoid_hom.ker S.AddCommGroup_homology_π = add_monoid_hom.ker S.AddCommGroup_homology_π' :=
begin
  dsimp only [AddCommGroup_homology_π],
  ext x₂,
  split,
  { intro hx₂,
    apply S.AddCommGroup_bijective_homology_iso_inv.1,
    simpa only [map_zero S.AddCommGroup_homology_iso.inv] using hx₂, },
  { intro hx₂,
    simp only [add_monoid_hom.mem_ker] at hx₂ ⊢,
    rw [comp_apply, hx₂, map_zero S.AddCommGroup_homology_iso.inv], },
end

lemma AddCommGroup_homology_π_eq_zero_iff (z : add_monoid_hom.ker S.g) :
  S.AddCommGroup_homology_π z = 0 ↔ z.1 ∈ (add_monoid_hom.range S.f) :=
begin
  change z ∈ add_monoid_hom.ker S.AddCommGroup_homology_π ↔ _,
  rw S.AddCommGroup_ker_homology_π_eq_ker_homology_π',
  exact S.AddCommGroup_homology_π'_eq_zero_iff z,
end

lemma AddCommGroup_homology_ext_iff (z z' : add_monoid_hom.ker S.g) :
  S.AddCommGroup_homology_π z = S.AddCommGroup_homology_π z' ↔ ∃ (x₁ : S.X₁), z.1 = z'.1 + S.f x₁ :=
begin
  split,
  { intro h,
    have eq : S.AddCommGroup_homology_π (z - z') = 0,
    { simp only [map_sub, h, sub_self], },
    rw S.AddCommGroup_homology_π_eq_zero_iff at eq,
    obtain ⟨x₁, hx₁⟩ := eq,
    use x₁,
    simp only [hx₁, subtype.val_eq_coe, add_subgroup_class.coe_sub, add_sub_cancel'_right], },
  { rintro ⟨x₁, hx₁⟩,
    rw [show z = z' + S.AddCommGroup_f' x₁, by { ext, exact hx₁, }],
    simp only [map_add, AddCommGroup_f'_comp_homology_π_apply, add_monoid_hom.zero_apply, add_zero], },
end

--@[ext]
lemma AddCommGroup_homology_ext (z z' : add_monoid_hom.ker S.g)
  (h : ∃ (x₁ : S.X₁), z.1 = z'.1 + S.f x₁) :
    S.AddCommGroup_homology_π z = S.AddCommGroup_homology_π z' :=
by simp only [S.AddCommGroup_homology_ext_iff, h]

variable (S)

lemma AddCommGroup_element_homology_is_zero_iff' (z : S.AddCommGroup_homology) :
  z = 0 ↔ ∃ (x₁ : S.X₁), z = S.AddCommGroup_homology_π' (S.AddCommGroup_f' x₁) :=
begin
  split,
  { rintro rfl,
    exact ⟨0, by simp only [map_zero]⟩, },
  { rintro ⟨x₁, hx₁⟩,
    simp only [hx₁, AddCommGroup_f'_comp_homology_π'_apply, zero_apply], },
end

lemma AddCommGroup_element_homology_is_zero_iff (z : S.homology) :
  z = 0 ↔ ∃ (x₁ : S.X₁), z = S.AddCommGroup_homology_π (S.AddCommGroup_f' x₁) :=
by simp only [AddCommGroup_f'_comp_homology_π_apply, add_monoid_hom.zero_apply, exists_const]

lemma AddCommGroup_exact_iff : S.exact ↔
  ∀ (x₂ : S.X₂) (hx₂ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
begin
  rw [S.AddCommGroup_left_homology_data.exact_iff, AddCommGroup.is_zero_iff],
  split,
  { intros h x₂ hx₂,
    have eq : S.AddCommGroup_homology_π' ⟨x₂, hx₂⟩ = 0 := h _,
    rw AddCommGroup_homology_π'_eq_zero_iff at eq,
    obtain ⟨x₁, hx₁⟩ := eq,
    exact ⟨x₁, hx₁⟩, },
  { intros h γ,
    obtain ⟨⟨x₂, hx₂⟩, rfl⟩ := S.AddCommGroup_surjective_homology_π' γ,
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂,
    simp only [S.AddCommGroup_homology_π'_eq_zero_iff, add_monoid_hom.mem_range, exists_apply_eq_apply], },
end

variables {S}

lemma AddCommGroup_map_from_homology_ext {A : AddCommGroup.{u}} (f f' : S.homology ⟶ A)
  (eq : ∀ (x₂ : add_monoid_hom.ker S.g), f (S.AddCommGroup_homology_π x₂) = f' (S.AddCommGroup_homology_π x₂)) :
  f = f' :=
begin
  ext,
  obtain ⟨x₂, rfl⟩ := S.AddCommGroup_surjective_homology_π x,
  exact eq x₂,
end

variables {S₁ S₂ : short_complex AddCommGroup.{u}} (φ φ' : S₁ ⟶ S₂)

@[simps]
def AddCommGroup_map_ker : of (add_monoid_hom.ker S₁.g) ⟶ of (add_monoid_hom.ker S₂.g) :=
add_monoid_hom.cod_restrict (φ.τ₂.comp (add_monoid_hom.ker S₁.g).subtype) _
  (begin
    rintro ⟨x₁, hx₁⟩,
    dsimp,
    rw add_monoid_hom.mem_ker at hx₁,
    rw [add_monoid_hom.mem_ker, ← comp_apply, φ.comm₂₃, comp_apply, hx₁, map_zero φ.τ₃],
  end)

/-@[simps]
def AddCommGroup_map_homology : S₁.AddCommGroup_homology ⟶ S₂.AddCommGroup_homology :=
submodule.liftq _ (AddCommGroup_map_ker φ ≫ S₂.AddCommGroup_homology_π')
begin
  rintros _ ⟨x₁, rfl⟩,
  simp only [linear_map.mem_ker, AddCommGroup.coe_comp, function.comp_app,
    AddCommGroup_homology_π'_eq_zero_iff],
  refine ⟨φ.τ₁ x₁, _⟩,
  dsimp [AddCommGroup_f'],
  simp only [← comp_apply, φ.comm₁₂],
end

@[simps]
def AddCommGroup_left_homology_map_data : left_homology_map_data φ S₁.AddCommGroup_left_homology_data
  S₂.AddCommGroup_left_homology_data :=
{ φK := AddCommGroup_map_ker φ,
  φH := AddCommGroup_map_homology φ,
  commi' := rfl,
  commf'' := begin
    simp only [AddCommGroup_left_homology_data_f'],
    ext x₁,
    dsimp [AddCommGroup_f'],
    simp only [← comp_apply, φ.comm₁₂],
  end,
  commπ' := by { ext x₁, rcases x₁ with ⟨x₁, hx₁⟩, refl, }, }

@[simp, reassoc, elementwise]
lemma AddCommGroup_homology_π_comp_homology_map :
  S₁.AddCommGroup_homology_π ≫ homology_map φ = AddCommGroup_map_ker φ ≫ S₂.AddCommGroup_homology_π :=
begin
  dsimp only [AddCommGroup_homology_π],
  rw (AddCommGroup_left_homology_map_data φ).homology_map_eq,
  have eq := (AddCommGroup_left_homology_map_data φ).commπ,
  dsimp only [AddCommGroup_left_homology_map_data, AddCommGroup_left_homology_data_π,
    AddCommGroup_homology_iso] at ⊢ eq,
  simp only [← reassoc_of eq, assoc, iso.inv_hom_id_assoc],
end -/

end short_complex

end category_theory
