import algebra.homology.short_complex.short_exact
import algebra.add_torsor

noncomputable theory

namespace category_theory

open limits category

universes v u

variables (C : Type u) [category.{v} C]

@[derive category]
def short_exact_sequence [has_zero_morphisms C] :=
full_subcategory (λ (S : short_complex C), S.short_exact)

namespace short_exact_sequence

variable {C}

section

variables [has_zero_morphisms C] (S : short_exact_sequence C)

abbreviation short_complex : short_complex C := S.1

lemma short_exact : S.short_complex.short_exact := S.2

lemma exact : S.short_complex.exact := S.short_exact.exact

instance : mono S.short_complex.f := S.short_exact.mono_f
instance : epi S.short_complex.g := S.short_exact.epi_g

end

instance five_lemma [preadditive C] [balanced C]
  {S₁ S₂ : short_exact_sequence C} (φ : S₁ ⟶ S₂)
  [is_iso φ.τ₁] [is_iso φ.τ₃] : is_iso φ.τ₂ :=
begin
  rw is_iso_iff_mono_and_epi,
  refine ⟨_, _⟩,
  { rw preadditive.mono_iff_cancel_zero,
    intros A f hf,
    let f' := S₁.short_exact.lift f
      (by simp only [assoc, ← cancel_mono φ.τ₃, ← φ.comm₂₃, reassoc_of hf, zero_comp]),
    have hf' : f' ≫ _ = _ := S₁.short_exact.lift_f _ _,
    have hf'' : f' = 0,
    { simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.short_complex.f, assoc, φ.comm₁₂,
        reassoc_of hf', hf, zero_comp], },
    rw [← hf', hf'', zero_comp], },
  { rw preadditive.epi_iff_cancel_zero,
    intros A f hf,
    let f' := S₂.short_exact.desc f
      (by simp only [← cancel_epi φ.τ₁, φ.comm₁₂_assoc, hf, comp_zero]),
    have hf' : _ ≫ f' = _ := S₂.short_exact.g_desc _ _,
    have hf'' : f' = 0,
    { simp only [← cancel_epi φ.τ₃, ← cancel_epi S₁.short_complex.g, ← φ.comm₂₃_assoc,
        hf', hf, comp_zero], },
    rw [← hf', hf'', comp_zero], },
end

end short_exact_sequence

namespace abelian

variables {C} (A B : C)

structure extension [has_zero_morphisms C] :=
(X : C)
(i : B ⟶ X)
(p : X ⟶ A)
(w : i ≫ p = 0)
(ex : (short_complex.mk _ _ w).short_exact)

namespace extension

section

variables {A B} [has_zero_morphisms C]

instance (E : extension A B) : mono E.i := E.ex.mono_f
instance (E : extension A B) : epi E.p := E.ex.epi_g

@[ext]
structure hom (E₁ E₂ : extension A B) :=
(τ : E₁.X ⟶ E₂.X)
(commi' : E₁.i ≫ τ = E₂.i . obviously)
(commp' : τ ≫ E₂.p = E₁.p . obviously)

restate_axiom hom.commi'
restate_axiom hom.commp'
attribute [simp, reassoc] w hom.commi hom.commp

@[simps]
def hom.id (E : extension A B) : hom E E :=
{ τ := 𝟙 _, }

@[simps]
def hom.comp {E₁ E₂ E₃ : extension A B} (φ : hom E₁ E₂) (φ' : hom E₂ E₃) : hom E₁ E₃ :=
{ τ := φ.τ ≫ φ'.τ, }

instance : category (extension A B) :=
{ hom := hom,
  id := hom.id,
  comp := λ E₁ E₂ E₃, hom.comp, }

@[simps]
def hom.mk' {E₁ E₂ : extension A B} (τ : E₁.X ⟶ E₂.X)
  (commi : E₁.i ≫ τ = E₂.i) (commp : τ ≫ E₂.p = E₁.p) : E₁ ⟶ E₂ :=
{ τ := τ,
  commi' := commi,
  commp' := commp, }

@[simp]
lemma comp_τ {E₁ E₂ E₃ : extension A B} (φ : E₁ ⟶ E₂) (φ' : E₂ ⟶ E₃) :
  (φ ≫ φ').τ = φ.τ ≫ φ'.τ := rfl

@[simp]
lemma id_τ (E : extension A B) :
  hom.τ (𝟙 E) = 𝟙 E.X := rfl

variables (A B)

@[simps]
def to_short_exact_sequence_functor : extension A B ⥤ short_exact_sequence C :=
{ obj := λ E, ⟨short_complex.mk E.i E.p E.w, E.ex⟩,
  map := λ E₁ E₂ φ,
  { τ₁ := 𝟙 _,
    τ₂ := φ.τ,
    τ₃ := 𝟙 _, },
  map_comp' := λ E₁ E₂ E₃ φ φ', begin
    ext,
    { dsimp, erw short_complex.comp_τ₁, dsimp, simp only [comp_id], },
    { refl, },
    { dsimp, erw short_complex.comp_τ₃, dsimp, simp only [comp_id], },
  end, }

instance : faithful (to_short_exact_sequence_functor A B) :=
⟨λ E₁ E₂ f₁ f₂ eq, begin
  ext,
  simpa only using congr_arg short_complex.hom.τ₂ eq,
end⟩

instance (E₁ E₂ : extension A B) (f : E₁ ⟶ E₂) :
  is_iso ((to_short_exact_sequence_functor A B).map f).τ₁ :=
by { dsimp, apply_instance, }

instance (E₁ E₂ : extension A B) (f : E₁ ⟶ E₂) :
  is_iso ((to_short_exact_sequence_functor A B).map f).τ₃ :=
by { dsimp, apply_instance, }

end

section preadditive

variables [has_zero_object C] [preadditive C]
  (A B) [has_binary_biproduct B A]

@[simps]
def trivial : extension A B :=
{ X := biprod B A,
  i := biprod.inl,
  p := biprod.snd,
  w := biprod.inl_snd,
  ex := short_complex.splitting.short_exact
    { r := biprod.fst,
      s := biprod.inr,
      f_r := by tidy,
      s_g := by tidy,
      id := by tidy, }, }

end preadditive

variable [abelian C]

variables {A B} {E₁ E₂ : extension A B}

instance (f : E₁ ⟶ E₂) : is_iso f.τ :=
(infer_instance : is_iso ((to_short_exact_sequence_functor A B).map f).τ₂)

instance (f : E₁ ⟶ E₂) : is_iso f :=
⟨begin
  refine ⟨⟨inv f.τ, _, _⟩, _, _⟩,
  tidy,
end⟩

@[simp, reassoc]
lemma iso_hom_inv_τ (e : E₁ ≅ E₂) : e.hom.τ ≫ e.inv.τ = 𝟙 _ :=
by rw [← comp_τ, e.hom_inv_id, id_τ]

@[simp, reassoc]
lemma iso_inv_hom_τ (e : E₁ ≅ E₂) : e.inv.τ ≫ e.hom.τ = 𝟙 _ :=
by rw [← comp_τ, e.inv_hom_id, id_τ]

@[simps]
instance has_vadd : has_vadd (A ⟶ B) (E₁ ⟶ E₂) :=
{ vadd := λ g f,
  { τ := E₁.p ≫ g ≫ E₂.i + f.τ, }, }

instance : add_action (A ⟶ B) (E₁ ⟶ E₂) :=
{ zero_vadd := by tidy,
  add_vadd := λ g₁ g₂ f, begin
    ext,
    simp only [has_vadd_vadd_τ, preadditive.add_comp, preadditive.comp_add, add_assoc],
  end, }

def hom.vsub (f₁ f₂ : E₁ ⟶ E₂) : A ⟶ B :=
begin
  let g₀ := E₂.ex.lift (f₁.τ - f₂.τ) (by simp),
  have hg₀ : g₀ ≫ E₂.i = _ := E₂.ex.lift_f _ _,
  exact E₁.ex.desc g₀ begin
    dsimp,
    simp only [← cancel_mono E₂.i, assoc, hg₀, preadditive.comp_sub,
      hom.commi, sub_self, zero_comp],
  end,
end

lemma hom.p_vsub_i (f₁ f₂ : E₁ ⟶ E₂) : E₁.p ≫ hom.vsub f₁ f₂ ≫ E₂.i = f₁.τ - f₂.τ :=
begin
  dsimp [hom.vsub],
  rw [← assoc, E₁.ex.g_desc, E₂.ex.lift_f],
end

instance has_vsub : has_vsub (A ⟶ B) (E₁ ⟶ E₂) :=
{ vsub := hom.vsub, }

@[simp, reassoc]
lemma p_has_vsub_vsub_i (f₁ f₂ : E₁ ⟶ E₂) :
  E₁.p ≫ (f₁ -ᵥ f₂) ≫ E₂.i = f₁.τ - f₂.τ :=
hom.p_vsub_i f₁ f₂

@[simp]
lemma vsub_vadd (f₁ f₂ : E₁ ⟶ E₂) :
  (f₁ -ᵥ f₂ : A ⟶ B) +ᵥ f₂ = f₁ :=
begin
  ext,
  simp only [has_vadd_vadd_τ, p_has_vsub_vsub_i, sub_add_cancel],
end

@[simp]
lemma vadd_vsub (g : A ⟶ B) (f : E₁ ⟶ E₂) :
  g +ᵥ f -ᵥ f = g :=
by rw [← cancel_mono E₂.i, ← cancel_epi E₁.p, p_has_vsub_vsub_i, has_vadd_vadd_τ, add_sub_cancel]

@[simps]
def iso_trivial_equiv (e : extension A B) :
  (e ≅ trivial A B) ≃ (short_complex.mk _ _ e.w).splitting :=
{ to_fun := λ φ,
  { r := φ.hom.τ ≫ biprod.fst,
    s := biprod.inr ≫ φ.inv.τ,
    f_r := by simp only [hom.commi_assoc, trivial_i, biprod.inl_fst],
    s_g := by simp only [assoc, hom.commp, trivial_p, biprod.inr_snd],
    id := begin
      dsimp,
      rw [← cancel_epi φ.inv.τ, ← cancel_mono φ.hom.τ],
      simp only [assoc, preadditive.comp_add, iso_inv_hom_τ_assoc, hom.commp_assoc,
        trivial_p, preadditive.add_comp, hom.commi, trivial_i, iso_inv_hom_τ, comp_id],
      erw [comp_id],
      dsimp,
      rw biprod.total,
    end },
  inv_fun := λ s, as_iso
  { τ := biprod.lift s.r e.p,
    commi' := begin
      ext,
      { simp only [assoc, biprod.lift_fst, trivial_i, biprod.inl_fst, s.f_r], },
      { simp only [w, assoc, biprod.lift_snd, trivial_i, biprod.inl_snd], },
    end, },
  left_inv := λ φ, begin
    ext,
    { tidy, },
    { dsimp,
      simpa only [biprod.lift_snd] using φ.hom.commp'.symm, },
  end,
  right_inv := λ s, short_complex.splitting.ext_r _ _ (by simp), }

@[simps]
def pull {A' : C} (E : extension A B) (π : A' ⟶ A) : extension A' B :=
{ X := pullback E.p π,
  i := pullback.lift E.i 0 (by simp),
  p := pullback.snd,
  w := pullback.lift_snd _ _ _,
  ex := short_complex.short_exact.of_f_is_kernel begin
    refine limits.kernel_fork.is_limit.of_ι _ _
      (λ Z x hx, E.ex.lift (x ≫ pullback.fst)
        (by { dsimp at hx ⊢, rw [assoc, pullback.condition, reassoc_of hx, zero_comp], })) _ _,
    { intros Z x hx,
      ext,
      { simp only [assoc, pullback.lift_fst, short_complex.short_exact.lift_f], },
      { simp only [assoc, pullback.lift_snd, comp_zero, hx], }, },
    { intros Z x hx m hm,
      simpa only [← cancel_mono E.i, assoc, short_complex.short_exact.lift_f,
        pullback.lift_fst] using hm =≫ pullback.fst, },
  end, }

@[simps]
def pull_short_complex {A' : C} (E : extension A B) (π : A' ⟶ A) :
  short_complex.mk _ _ (E.pull π).w ⟶ short_complex.mk _ _ E.w :=
{ τ₁ := 𝟙 _,
  τ₂ := pullback.fst,
  τ₃ := π,
  comm₂₃' := pullback.condition, }

@[simps]
def pull_functor {A A' : C} (π : A' ⟶ A) (B : C) : extension A B ⥤ extension A' B :=
{ obj := λ E, E.pull π,
  map := λ E₁ E₂ f,
  { τ := pullback.map _ _ _ _ f.τ (𝟙 A') (𝟙 A) (by simp) (by simp), }, }

def pull_functor_id (A B : C) : pull_functor (𝟙 A) B ≅ 𝟭 _ :=
nat_iso.of_components
  (λ E, as_iso
    { τ := pullback.fst,
      commp' := by { dsimp, rw [pullback.condition, comp_id], }, })
  (by tidy)

def pull_functor_comp {A A' A'' : C} (π : A' ⟶ A) (π' : A'' ⟶ A') (B : C) :
  pull_functor π B ⋙ pull_functor π' B ≅ pull_functor (π' ≫ π) B :=
nat_iso.of_components
  (λ E, as_iso
    { τ := pullback.lift (pullback.fst ≫ pullback.fst) pullback.snd
        (by erw [assoc, pullback.condition, pullback.condition_assoc]), })
  (by tidy)

@[simps]
def push {B' : C} (E : extension A B) (ι : B ⟶ B') : extension A B' :=
{ X := pushout E.i ι,
  i := pushout.inr,
  p := pushout.desc E.p 0 (by simp),
  w := pushout.inr_desc _ _ _,
  ex := short_complex.short_exact.of_g_is_cokernel begin
    refine limits.cokernel_cofork.is_colimit.of_π _ _
      (λ Z x hx, E.ex.desc (pushout.inl ≫ x)
      (by { dsimp at hx ⊢, rw [pushout.condition_assoc, hx, comp_zero], })) _ _,
    { intros A x hx,
      ext,
      { simp only [pushout.inl_desc_assoc, E.ex.g_desc (pushout.inl ≫ x)], },
      { simp only [pushout.inr_desc_assoc, zero_comp, hx], }, },
    { intros Z x hx m hm,
      rw [← cancel_epi E.p, E.ex.g_desc (pushout.inl ≫ x), ← hm, pushout.inl_desc_assoc], },
  end, }

@[simps]
def push_short_complex {B' : C} (E : extension A B) (ι : B ⟶ B') :
  short_complex.mk _ _ E.w ⟶ short_complex.mk _ _ (E.push ι).w :=
{ τ₁ := ι,
  τ₂ := pushout.inl,
  τ₃ := 𝟙 _,
  comm₁₂' := pushout.condition.symm, }

@[simps]
def push_functor (A : C) {B B' : C} (ι : B ⟶ B') : extension A B ⥤ extension A B' :=
{ obj := λ E, E.push ι,
  map := λ E₁ E₂ f,
  { τ := pushout.map _ _ _ _ f.τ (𝟙 B') (𝟙 B) (by simp) (by simp), }, }

def push_functor_id (A B : C) : push_functor A (𝟙 B) ≅ 𝟭 _ :=
iso.symm (nat_iso.of_components
  (λ E, as_iso
    { τ := pushout.inl,
      commi' := by { dsimp, rw [pushout.condition, id_comp], }, })
  (by tidy))

def push_functor_comp (A : C) {B B' B'' : C} (ι : B ⟶ B') (ι' : B' ⟶ B'') :
  push_functor A ι ⋙ push_functor A ι' ≅ push_functor A (ι ≫ ι') :=
iso.symm (nat_iso.of_components
  (λ E, as_iso
    { τ := pushout.desc (pushout.inl ≫ pushout.inl) pushout.inr
        (by rw [pushout.condition_assoc, pushout.condition, assoc]), })
  (by tidy))

def pull_functor_comm_push_functor {A A' B B' : C} (π : A' ⟶ A) (ι : B ⟶ B') :
  pull_functor π B ⋙ push_functor A' ι ≅
    push_functor A ι ⋙ pull_functor π B' :=
nat_iso.of_components
  (λ E, as_iso
    { τ := pushout.desc
        (pullback.map _ _ _ _ pushout.inl (𝟙 A') (𝟙 A) (by tidy) (by simp))
        (pullback.lift pushout.inr 0
          (by { dsimp, simp only [pushout.inr_desc, zero_comp], }))
        begin
          ext,
          { dsimp, simp [pushout.condition], },
          { dsimp, simp, },
        end, })
  (by tidy)

end extension

variable [abelian C]

def extensions := quotient (is_isomorphic_setoid (extension A B))

def extensions_map_src {A A' : C} (π : A' ⟶ A) (B : C) : extensions A B → extensions A' B :=
quot.map (extension.pull_functor π B).obj begin
  rintro E₁ E₂ ⟨e⟩,
  exact ⟨(extension.pull_functor π B).map_iso e⟩,
end

def extensions_map_tgt (A : C) {B B' : C} (ι : B ⟶ B') : extensions A B → extensions A B' :=
quot.map (extension.push_functor A ι).obj begin
  rintro E₁ E₂ ⟨e⟩,
  exact ⟨(extension.push_functor A ι).map_iso e⟩,
end

lemma extensions_map_src_id (A B : C) :
  extensions_map_src (𝟙 A) B = id :=
begin
  ext E,
  obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' E,
  exact quot.sound ⟨(extension.pull_functor_id A B).app E⟩,
end

lemma extensions_map_src_comp {A A' A'' : C} (π' : A'' ⟶ A') (π : A' ⟶ A) (B : C) :
  extensions_map_src π' B ∘ extensions_map_src π B = extensions_map_src (π' ≫ π) B :=
begin
  ext E,
  obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' E,
  exact quot.sound ⟨(extension.pull_functor_comp π π' B).app E⟩,
end

lemma extensions_map_tgt_id (A B : C) :
  extensions_map_tgt A (𝟙 B) = id :=
begin
  ext E,
  obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' E,
  exact quot.sound ⟨(extension.push_functor_id A B).app E⟩,
end

lemma extensions_map_tgt_comp (A : C) {B B' B'' : C} (ι : B ⟶ B') (ι' : B' ⟶ B'') :
  extensions_map_tgt A ι' ∘ extensions_map_tgt A ι = extensions_map_tgt A (ι ≫ ι') :=
begin
  ext E,
  obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' E,
  exact quot.sound ⟨(extension.push_functor_comp A ι ι').app E⟩,
end

lemma extensions_map_tgt_comp_map_src {A A' B B' : C} (π : A' ⟶ A) (ι : B ⟶ B') :
  extensions_map_tgt A' ι ∘ extensions_map_src π B =
    extensions_map_src π B' ∘ extensions_map_tgt A ι :=
begin
  ext E,
  obtain ⟨E, rfl⟩ := quotient.surjective_quotient_mk' E,
  exact quot.sound ⟨(extension.pull_functor_comm_push_functor π ι).app E⟩,
end

variable (C)

@[simps]
def extensions_functor : C ⥤ Cᵒᵖ ⥤ Type (max u v) :=
{ obj := λ B,
  { obj := λ A, extensions A.unop B,
    map := λ A A' π, extensions_map_src π.unop B,
    map_id' := λ A, extensions_map_src_id A.unop B,
    map_comp' := λ A A' A'' π π', (extensions_map_src_comp π'.unop π.unop B).symm, },
  map := λ B B' ι,
  { app := λ A, extensions_map_tgt A.unop ι,
    naturality' := λ A A' π, extensions_map_tgt_comp_map_src π.unop ι, },
  map_id' := λ B, begin
    ext A : 2,
    exact extensions_map_tgt_id A.unop B,
  end,
  map_comp' := λ B B' B'' ι ι', begin
    ext A : 2,
    exact (extensions_map_tgt_comp A.unop ι ι').symm,
  end }

end abelian

end category_theory
