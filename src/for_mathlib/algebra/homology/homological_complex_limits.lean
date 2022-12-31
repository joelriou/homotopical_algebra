import algebra.homology.single
import category_theory.limits.shapes.finite_products
import category_theory.limits.preserves.finite

noncomputable theory

open category_theory category_theory.limits
  category_theory.category

namespace category_theory.limits

lemma is_limit.of_is_zero {J C : Type*} [category J] [category C] [has_zero_object C]
  [has_zero_morphisms C]
  (F : J ⥤ C) (hF : is_zero F) (c : cone F) (hc : is_zero c.X) : is_limit c :=
{ lift := λ s, 0,
  fac' := λ s j, (F.is_zero_iff.1 hF j).eq_of_tgt _ _,
  uniq' := λ s m hm, hc.eq_of_tgt _ _, }

lemma preserves_limits_of_shape_of_is_zero {J C D : Type*}
  [category J] [category C] [category D] [has_zero_object D] [has_zero_morphisms D]
  (G : C ⥤ D) (hG : is_zero G) :
  preserves_limits_of_shape J G :=
⟨λ F, ⟨λ c hc, begin
  rw functor.is_zero_iff at hG,
  apply is_limit.of_is_zero,
  { rw functor.is_zero_iff,
    exact λ X, hG _, },
  { exact hG c.X, },
end⟩⟩

lemma is_colimit.of_is_zero {J C : Type*} [category J] [category C] [has_zero_object C]
  [has_zero_morphisms C]
  (F : J ⥤ C) (hF : is_zero F) (c : cocone F) (hc : is_zero c.X) : is_colimit c :=
{ desc := λ s, 0,
  fac' := λ s j, (F.is_zero_iff.1 hF j).eq_of_src _ _,
  uniq' := λ s m hm, hc.eq_of_src _ _, }

lemma preserves_colimits_of_shape_of_is_zero {J C D : Type*}
  [category J] [category C] [category D] [has_zero_object D] [has_zero_morphisms D]
  (G : C ⥤ D) (hG : is_zero G):
  preserves_colimits_of_shape J G :=
⟨λ F, ⟨λ c hc, begin
  rw functor.is_zero_iff at hG,
  apply is_colimit.of_is_zero,
  { rw functor.is_zero_iff,
    exact λ X, hG _, },
  { exact hG c.X, },
end⟩⟩

end category_theory.limits

open category_theory category_theory.limits
  category_theory.category

namespace homological_complex

variables (C : Type*) {ι J : Type*} [category C] [category J] [has_zero_morphisms C]
  (c : complex_shape ι) (F : J ⥤ homological_complex C c)

def single_nat_iso_self [has_zero_object C] [decidable_eq ι] (i : ι) :
  single C c i ⋙ eval C c i ≅ 𝟭 C :=
nat_iso.of_components (λ A, single_obj_X_self C c i A) (by tidy)

lemma is_zero_single_comp_eval_of_neq [has_zero_object C] [decidable_eq ι] (i j : ι) (h : i ≠ j) :
  is_zero (single C c i ⋙ eval C c j) :=
begin
  rw functor.is_zero_iff,
  intro A,
  dsimp,
  rw if_neg,
  { exact limits.is_zero_zero C, },
  { tauto, },
end

variables {C c}

namespace limits

section

variables [∀ (n : ι), has_limit (F ⋙ homological_complex.eval C c n)]

@[protected, simps]
def cone_of_limit_eval : cone F :=
{ X :=
  { X := λ n, limit (F ⋙ homological_complex.eval C c n),
    d := λ n m, lim_map { app := λ j, (F.obj j).d n m, },
    shape' := λ n m h, begin
      ext j,
      simp only [lim_map_π, zero_comp, (F.obj j).shape _ _ h, comp_zero],
    end, },
  π :=
  { app := λ j,
    { f := λ n, limit.π _ j, },
    naturality' := λ i j φ, begin
      ext n,
      dsimp,
      erw [limit.w, id_comp],
    end, }, }

lemma is_limit_cone : is_limit (cone_of_limit_eval F) :=
{ lift := λ s,
  { f := λ n, limit.lift _ ((eval C c n).map_cone s), },
  uniq' := λ s m hm, begin
    ext n j,
    simp only [limit.lift_π, functor.map_cone_π_app, eval_map,
      ← hm, comp_f, cone_of_limit_eval_π_app_f],
  end, }

instance : has_limit F := ⟨⟨⟨ _, is_limit_cone F⟩⟩⟩

instance (n : ι) : preserves_limit F (homological_complex.eval C c n) :=
preserves_limit_of_preserves_limit_cone (is_limit_cone F)
  (is_limit.of_iso_limit (limit.is_limit _)
    (cones.ext (iso.refl _) (by tidy)))

end

section

variables [∀ (n : ι), has_colimit (F ⋙ homological_complex.eval C c n)]

@[simps]
def cocone_of_colimit_eval : cocone F :=
{ X :=
  { X := λ n, colimit (F ⋙ homological_complex.eval C c n),
    d:= λ n m, colim_map { app := λ j, (F.obj j).d n m, },
    shape' := λ n m h, begin
      ext j,
      simp only [ι_colim_map, comp_zero, (F.obj j).shape _ _ h, zero_comp],
    end, },
  ι :=
  { app := λ j,
    { f := λ n, colimit.ι (F ⋙ eval C c n) j, },
    naturality' := λ i j φ, begin
      ext n,
      dsimp,
      rw [comp_id],
      exact colimit.w (F ⋙ eval C c n) φ,
    end, }, }

lemma is_colimit_cocone : is_colimit (cocone_of_colimit_eval F) :=
{ desc := λ s,
  { f := λ n, colimit.desc _ ((eval C c n).map_cocone s), },
  uniq' := λ s m hm, begin
    ext n j,
    simp only [←hm, functor.map_cocone_ι_app, eval_map, colimit.ι_desc, comp_f,
      cocone_of_colimit_eval_ι_app_f],
  end, }

instance : has_colimit F := ⟨⟨⟨ _, is_colimit_cocone F⟩⟩⟩

instance (n : ι) : preserves_colimit F (homological_complex.eval C c n) :=
preserves_colimit_of_preserves_colimit_cocone (is_colimit_cocone F)
  (is_colimit.of_iso_colimit (colimit.is_colimit _)
    (cocones.ext (iso.refl _) (by tidy)))

end

instance [has_limits_of_shape J C] :
  has_limits_of_shape J (homological_complex C c) :=
⟨λ F, infer_instance⟩

instance [has_colimits_of_shape J C] :
  has_colimits_of_shape J (homological_complex C c) :=
⟨λ F, infer_instance⟩

instance [has_limits_of_shape J C] (n : ι) :
  preserves_limits_of_shape J (homological_complex.eval C c n) :=
⟨λ F, infer_instance⟩

instance [has_colimits_of_shape J C] (n : ι) :
  preserves_colimits_of_shape J (homological_complex.eval C c n) :=
⟨λ F, infer_instance⟩

instance [has_finite_limits C] :
  has_finite_limits (homological_complex C c) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_colimits C] :
  has_finite_colimits (homological_complex C c) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_limits C] (n : ι) :
  preserves_finite_limits (homological_complex.eval C c n) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_colimits C] (n : ι) :
  preserves_finite_colimits (homological_complex.eval C c n) :=
⟨λ J, begin
  introI,
  introI,
  apply_instance,
end⟩

instance [has_finite_products C] :
  has_finite_products (homological_complex C c) :=
⟨λ n, infer_instance⟩

instance [has_finite_coproducts C] :
  has_finite_coproducts (homological_complex C c) :=
⟨λ n, infer_instance⟩

variable {F}

def is_limit_of_eval (s : limits.cone F) [has_limits_of_shape J C]
  (hs : ∀ (i : ι), is_limit ((eval C c i).map_cone s)) : is_limit s :=
{ lift := λ t,
  { f := λ i, (hs i).lift ((eval C c i).map_cone t),
    comm' := λ i i' hii', is_limit.hom_ext (hs i') (begin
      intro j,
      have eq := λ i, (hs i).fac ((eval C c i).map_cone t),
      simp only [functor.map_cone_π_app, eval_map] at eq,
      simp only [functor.map_cone_π_app, eval_map, assoc],
      rw [eq i', ← hom.comm, reassoc_of (eq i), hom.comm],
    end), },
  fac' := λ t j, begin
    ext i,
    simp only [comp_f],
    apply (hs i).fac,
  end,
  uniq' := λ t m hm, begin
    ext i,
    exact (hs i).uniq ((eval C c i).map_cone t) (m.f i)
      (λ j, congr_fun (congr_arg homological_complex.hom.f (hm j)) i),
  end, }

def preserves_limits_of_shape_of_eval {D : Type*} [category D]
  (G : D ⥤ homological_complex C c) [has_limits_of_shape J C]
  (hG : Π (i : ι), preserves_limits_of_shape J (G ⋙ eval C c i)) :
  preserves_limits_of_shape J G :=
⟨λ F, ⟨λ s hs, is_limit_of_eval _ (λ i, begin
  let hs' := is_limit_of_preserves (G ⋙ eval C c i) hs,
  exact hs',
end)⟩⟩

def is_colimit_of_eval (s : limits.cocone F) [has_colimits_of_shape J C]
  (hs : ∀ (i : ι), is_colimit ((eval C c i).map_cocone s)) : is_colimit s :=
{ desc := λ t,
  { f := λ i, (hs i).desc ((eval C c i).map_cocone t),
    comm' := λ i i' hii', is_colimit.hom_ext (hs i) begin
      intro j,
      have eq := λ i, (hs i).fac ((eval C c i).map_cocone t),
      simp only [functor.map_cocone_ι_app, eval_map] at eq,
      simp only [functor.map_cocone_ι_app, eval_map, hom.comm_assoc],
      rw [eq i', reassoc_of (eq i), hom.comm],
    end, },
  fac' := λ t j, begin
    ext i,
    simp only [comp_f],
    apply (hs i).fac,
  end,
  uniq' := λ t m hm, begin
    ext i,
    exact (hs i).uniq ((eval C c i).map_cocone t) (m.f i)
      (λ j, congr_fun (congr_arg homological_complex.hom.f (hm j)) i),
  end, }

def preserves_colimits_of_shape_of_eval {D : Type*} [category D]
  (G : D ⥤ homological_complex C c) [has_colimits_of_shape J C]
  (hG : Π (i : ι), preserves_colimits_of_shape J (G ⋙ eval C c i)) :
  preserves_colimits_of_shape J G :=
⟨λ F, ⟨λ s hs, is_colimit_of_eval _ (λ i, begin
  let hs' := is_colimit_of_preserves (G ⋙ eval C c i) hs,
  exact hs',
end)⟩⟩


variables [has_zero_object C] [decidable_eq ι]

instance [has_zero_object C] [has_limits_of_shape J C] (i : ι) :
  preserves_limits_of_shape J (single C c i) :=
preserves_limits_of_shape_of_eval _ (λ i', begin
  by_cases i = i',
  { subst h,
    exact preserves_limits_of_shape_of_nat_iso (single_nat_iso_self C c i).symm, },
  { apply limits.preserves_limits_of_shape_of_is_zero,
    exact is_zero_single_comp_eval_of_neq C c i i' h, },
end)

instance [has_zero_object C] [has_colimits_of_shape J C] (i : ι) :
  preserves_colimits_of_shape J (single C c i) :=
preserves_colimits_of_shape_of_eval _ (λ i', begin
  by_cases i = i',
  { subst h,
    exact preserves_colimits_of_shape_of_nat_iso (single_nat_iso_self C c i).symm, },
  { apply limits.preserves_colimits_of_shape_of_is_zero,
    exact is_zero_single_comp_eval_of_neq C c i i' h, },
end)

instance [has_finite_limits C] (i : ι) : preserves_finite_limits (single C c i) :=
⟨λ J, by { introI, introI, apply_instance, }⟩

instance [has_finite_colimits C] (i : ι) : preserves_finite_colimits (single C c i) :=
⟨λ J, by { introI, introI, apply_instance, }⟩

end limits

end homological_complex
