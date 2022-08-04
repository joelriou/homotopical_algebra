import category_theory.limits.shapes.strong_epi
import algebraic_topology.simplex_category
import tactic.equiv_rw

noncomputable theory

universes u

namespace category_theory

lemma concrete_category.bijective_of_is_iso {C : Type*} [category C]
  [concrete_category C] {X Y : C} (f : X ⟶ Y) [is_iso f] :
  function.bijective ((forget _).map f) :=
by { rw ← is_iso_iff_bijective, apply_instance, }

lemma strong_epi_of_split_epi
  {C : Type*} [category C] {A B : C} (f : A ⟶ B) [split_epi f] : strong_epi f :=
{ epi := infer_instance,
  has_lift := begin
    introsI X Y u v z hz fac,
    constructor,
    exact nonempty.intro
    { lift := section_ f ≫ u,
      fac_left' :=
        by simp only [arrow.mk_hom, arrow.hom_mk'_left, ← cancel_mono z,
          category.assoc, fac, split_epi.id_assoc f],
      fac_right' := by simp only [← cancel_epi f, arrow.mk_hom, category.assoc,
          arrow.hom_mk'_right, fac, split_epi.id_assoc f], },
  end, }

namespace functor

variables {C D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

lemma epi_iff_map [hF₁ : preserves_epimorphisms F] [hF₂ : reflects_epimorphisms F] :
  epi f ↔ epi (F.map f) :=
begin
  split,
  { introI h,
    exact F.map_epi f, },
  { exact F.epi_of_epi_map, },
end

lemma mono_iff_map [hF₁ : preserves_monomorphisms F] [hF₂ : reflects_monomorphisms F] :
  mono f ↔ mono (F.map f) :=
begin
  split,
  { introI h,
    exact F.map_mono f, },
  { exact F.mono_of_mono_map, },
end

@[ext]
lemma split_epi.ext (s₁ s₂ : split_epi f) (h : s₁.section_ = s₂.section_) : s₁ = s₂ :=
begin
  unfreezingI { cases s₁, cases s₂, },
  dsimp at *,
  subst h,
end

def split_epi_equiv [full F] [faithful F] : split_epi f ≃ split_epi (F.map f) :=
{ to_fun := λ s, ⟨F.map s.section_,
    by { rw [← F.map_comp, ← F.map_id], congr' 1, apply split_epi.id, }⟩,
  inv_fun := λ s, begin
    refine ⟨F.preimage s.section_, _⟩,
    apply F.map_injective,
    simp only [map_comp, image_preimage, map_id],
    apply split_epi.id,
  end,
  left_inv := by tidy,
  right_inv := by tidy, }

end functor

end category_theory

open category_theory

namespace simplex_category

lemma skeletal_equivalence.functor.map_eq
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  coe_fn (simplex_category.skeletal_equivalence.{u}.functor.map f) =
    ulift.up ∘ f.to_order_hom ∘ ulift.down := rfl

lemma skeletal_equivalence.functor.surjective_iff_map
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  function.surjective f.to_order_hom ↔
  function.surjective
  (simplex_category.skeletal_equivalence.{u}.functor.map f) :=
by rw [skeletal_equivalence.functor.map_eq,
    function.surjective.of_comp_iff' ulift.up_bijective, function.surjective.of_comp_iff _ ulift.down_surjective]

end simplex_category

namespace NonemptyFinLinOrd

lemma epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} {f : A ⟶ B} :
  epi f ↔ function.surjective f :=
begin
  have eq := simplex_category.skeletal_equivalence.counit_iso.hom.naturality f,
  simp only [← cancel_mono (simplex_category.skeletal_equivalence.counit_iso.inv.app B),
    category.assoc, iso.hom_inv_id_app, category.comp_id, functor.id_map] at eq,
  rw [simplex_category.skeletal_equivalence.inverse.epi_iff_map,
    simplex_category.epi_iff_surjective,
    simplex_category.skeletal_equivalence.functor.surjective_iff_map,
    ← functor.comp_map, eq, coe_comp, coe_comp,
    function.surjective.of_comp_iff, function.surjective.of_comp_iff'],
  { apply concrete_category.bijective_of_is_iso, },
  { apply function.bijective.surjective,
    apply concrete_category.bijective_of_is_iso, },
end

lemma split_epi_of_epi {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) [hf : epi f] :
  split_epi f :=
begin
  have H : ∀ (b : B), nonempty (f⁻¹' { b }),
  { rw epi_iff_surjective at hf,
    intro b,
    exact nonempty.intro ⟨(hf b).some, (hf b).some_spec⟩, },
  let φ : B → A := λ b, (H b).some.1,
  have hφ : ∀ (b : B), f (φ b) = b := λ b, (H b).some.2,
  refine ⟨⟨φ, _⟩, _⟩, swap,
  { ext b,
    apply hφ, },
  { intros a b,
    contrapose,
    intro h,
    simp only [not_le] at h ⊢,
    suffices : b ≤ a,
    { cases this.lt_or_eq with h₁ h₂,
      { assumption, },
      { exfalso,
        simpa only [h₂, lt_self_iff_false] using h, }, },
    simpa only [hφ] using f.monotone (le_of_lt h), },
end

end NonemptyFinLinOrd

namespace simplex_category

lemma split_epi_of_epi {Δ₁ Δ₂ : simplex_category}
  (θ : Δ₁ ⟶ Δ₂) [epi θ] : split_epi θ :=
begin
  equiv_rw simplex_category.skeletal_equivalence.functor.split_epi_equiv _,
  apply NonemptyFinLinOrd.split_epi_of_epi,
end

end simplex_category
