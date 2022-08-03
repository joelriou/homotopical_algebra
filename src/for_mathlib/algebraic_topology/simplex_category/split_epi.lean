import category_theory.limits.shapes.strong_epi
import algebraic_topology.simplex_category

noncomputable theory

universes u

namespace category_theory

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

end category_theory

open category_theory

namespace NonemptyFinLinOrd

lemma epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} {f : A ⟶ B} :
  epi f ↔ function.surjective f := sorry

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
  (θ : Δ₁ ⟶ Δ₂) [epi θ] : split_epi θ := sorry

end simplex_category
