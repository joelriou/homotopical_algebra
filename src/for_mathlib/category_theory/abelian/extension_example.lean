import algebra.homology.short_complex.Module
import for_mathlib.category_theory.abelian.extensions_derived_category
import ring_theory.non_zero_divisors

noncomputable theory

open category_theory category_theory.abelian category_theory.limits

variables {R : Type*} [comm_ring R] (x : R)

namespace Module

@[simps]
def short_complex_ring_mod_ideal_span_singleton : short_complex (Module R) :=
{ X₁ := Module.of R R,
  X₂ := Module.of R R,
  X₃ := Module.of R (R ⧸(ideal.span {x} : ideal R)),
  f := x • 𝟙 _,
  g := Module.of_hom (submodule.mkq _),
  zero := begin
    ext1,
    erw ideal.quotient.eq_zero_iff_mem,
    rw ideal.mem_span_singleton',
    exact ⟨1, by simp⟩,
  end, }

namespace short_complex_ring_mod_ideal_span_singleton

instance : epi (short_complex_ring_mod_ideal_span_singleton x).g :=
begin
  rw Module.epi_iff_surjective,
  rintro ⟨a⟩,
  exact ⟨a, rfl⟩,
end

lemma exact : (short_complex_ring_mod_ideal_span_singleton x).exact :=
begin
  rw short_complex.Module_exact_iff,
  intros a ha,
  dsimp at a ha,
  rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton'] at ha,
  obtain ⟨b, hb⟩ := ha,
  exact ⟨b, by { dsimp, rw [← hb, mul_comm], }⟩,
end

lemma mono_f (hx : x ∈ non_zero_divisors R) :
  mono (short_complex_ring_mod_ideal_span_singleton x).f :=
begin
  simp only [Module.mono_iff_ker_eq_bot, short_complex_ring_mod_ideal_span_singleton_f],
  ext a,
  split,
  { intro ha,
    simp only [linear_map.mem_ker, linear_map.smul_apply, Module.id_apply,
      algebra.id.smul_eq_mul] at ha,
    rw mem_non_zero_divisors_iff at hx,
    simpa only [ideal.mem_bot] using hx a (by rw [mul_comm, ha]), },
  { intro ha,
    simp only [ideal.mem_bot] at ha,
    simp only [ha, linear_map.mem_ker, linear_map.smul_apply, Module.id_apply,
      algebra.id.smul_eq_mul, mul_zero], },
end

lemma short_exact (hx : x ∈ non_zero_divisors R) :
  (short_complex_ring_mod_ideal_span_singleton x).short_exact :=
begin
  haveI := mono_f x hx,
  exact short_complex.short_exact.mk (short_complex_ring_mod_ideal_span_singleton.exact x),
end

end short_complex_ring_mod_ideal_span_singleton

variable (hx : x ∈ non_zero_divisors R)

def extension_of_non_zero_divisor (hx : x ∈ non_zero_divisors R) :
  extension (Module.of R (R ⧸(ideal.span {x} : ideal R))) (Module.of R R) :=
(short_complex_ring_mod_ideal_span_singleton.short_exact x hx).extension

namespace extension_of_non_zero_divisor

lemma nonempty_iso_trivial_iff :
  nonempty (extension_of_non_zero_divisor x hx ≅ extension.trivial _ _) ↔
    is_unit x :=
begin
  split,
  { rintro ⟨e⟩,
    rw is_unit_iff_exists_inv,
    obtain ⟨s, hs⟩ := (extension.iso_trivial_equiv _).symm.surjective e,
    refine ⟨s.r (1 : R),_⟩,
    let φ : ((of R R) ⟶ (of R R)) → R := λ φ, φ (1 : R),
    have eq := congr_arg φ s.f_r,
    dsimp only [extension_of_non_zero_divisor] at eq,
    simpa only [short_complex.short_exact.extension_i,
      short_complex_ring_mod_ideal_span_singleton_f, linear.smul_comp] using eq, },
  { intro hx',
    haveI := is_unit.invertible hx',
    refine nonempty.intro _,
    equiv_rw extension.iso_trivial_equiv _,
    have h : is_zero (short_complex_ring_mod_ideal_span_singleton x).X₃,
    { rw is_zero.iff_id_eq_zero,
      ext,
      simp only [linear_map.coe_comp, function.comp_app, submodule.mkq_apply,
        ideal.quotient.mk_eq_mk, map_one, id_apply, linear_map.zero_apply],
      erw [ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton'],
      exact ⟨⅟x, by simp only [inv_of_mul_self]⟩, },
    exact
    { r := ⅟x • 𝟙 _,
      f_r := begin
        dsimp [extension_of_non_zero_divisor],
        simp only [smul_smul, linear.comp_smul, category.comp_id, inv_of_mul_self, one_smul],
      end,
      s := 0,
      s_g := h.eq_of_src _ _,
      id := begin
        dsimp [extension_of_non_zero_divisor],
        simp only [comp_zero, add_zero, linear.smul_comp, category.id_comp,
          smul_smul, inv_of_mul_self, one_smul],
      end, }, },
end

lemma δ_neq_zero  : (extension_of_non_zero_divisor x hx).δ ≠ 0 ↔ ¬is_unit x :=
by simp only [extension.δ_neq_zero_iff, ← nonempty_iso_trivial_iff x hx, not_nonempty_iff]

end extension_of_non_zero_divisor

end Module

lemma int.non_zero_divisor_of_two_le (n : ℤ) (hn : 2 ≤ n) :
  n ∈ non_zero_divisors ℤ :=
begin
  intros a ha,
  rw mul_eq_zero at ha,
  cases ha,
  { exact ha, },
  { linarith, },
end
