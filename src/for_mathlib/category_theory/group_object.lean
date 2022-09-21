import category_theory.limits.shapes.finite_products

noncomputable theory

namespace category_theory

open limits category

variables (C : Type*) [category C] [has_finite_products C]

structure add_comm_group_object :=
(X : C)
(zero : ⊤_ C ⟶ X)
(add : prod X X ⟶ X)
(neg : X ⟶ X)
(add_assoc' : prod.lift (limits.prod.map (𝟙 X) limits.prod.fst ≫ add) (limits.prod.snd ≫ limits.prod.snd) ≫ add =
  (limits.prod.map (𝟙 X) add) ≫ add)
(add_zero' : (prod.lift (terminal.from X ≫ zero) (𝟙 X)) ≫ add = 𝟙 X)
(comm' : prod.lift limits.prod.snd limits.prod.fst ≫ add = add)
(add_left_neg' : prod.lift neg (𝟙 X) ≫ add = terminal.from X ≫ zero)

instance (A : C) [G : add_comm_group_object C] : add_comm_group (A ⟶ G.X) :=
begin
  let zero : A ⟶ G.X := terminal.from A ≫ G.zero,
  let add := λ (g₁ g₂ : A ⟶ G.X), prod.lift g₁ g₂ ≫ G.add,
  have zero_add : ∀ (g : A ⟶ G.X), add zero g = g,
  { intro g,
    dsimp [add, zero],
    have h := g ≫= G.add_zero',
    simp only [← assoc, comp_id] at h,
    convert h,
    ext,
    { simp only [prod.comp_lift, prod.lift_fst, ← assoc],
      congr' 1, },
    { tidy, }, },
  have comm : ∀ (g₁ g₂ : A ⟶ G.X), add g₁ g₂ = add g₂ g₁,
  { intros g₁ g₂,
    dsimp [add],
    have h := prod.lift g₁ g₂ ≫= G.comm',
    simp only [← assoc] at h,
    convert h.symm,
    tidy, },
  exact
  { add := add,
    add_assoc := λ g₁ g₂ g₃, begin
      dsimp,
      have h := prod.lift g₁ (prod.lift g₂ g₃) ≫= G.add_assoc',
      simp only [← assoc] at h,
      convert h,
      tidy,
    end,
    add_comm := comm,
    zero := zero,
    neg := λ g, g ≫ G.neg,
    zero_add := zero_add,
    add_zero := λ g, begin
      change add g zero = g,
      rw [comm, zero_add],
    end,
    add_left_neg := λ g, begin
      change prod.lift (g ≫ G.neg) g ≫ G.add = terminal.from A ≫ G.zero,
      have h := g ≫= G.add_left_neg',
      simp only [← assoc] at h,
      convert h,
      tidy,
    end, },
end

namespace add_comm_group_object

variable {C}

def hom (G₁ G₂ : add_comm_group_object C) :=
{ f : G₁.X ⟶ G₂.X // G₁.add ≫ f = limits.prod.map f f ≫ G₂.add }

@[simps]
def hom.id (G : add_comm_group_object C) : hom G G :=
⟨𝟙 G.X, by tidy⟩

@[simps]
def hom.comp {G₁ G₂ G₃ : add_comm_group_object C} (f : hom G₁ G₂) (g : hom G₂ G₃) :
  hom G₁ G₃ :=
⟨ f.1 ≫ g.1, begin
  slice_lhs 1 2 { rw f.2,},
  rw [assoc, g.2, prod.map_map_assoc],
end⟩

instance : category (add_comm_group_object C) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z, hom.comp, }

end add_comm_group_object

end category_theory
