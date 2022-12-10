import category_theory.triangulated.pretriangulated

namespace category_theory

variables (C : Type*) [category C] [has_shift C ℤ]

namespace pretriangulated

namespace triangle

@[simps]
def eval₁ : triangle C ⥤ C :=
{ obj := λ T, T.obj₁,
  map := λ T T' φ, φ.hom₁, }

@[simps]
def eval₂ : triangle C ⥤ C :=
{ obj := λ T, T.obj₂,
  map := λ T T' φ, φ.hom₂, }
@[simps]

def eval₃ : triangle C ⥤ C :=
{ obj := λ T, T.obj₃,
  map := λ T T' φ, φ.hom₃, }

variable {C}

instance is_iso_hom₁ {T T' : triangle C} (φ : T ⟶ T') [is_iso φ] : is_iso φ.hom₁ :=
by { change is_iso ((eval₁ C).map φ), apply_instance, }

instance is_iso_hom₂ {T T' : triangle C} (φ : T ⟶ T') [is_iso φ] : is_iso φ.hom₂ :=
by { change is_iso ((eval₂ C).map φ), apply_instance, }

instance is_iso_hom₃ {T T' : triangle C} (φ : T ⟶ T') [is_iso φ] : is_iso φ.hom₃ :=
by { change is_iso ((eval₃ C).map φ), apply_instance, }

end triangle

end pretriangulated

namespace iso

open pretriangulated

variable {C}

@[simps]
def triangle_eval₁ {T T' : triangle C} (e : T ≅ T') : T.obj₁ ≅ T'.obj₁ :=
(triangle.eval₁ C).map_iso e

@[simps]
def triangle_eval₂ {T T' : triangle C} (e : T ≅ T') : T.obj₂ ≅ T'.obj₂ :=
(triangle.eval₂ C).map_iso e

@[simps]
def triangle_eval₃ {T T' : triangle C} (e : T ≅ T') : T.obj₃ ≅ T'.obj₃ :=
(triangle.eval₃ C).map_iso e

@[simp, reassoc]
lemma triangle_hom_inv_id₁ {T T' : triangle C} (e : T ≅ T') : e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ :=
e.triangle_eval₁.hom_inv_id

@[simp, reassoc]
lemma triangle_hom_inv_id₂ {T T' : triangle C} (e : T ≅ T') : e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ :=
e.triangle_eval₂.hom_inv_id

@[simp, reassoc]
lemma triangle_hom_inv_id₃ {T T' : triangle C} (e : T ≅ T') : e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ :=
e.triangle_eval₃.hom_inv_id

@[simp, reassoc]
lemma triangle_inv_hom_id₁ {T T' : triangle C} (e : T ≅ T') : e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ :=
e.triangle_eval₁.inv_hom_id

@[simp, reassoc]
lemma triangle_inv_hom_id₂ {T T' : triangle C} (e : T ≅ T') : e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ :=
e.triangle_eval₂.inv_hom_id

@[simp, reassoc]
lemma triangle_inv_hom_id₃ {T T' : triangle C} (e : T ≅ T') : e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ :=
e.triangle_eval₃.inv_hom_id

end iso

end category_theory
