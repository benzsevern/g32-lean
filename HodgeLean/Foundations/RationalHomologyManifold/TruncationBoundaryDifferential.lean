import HodgeLean.Foundations.RationalHomologyManifold.TruncationDifferential

/-! The actual differential at the boundary of good truncation.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The first differential of good truncation is the original differential factored through its boundary quotient.
Source: Mathlib, Algebra.Homology.Embedding.TruncGE, truncGE'_d_eq_fromOpcycles.
HC no distance; AV milestone no distance.
-/
theorem truncGE_d_boundary {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (b : ℤ) :
    (K.truncGE b).d b (b + 1) =
      (K.truncGEXIsoOpcycles b).hom ≫ K.fromOpcycles b (b + 1) ≫
        (K.truncGEXIso b (b + 1) (by omega)).inv := by
  let e := ComplexShape.embeddingUpIntGE b
  have h₀ : e.f 0 = b := by change b + (0 : ℤ) = b; omega
  let a := (b + 1 - b).natAbs
  have ha : a = 1 := by dsimp [a]; omega
  have h₁ : e.f a = b + 1 := by rw [ha]; rfl
  have hab : (ComplexShape.up ℕ).Rel 0 a := by change 0 + 1 = a; omega
  have hbound : e.BoundaryGE 0 := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  change ((K.truncGE' e).extend e).d b (b + 1) = _
  rw [HomologicalComplex.extend_d_eq _ e h₀ h₁,
    HomologicalComplex.truncGE'_d_eq_fromOpcycles K e hab h₀ h₁ hbound]
  simp only [CochainComplex.truncGEXIsoOpcycles, CochainComplex.truncGEXIso,
    HomologicalComplex.truncGEXIsoOpcycles, HomologicalComplex.truncGEXIso,
    Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rfl

#print axioms truncGE_d_boundary
/-- The first good-truncation differential retains its boundary-quotient formula after equality of the next degree.
Source: Mathlib, Algebra.Homology.Embedding.TruncGE; equality transport of the first differential.
HC no distance; AV milestone no distance.
-/
theorem truncGE_d_boundary_of_eq {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (b j : ℤ) (hj : b + 1 = j) :
    (K.truncGE b).d b j =
      (K.truncGEXIsoOpcycles b).hom ≫ K.fromOpcycles b j ≫
        (K.truncGEXIso b j (by omega)).inv := by
  subst j
  exact truncGE_d_boundary K b

#print axioms truncGE_d_boundary_of_eq
end HodgeLean.Foundations.RationalHomologyManifold
