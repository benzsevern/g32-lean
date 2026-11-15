import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.TruncGE

/-! The actual differential of good truncation above its boundary.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Above the truncation boundary, its canonical term isomorphisms retain the original differential.
Source: Mathlib, Algebra.Homology.Embedding.TruncGE; the actual good truncation construction.
HC no distance; AV milestone no distance.
-/
theorem truncGE_d_via_termIso {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) (b i j : ℤ) (hi : b < i) (hj : b < j) (hij : i + 1 = j) :
    (K.truncGE b).d i j =
      (K.truncGEXIso b i hi).hom ≫ K.d i j ≫ (K.truncGEXIso b j hj).inv := by
  let e := ComplexShape.embeddingUpIntGE b
  let a := (i - b).natAbs
  let a' := (j - b).natAbs
  have ha : e.f a = i := by
    change b + ((i - b).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have ha' : e.f a' = j := by
    change b + ((j - b).natAbs : ℤ) = j
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  have hab : (ComplexShape.up ℕ).Rel a a' := by
    change a + 1 = a'
    dsimp [a, a']
    omega
  have hboundary : ¬ e.BoundaryGE a := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    dsimp [a]
    omega
  change ((K.truncGE' e).extend e).d i j = _
  rw [HomologicalComplex.extend_d_eq _ e ha ha',
    HomologicalComplex.truncGE'_d_eq K e hab ha ha' hboundary]
  simp only [CochainComplex.truncGEXIso, HomologicalComplex.truncGEXIso,
    Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rfl

#print axioms truncGE_d_via_termIso
end HodgeLean.Foundations.RationalHomologyManifold
