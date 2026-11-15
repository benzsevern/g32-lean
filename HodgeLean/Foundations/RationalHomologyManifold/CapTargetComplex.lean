import HodgeLean.Foundations.RationalHomologyManifold.CapSignNormalization
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionTruncationSoftness

/-! The actual bounded supported-chain target in the fixed-cycle cap grading.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Shift the actual good orientation truncation and restrict to natural cochain degrees.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; regrading of the bounded supported-chain model.
HC no distance; AV milestone no distance.
-/
def capUnnormalizedTargetComplex (X : TopCat.{0}) (N : ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  ((subdivisionTruncatedSheafComplex X N)⟦-(N : ℤ)⟧).restriction ComplexShape.embeddingUpNat

#print axioms capUnnormalizedTargetComplex
/-- The actual degreewise integral units convert the shifted boundary signs into the fixed-cycle cap convention.
Source: Hatcher, Algebraic Topology, section 3.3; the Alexander–Whitney differential sign.
HC no distance; AV milestone no distance.
-/
def capDegreeUnit (N : ℕ) : ℕ → ℤˣ
  | 0 => 1
  | p + 1 => capDegreeUnit N p * (-1 : ℤˣ) ^ (N + p + 1)

#print axioms capDegreeUnit
/-- Normalize the actual bounded supported-chain model by the specified degreewise cap units.
Source: Hatcher, Algebraic Topology, section 3.3; transport of the Alexander–Whitney sign convention.
HC no distance; AV milestone no distance.
-/
def capTargetComplex (X : TopCat.{0}) (N : ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  signAdjustedComplex (capUnnormalizedTargetComplex X N) (capDegreeUnit N)

#print axioms capTargetComplex
/-- The cap target retains the actual shifted good truncation by the specified degreewise sign isomorphism.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; the bounded supported-chain model with cap grading.
HC no distance; AV milestone no distance.
-/
def capTargetComplexIso (X : TopCat.{0}) (N : ℕ) :
    capUnnormalizedTargetComplex X N ≅ capTargetComplex X N :=
  signAdjustedComplexIso _ _

#print axioms capTargetComplexIso
end HodgeLean.Foundations.RationalHomologyManifold
