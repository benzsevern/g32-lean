import HodgeLean.Foundations.Program.SchoenSegrePowerGluing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual factor permutation on the finite integral projective-space power. -/
def s2_segrePowerPerm (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s2_segrePower d n ⟶ s2_segrePower d n :=
  s2_schemeProductLift n _ (fun i => s2_schemeProductπ n _ (σ.symm i))

/-- Actual factor permutations have the prescribed equation on every projective coordinate projection. -/
theorem s2_segrePowerPerm_π (d n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    s2_segrePowerPerm d n σ ≫ s2_schemeProductπ n (fun _ => g3c_P d) i =
      s2_schemeProductπ n (fun _ => g3c_P d) (σ.symm i) :=
  s2_schemeProductLift_π n _ _ i

/-- The actual tuple-chart morphism that reindexes its factors under a projective-factor permutation. -/
def s2_segrePowerChartPerm (d n : ℕ) (a : Fin n → Fin (d + 1)) (σ : Equiv.Perm (Fin n)) :
    s2_segrePowerChart d n a ⟶ s2_segrePowerChart d n (fun i => a (σ.symm i)) :=
  s2_schemeProductLift n _ (fun i => s2_schemeProductπ n _ (σ.symm i))

/-- Actual tuple-chart reindexing has its prescribed equation with every affine factor projection. -/
theorem s2_segrePowerChartPerm_π (d n : ℕ) (a : Fin n → Fin (d + 1))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    s2_segrePowerChartPerm d n a σ ≫ s2_schemeProductπ n _ i =
      s2_schemeProductπ n _ (σ.symm i) :=
  s2_schemeProductLift_π n _ _ i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual factor permutations commute with the retained tuple-chart immersions and their reindexing morphisms. -/
theorem s2_segrePowerChartPerm_ι (d n : ℕ) (a : Fin n → Fin (d + 1))
    (σ : Equiv.Perm (Fin n)) :
    s2_segrePowerChartι d n a ≫ s2_segrePowerPerm d n σ =
      s2_segrePowerChartPerm d n a σ ≫ s2_segrePowerChartι d n (fun i => a (σ.symm i)) := by
  apply s2_schemeProduct_hom_ext n (fun _ => g3c_P d)
  intro i
  simp only [Category.assoc, s2_segrePowerPerm_π, s2_segrePowerChartι_π]
  rw [← Category.assoc, s2_segrePowerChartPerm_π]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback by actual tuple-chart reindexing preserves the corresponding normalized factor coordinates. -/
theorem s2_segrePowerChartPerm_coord (d n : ℕ) (a : Fin n → Fin (d + 1))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) (k : Fin (d + 1)) :
    (s2_segrePowerChartPerm d n a σ).appTop.hom
      (s2_segrePowerCoord d n (fun j => a (σ.symm j)) i k) =
        s2_segrePowerCoord d n a (σ.symm i) k := by
  have H := congrArg
    (fun f : s2_segrePowerChart d n a ⟶
      Spec (.of (Away (UniversalGrading d) (X (a (σ.symm i)) : UniversalRing d))) =>
      f.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (chartCoordinate (a (σ.symm i)) k)))
    (s2_segrePowerChartPerm_π d n a σ i)
  exact H

end HodgeLean.Foundations.Program
