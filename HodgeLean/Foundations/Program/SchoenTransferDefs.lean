import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleClassDefs
import HodgeLean.Foundations.Program.CycleFoundationsSpans
import HodgeLean.Foundations.ComplexSheafSingular

/-! Concrete sum maps and primitive invariant subspaces for Schoen transfer.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The sum of the Abel maps of all coordinates, in the group law of the target.
Source: Schoen (1988), Remark 1.4 and Corollary 3.1. -/
def s4_sum {Y A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    (j : Y ⟶ A) (h : ℕ) : g3_power Y h ⟶ A :=
  ∏ i : Fin h, g3_proj Y h i ≫ j

example {Y A : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    (j : Y ⟶ A) : s4_sum j 0 = 1 := by
  simp only [s4_sum, Finset.univ_eq_empty, Finset.prod_empty]

/-- Singular pullback on the complex points of arbitrary scheme models.
Source: Hatcher, Algebraic Topology, §3.1. -/
def s4_singularPullback {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (n : ℕ) :=
  AlgebraicTopology.Singular.cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap f))

example {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (n : ℕ) :
    s4_singularPullback f n 0 = 0 := map_zero _

/-- Rational singular-to-sheaf comparison after pullback to a smooth model.
Source: Bredon, Sheaf Theory, III.1; `spec_singularToFieldCohomology_smul`. -/
def s4_quotientPullback {T W : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] (q : T ⟶ W) (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) n →ₗ[ℚ] HQ T n where
  toFun v := singularToFieldCohomology ℚ T n (s4_singularPullback q n v)
  map_add' v w := by
    change _ = (singularToFieldCohomology ℚ T n) _ + (singularToFieldCohomology ℚ T n) _
    rw [map_add, map_add]
  map_smul' c v := by
    change _ = c • (singularToFieldCohomology ℚ T n) _
    rw [map_smul, spec_singularToFieldCohomology_smul]

example {T W : Over (Spec ↧ℂ)} [IsIntegral T.left] [Smooth T.hom]
    (q : T ⟶ W) (n : ℕ) : s4_quotientPullback q n 0 = 0 := map_zero _

/-- Primitive residual cohomology fixed by permutations and sum-zero deck tuples.
Source: Schoen (1988), §1, Lemmas 1.1–1.2; the space U. -/
def s4_invariantPrimitive (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    Submodule ℚ (HQ (g3_power Y h) h) :=
  LinearMap.ker (Polynomial.aeval
    (homPullback (s2_action S Y a e h (s2_delta S h hh 1) 1) h)
    (Polynomial.cyclotomic S.m ℚ)) ⊓
  ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
    ⨅ σ : Equiv.Perm (Fin h),
      LinearMap.ker (homPullback (s2_action S Y a e h v.val σ) h - LinearMap.id)

example (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    0 ∈ s4_invariantPrimitive S Y a e h hh := Submodule.zero_mem _

end HodgeLean.Foundations.Program
