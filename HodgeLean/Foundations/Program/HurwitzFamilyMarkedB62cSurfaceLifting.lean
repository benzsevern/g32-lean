import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceModularCycles
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cGlobalClasses
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cBoundaryLifting
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCoefficients
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalLifting
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLiftingTransfer
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cModularCycles
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalHomologyCoefficients

noncomputable section

namespace HodgeLean.Foundations.Program

open AlgebraicTopology.Singular
open scoped Manifold ContDiff

theorem b6m_surface_integral_cycle_lifting
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C] :
    ∀ (n : ℤ), n ≠ 0 →
      ∀ (c : (SingularChainComplex ℤ (TopCat.of C)).X 2)
        (z : (SingularChainComplex ℤ (TopCat.of C)).X 1),
      ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom c =
        ((SingularChainComplex ℤ (TopCat.of C)).X 1).isModule.smul n z →
        ∃ (w q : (SingularChainComplex ℤ (TopCat.of C)).X 2),
          ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom w = 0 ∧ c - w =
            ((SingularChainComplex ℤ (TopCat.of C)).X 2).isModule.smul n q := by
  intro n hn c z hc
  obtain ⟨w, q, hw, hq⟩ := b6m_integral_cycle_lifting_of_modular_cycles (TopCat.of C)
    (fun k _ => b6m_modular_cycles_lift_of_homology_representatives (TopCat.of C) k
      (b6m_surface_modular_homology_representatives C k)) n hn c z
      (hc.trans (int_smul_eq_zsmul
        ((SingularChainComplex ℤ (TopCat.of C)).X 1).isModule n z))
  exact ⟨w, q, hw, hq.trans (int_smul_eq_zsmul
    ((SingularChainComplex ℤ (TopCat.of C)).X 2).isModule n q).symm⟩

end HodgeLean.Foundations.Program
