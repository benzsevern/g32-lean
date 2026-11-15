import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceLocalReduction
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cModularCycles

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicTopology.Singular
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surface_reduced_orientation_generator
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) 1 C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (n : ℕ) :
    ∃ z : (SingularChainComplex ℤ (TopCat.of C)).X 2,
      ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom z = 0 ∧
      ∃ d : (SingularChainComplex (ZMod n) (TopCat.of C)).cycles 2,
        ((SingularChainComplex (ZMod n) (TopCat.of C)).iCycles 2).hom d =
          b6m_singularReduction (TopCat.of C) n 2 z ∧
        Function.Bijective (fun r : ZMod n =>
          r • ((SingularChainComplex (ZMod n) (TopCat.of C)).homologyπ 2).hom d) := by
  let X := TopCat.of C
  let K := SingularChainComplex ℤ X
  let D := SingularChainComplex (ZMod n) X
  obtain ⟨a, ha⟩ := b6m_surface_absoluteOrientation ℤ (C := C)
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 2)).mp inferInstance a
  let z := (K.iCycles 2).hom c
  have hz : (K.d 2 1).hom z = 0 :=
    ConcreteCategory.congr_hom (K.iCycles_d 2 1) c
  have hzm : (D.d 2 1).hom (b6m_singularReduction X n 2 z) = 0 := by
    calc
      _ = b6m_singularReduction X n 1 ((K.d 2 1).hom z) :=
        (b6m_singularReduction_boundary X n 1 z).symm
      _ = 0 := by rw [hz, map_zero]
  let d := b6m_cycleOfChain (ZMod n) D 2 (b6m_singularReduction X n 2 z)
    (by rw [ChainComplex.next_nat_succ 1]; exact hzm)
  have hrep : (D.iCycles 2).hom d = b6m_singularReduction X n 2 z :=
    b6m_cycleOfChain_inclusion (ZMod n) D 2 _ _
  refine ⟨z, hz, d, hrep, ?_⟩
  apply b6m_absolute_topHomology_generated_by_point_generators (ZMod n)
    (E := ℂ) Complex.finrank_real_complex ((D.homologyπ 2).hom d)
  intro x
  have hlocal := b6m_surfaceLocalClass_reduction n c d hrep ha x
  rw [hlocal]
  exact b6m_surfaceLocalClass_smul_bijective (ZMod n) x

set_option backward.isDefEq.respectTransparency false in
theorem b6m_surface_modular_homology_representatives
    (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) 1 C] [T2Space C] [CompactSpace C] [ConnectedSpace C] (n : ℕ) :
    ∀ v : (SingularChainComplex (ZMod n) (TopCat.of C)).X 2,
      ((SingularChainComplex (ZMod n) (TopCat.of C)).d 2 1).hom v = 0 →
      ∃ w : (SingularChainComplex ℤ (TopCat.of C)).X 2,
        ((SingularChainComplex ℤ (TopCat.of C)).d 2 1).hom w = 0 ∧
        ∃ u : (SingularChainComplex (ZMod n) (TopCat.of C)).X 3,
          v = b6m_singularReduction (TopCat.of C) n 2 w +
            ((SingularChainComplex (ZMod n) (TopCat.of C)).d 3 2).hom u := by
  intro v hv
  let X := TopCat.of C
  let K := SingularChainComplex ℤ X
  let D := SingularChainComplex (ZMod n) X
  obtain ⟨z, hz, d, hd, hgen⟩ := b6m_surface_reduced_orientation_generator C n
  let dv := b6m_cycleOfChain (ZMod n) D 2 v
    (by rw [ChainComplex.next_nat_succ 1]; exact hv)
  have hvrep : (D.iCycles 2).hom dv = v := b6m_cycleOfChain_inclusion (ZMod n) D 2 v _
  obtain ⟨r, hr⟩ := hgen.2 ((D.homologyπ 2).hom dv)
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective r
  let w : K.X 2 := m • z
  have hw : (K.d 2 1).hom w = 0 := by
    dsimp [w]
    rw [map_zsmul, hz, zsmul_zero]
  have hred : b6m_singularReduction X n 2 w =
      (m : ZMod n) • b6m_singularReduction X n 2 z := by
    dsimp only [w]
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hzero : (D.homologyπ 2).hom (dv - (m : ZMod n) • d) = 0 := by
    rw [map_sub, map_smul, hm]
    exact sub_eq_zero.mpr hr.symm
  obtain ⟨u, hu⟩ := (b6m_homologyπ_zero_iff_boundary (ZMod n) D 2 _).mp hzero
  have huv : (D.d 3 2).hom u = v - b6m_singularReduction X n 2 w := by
    rw [hred]
    calc
      _ = v - (m : ZMod n) • (D.iCycles 2).hom d := by
        simpa only [map_sub, map_smul, hvrep] using hu
      _ = _ := congrArg (fun y => v - (m : ZMod n) • y) hd
  exact ⟨w, hw, u, (sub_eq_iff_eq_add.mp huv.symm).trans (add_comm _ _)⟩

end HodgeLean.Foundations.Program
