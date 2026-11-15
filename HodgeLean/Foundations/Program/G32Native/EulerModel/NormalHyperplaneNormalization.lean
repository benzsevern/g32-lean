import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointAbsoluteTransport
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalPointCupComparison
import HodgeLean.Foundations.Program.G32Native.EulerModel.NativeCoordinatePower
import HodgeLean.Foundations.Program.G32Native.EulerModel.SubschemeIsoClass
import HodgeLean.Foundations.Program.G32Native.EulerModel.HyperplanePowerNaturality

/-! # Exact point and hyperplane normalization on the supplied projective component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual normalized coordinate-point coclass is exactly the top power of the same supplied normalized hyperplane coclass on the specified component. -/
theorem normalComponentPointCoclass_hyperplane_power
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom
      (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) :
    s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (normalComponentPointCoclass k eQ) =
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
        (s2e_classToAbsolute Q
          (s2e_componentCycle (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k := by
  classical
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let T : Finset (Fin (k + 1)) := Finset.univ.erase 0
  have hbound : T.card ≤ k := by simp [T]
  have hcard : T.card = k := by simp [T]
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral k
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth k
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  obtain ⟨hpt, _, _, _⟩ := coordinate_intersection_class PP k (Iso.refl PP) T hbound
  letI := hpt
  obtain ⟨h0, hpow⟩ := nativeCoordinatePower_normalized k hk
  letI := h0
  obtain ⟨_, _, _, c0, hc0⟩ := nativeResidueHyperplane_class k hk 0
  let j0 := s2c_subschemeι PP (s2e_s2b_residueIdeal k 0)
  let H0 := s2e_classToAbsolute PP (s2e_componentCycle j0 ℚ) 1 c0
  have hnative := (normalComponentPointCoclass_cupComparison PP k (Iso.refl PP)).symm.trans
    (hpow c0 hc0 k T hbound hcard hk)
  have hcodim : ∀ x ∈ (s2e_componentCycle
      (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ).support,
      (1 : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    rw [s2e_componentCycle_support] at hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (hyperplane_generic_coheight Q k hk eQ).ge
  letI : IsIntegral (s2c_subscheme PP (s2e_hyperplaneIdeal k)).left := h0
  have hH := normalized_subscheme_absolute_iso eQ (s2e_hyperplaneIdeal k) 1
    hcodim cH c0 hcH hc0
  rw [normalComponentPointCoclass_absolute_iso k eQ, hnative]
  change cohomologyMap ℚ (2 * k) (TopCat.ofHom (Point.continuousMap eQ.hom))
    (s2e_hyperplanePower (TopCat.of (ComplexPoint PP)) H0 k) = _
  rw [hyperplanePower_pullback]
  change s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
    (s2e_pullback ℚ eQ.hom 2 H0) k = _
  exact congrArg (fun H : Cohomology ℚ (TopCat.of (ComplexPoint Q)) 2 =>
    s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H k) hH.symm

#print axioms normalComponentPointCoclass_hyperplane_power
end HodgeLean.Foundations.Program.G32Native.EulerModel
