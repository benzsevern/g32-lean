import HodgeLean.Foundations.Program.SchoenCycleU1AffineStationaryKernel
import HodgeLean.Foundations.Program.SchoenCycleU1DualSpectrum
import HodgeLean.Foundations.Program.SchoenCycleU1SpecSectionAlgebra
import HodgeLean.Foundations.Program.SchoenCycleU1AffineChartNaturality

/-! # Separation of actual scheme dual-number maps from stationary kernels -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Actual complex point separation and a zero actual stationary kernel imply
separation of arbitrary dual-number scheme maps.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, affine charts and tangent maps. -/
theorem s2e_u1_scheme_dual_injective_of_stationary_kernel
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (hpoint : Function.Injective (Point.map f))
    (hkernel : ∀ u : s2e_u1_specOver (DualNumber ℂ) ⟶ X,
      u ≫ f = s2e_u1_constantDualPoint Y
        (Point.map f (Point.map u s2e_u1_dualResiduePoint)) →
      u = s2e_u1_constantDualPoint X (Point.map u s2e_u1_dualResiduePoint)) :
    Function.Injective (fun u : s2e_u1_specOver (DualNumber ℂ) ⟶ X => u ≫ f) := by
  intro u v huv
  change u ≫ f = v ≫ f at huv
  have hx : Point.map u s2e_u1_dualResiduePoint =
      Point.map v s2e_u1_dualResiduePoint := by
    apply hpoint
    change Point.map (u ≫ f) s2e_u1_dualResiduePoint =
      Point.map (v ≫ f) s2e_u1_dualResiduePoint
    rw [huv]
  have hYbasis := Y.left.isBasis_affineOpens
  rw [Opens.isBasis_iff_nbhd] at hYbasis
  obtain ⟨V, hVa, hV, _⟩ := @hYbasis ⊤
    (Point.map f (Point.map u s2e_u1_dualResiduePoint)).underlying (by trivial)
  have hpre : (Point.map u s2e_u1_dualResiduePoint).underlying ∈ f.left ⁻¹ᵁ V := by
    change f.left (Point.map u s2e_u1_dualResiduePoint).underlying ∈ V
    simpa only [Point.underlying_map] using hV
  have hXbasis := X.left.isBasis_affineOpens
  rw [Opens.isBasis_iff_nbhd] at hXbasis
  obtain ⟨U, hUa, hU, hUV⟩ := @hXbasis (f.left ⁻¹ᵁ V)
    (Point.map u s2e_u1_dualResiduePoint).underlying hpre
  letI : Subsingleton (s2e_u1_specOver (DualNumber ℂ)).left := by
    change Subsingleton (PrimeSpectrum (DualNumber ℂ))
    exact s2e_u1_dualSpectrum_subsingleton
  have huU : ⊤ ≤ u.left ⁻¹ᵁ U := by
    intro z _
    change u.left z ∈ U
    rw [Subsingleton.elim z s2e_u1_dualResiduePoint.underlying]
    simpa only [Point.underlying_map] using hU
  have hvU : ⊤ ≤ v.left ⁻¹ᵁ U := by
    intro z _
    change v.left z ∈ U
    rw [Subsingleton.elim z s2e_u1_dualResiduePoint.underlying]
    have hU' : (Point.map v s2e_u1_dualResiduePoint).underlying ∈ U := by rw [← hx]; exact hU
    simpa only [Point.underlying_map] using hU'
  letI := s2e_step1_sectionAlgebra X U
  letI := s2e_step1_sectionAlgebra Y V
  let A := Γ(X.left, U)
  let R := Γ(Y.left, V)
  let i := s2e_u1_fromSpecOver X U hUa
  let r := s2e_u1_fromSpecOver Y V hVa
  let j := s2e_u1_appLE_algHom X Y f V U hUV
  letI : Mono i.left := by change Mono hUa.fromSpec; infer_instance
  letI : Mono r.left := by change Mono hVa.fromSpec; infer_instance
  have hcomm : i ≫ f = s2e_u1_specOverMap j ≫ r :=
    s2e_u1_fromSpecOver_naturality X Y f U V hUa hVa hUV
  have hinj := s2e_u1_affine_injective_of_scheme_stationary_kernel
    X Y f hpoint hkernel A R j i r hcomm
  let φ := s2e_u1_specSectionAlgebraEvaluation (DualNumber ℂ) X u U huU
  let ψ := s2e_u1_specSectionAlgebraEvaluation (DualNumber ℂ) X v U hvU
  have huf : s2e_u1_specOverMap φ ≫ i = u :=
    s2e_u1_specSectionAlgebraEvaluation_factor (DualNumber ℂ) X u U hUa huU
  have hvf : s2e_u1_specOverMap ψ ≫ i = v :=
    s2e_u1_specSectionAlgebraEvaluation_factor (DualNumber ℂ) X v U hUa hvU
  have he : (s2e_u1_specOverMap φ ≫ i) ≫ f =
      (s2e_u1_specOverMap ψ ≫ i) ≫ f := by rw [huf, hvf]; exact huv
  simp only [Category.assoc, hcomm] at he
  have hm : s2e_u1_specOverMap (φ.comp j) ≫ r =
      s2e_u1_specOverMap (ψ.comp j) ≫ r := by
    simpa only [← Category.assoc, s2e_u1_specOverMap_comp] using he
  have hs : s2e_u1_specOverMap (φ.comp j) = s2e_u1_specOverMap (ψ.comp j) := by
    apply Over.OverMorphism.ext
    exact (cancel_mono r.left).mp (congrArg Over.Hom.left hm)
  have hφ : φ = ψ := hinj (s2e_u1_specOverMap_injective hs)
  calc
    u = s2e_u1_specOverMap φ ≫ i := huf.symm
    _ = s2e_u1_specOverMap ψ ≫ i := by rw [hφ]
    _ = v := hvf

end HodgeLean.Foundations.Program
