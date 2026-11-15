import HodgeLean.Foundations.Program.G32Native.JointSelectedZeroPairEtale
import HodgeLean.Foundations.Program.G32Native.JointSelectedSymmetricQuotient
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelGeometry
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalFrames
import HodgeLean.Foundations.Program.G32Native.ZeroPairCanonicalSlice
import HodgeLean.Foundations.Program.G32Native.ZeroPairComponent

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3
  G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7
  G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11
  G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15
  G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19
  G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27
  G32JointPrefix.inst28 G32JointPrefix.inst29

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointZeroGeometry {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) where
  etale : Etale R.β₀.left
  [smoothZ : SmoothOfRelativeDimension 1 R.Z.hom]
  [smoothB : SmoothOfRelativeDimension (R.P.k + R.P.k) R.B₀.hom]
  [smoothW : SmoothOfRelativeDimension (R.P.k + R.P.k) R.W₀.hom]
  Q : Over (Spec ↧ℂ)
  [integralQ : IsIntegral Q.left]
  [projectiveQ : IsProjective Q.hom]
  [smoothQ : SmoothOfRelativeDimension R.P.k Q.hom]
  ℓ : Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ)) ⟶ R.B₀
  eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  ι : Q ⟶ R.W₀
  immersionℓ : IsClosedImmersion ℓ.left
  immersion : IsClosedImmersion ι.left
  square : ι ≫ R.β₀ = eQ.hom ≫ ℓ
  disjoint : ∀ s t : Fin S.m, s ≠ t → Disjoint
    (Set.range (ι ≫ (End.of R.d₀ ^ s.val).asHom).left)
    (Set.range (ι ≫ (End.of R.d₀ ^ t.val).asHom).left)
  union : R.β₀.left ⁻¹' Set.range ℓ.left =
    ⋃ t : Fin S.m, Set.range (ι ≫ (End.of R.d₀ ^ t.val).asHom).left
  hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint R.Z)) = R.P.k + 1
  hg : ((2 * R.P.k : ℕ) : ℤ) =
    2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint R.Z)) : ℤ) - 2
  canonical :
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint R.Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    Point.map ℓ = fun p => s2e_canonicalQuotientPoint R.Z R.B₀ (2 * R.P.k)
      (jointSelectedSymmetricQuotient R).γ hg
      ((s2e_finiteDimensionalProjectivePointEquiv R.P.k hd).symm p)

attribute [local instance] G32JointZeroGeometry.integralQ
  G32JointZeroGeometry.projectiveQ G32JointZeroGeometry.smoothQ

/-- Form U10's actual geometry from the retained zero-pair data. -/
def G32JointZeroGeometry.geometry
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    {R : G32JointPrefix J aut S} (U : G32JointZeroGeometry R) :
    G32Native.CanonicalAbelGeometry where
  k := R.P.k
  Z := R.Z
  B := R.B₀
  W := R.W₀
  Q := U.Q
  integralZ := R.inst4
  smoothCurve := R.inst5
  smoothZ := U.smoothZ
  projectiveZ := R.inst6
  integralB := R.inst9
  smoothB := U.smoothB
  projectiveB := R.inst11
  smoothW := U.smoothW
  smoothQ := U.smoothQ
  γ := (jointSelectedSymmetricQuotient R).γ
  finiteγ := (jointSelectedSymmetricQuotient R).finiteγ
  surjectiveγ := (jointSelectedSymmetricQuotient R).surjectiveγ
  invariantγ := (jointSelectedSymmetricQuotient R).invariantγ
  quotientγ := (jointSelectedSymmetricQuotient R).quotientγ
  β := R.β₀
  etaleβ := U.etale
  ℓ := U.ℓ
  eQ := U.eQ
  ι := U.ι
  immersion := U.immersion
  square := U.square
  hd := U.hd
  hg := U.hg
  canonical := U.canonical

/-- Build the canonical fibre and its component on the shared empty-branch prefix. -/
theorem jointSelectedZeroGeometry_exists
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (hEmpty : g32p_exponents S = []) :
    Nonempty (G32JointZeroGeometry R) := by
  have hlen := Fintype.card_congr R.σ
  simp only [Fintype.card_fin, hEmpty, List.length_nil] at hlen
  have hr : R.r = 0 := by omega
  have hgenus := R.hgenus
  rw [hEmpty, List.length_nil] at hgenus
  obtain ⟨hZ, hd, hg⟩ := s2e_chain_unramified_native_genus
    R.Z R.hdimZ R.eZ R.P.k R.r hr (by simpa only [hr, Nat.mul_zero] using hgenus)
  letI := hZ
  let K := jointSelectedSymmetricQuotient R
  letI := K.finiteγ
  obtain ⟨ell, hcanonical⟩ := s2e_canonicalProjective_algebraize
    R.Z R.B₀ (2 * R.P.k) R.P.k K.γ K.invariantγ hg hd
  have himm := s2e_chain_canonical_immersion R.Z R.B₀ R.P.k K.γ
    K.surjectiveγ K.invariantγ K.quotientγ hg hd ell hcanonical
  have het := jointSelectedZeroPair_etale R hEmpty
  obtain ⟨Q, hQi, hQs, hQp, eQ, ι, hι, hsquare, hdis, hunion⟩ :=
    g32n_zeroPairComponent S R.Y R.Z R.W₀ R.B₀ R.a R.e R.ha1 R.hamul
      R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.hbranch hr
      R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀
      R.d₀ R.hd₀ R.hgenerator het R.P.k ell himm
  letI := hQi
  letI := hQs
  letI := hQp
  letI := het
  have hB : TopologicalSpace.dim R.B₀.left = R.P.k + R.P.k := by
    rw [s2e_finite_curve_power_target_dimension R.Z R.B₀ R.hdimZ (R.h + 1)
      R.γ R.hγsurj, R.hselected, two_mul]
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) R.B₀.hom := by
    rw [← hB]
    infer_instance
  letI : SmoothOfRelativeDimension (R.P.k + R.P.k) R.W₀.hom := by
    rw [← Over.w R.β₀]
    simpa only [Nat.zero_add] using
      smoothOfRelativeDimension_comp 0 (R.P.k + R.P.k) R.β₀.left R.B₀.hom
  letI : SmoothOfRelativeDimension R.P.k Q.hom := by
    rw [← s2e_projective_model_dimension Q R.P.k eQ]
    infer_instance
  exact ⟨{
    etale := het, Q := Q, ℓ := ell, eQ := eQ, ι := ι
    immersionℓ := himm, immersion := hι, square := hsquare, disjoint := hdis, union := hunion
    hd := hd, hg := hg, canonical := hcanonical }⟩

#print axioms G32JointZeroGeometry.geometry
#print axioms jointSelectedZeroGeometry_exists
end HodgeLean.Foundations.Program
