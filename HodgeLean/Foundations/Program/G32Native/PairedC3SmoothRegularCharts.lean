import HodgeLean.Ported.Hironaka.Scheme.Smooth.StandardChart
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.Program.G32Native.PairedC3ClosedPointCover

/-! # Regular affine equations for a smooth subscheme -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Affine sections of an ideal agree with its equations on the associated
spectrum chart.
Source: Hartshorne, Algebraic Geometry, II.5. -/
theorem paired_c3_fromSpec_ideal {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    Ideal.map (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom
      ((I.comap U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩) = I.ideal U := by
  have hle : ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1 := by
    intro x _
    change U.2.fromSpec x ∈ U.1
    have hx : U.2.fromSpec x ∈ U.2.fromSpec.opensRange := ⟨x, rfl⟩
    simpa only [U.2.opensRange_fromSpec] using hx
  have h := I.ideal_comap_of_le U.2.fromSpec U ⟨⊤, isAffineOpen_top _⟩ hle
  rw [h, Ideal.map_map]
  have he : (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom.comp
      (U.2.fromSpec.appLE U.1 ⊤ hle).hom = RingHom.id _ := by
    change ((U.2.fromSpec.appLE U.1 ⊤ hle) ≫
      (Scheme.ΓSpecIso Γ(X, U.1)).hom).hom = _
    have hm : U.2.fromSpec.appLE U.1 ⊤ hle =
        (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
      simp [Scheme.Hom.appLE, U.2.fromSpec_app_self, ← Functor.map_comp]
    rw [hm, Iso.inv_hom_id]
    rfl
  rw [he, Ideal.map_id]

/-- A smooth subscheme has regular affine equations of its actual ideal at
any closed point of its support.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; EGA IV, 17.11.1. -/
theorem paired_c3_smooth_regular_chart_closed
    {K : Type} [Field K] [PerfectField K]
    {X : Scheme.{0}} (g : X ⟶ Spec (.of K)) (n k : ℕ) (hk : k ≤ n)
    [SmoothOfRelativeDimension n g] (I : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - k) (I.subschemeι ≫ g)]
    (x : X) (hx : x ∈ I.support) (hc : IsClosed ({x} : Set X)) :
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X) (_ : IsOpenImmersion j),
      x ∈ j.opensRange ∧ ∃ f : Fin k → A,
        RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  classical
  obtain ⟨E⟩ := nonempty_etaleCoordinatesAdapted g n k I hk hx hc
  let A := Γ(X, E.U.1)
  letI := g.sectionsAlgebra E.U.1
  let F : MvPolynomial (Fin n) K →+* A := (MvPolynomial.aeval E.v).toRingHom
  have hF : F.Etale := (etale_toAffineSpace_iff g E.U.2 E.v).mp E.etale
  letI : Algebra (MvPolynomial (Fin n) K) A := F.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin n) K) A := hF
  let sel : Fin k ↪ Fin n := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  let f : Fin k → A := fun j => E.v (sel j)
  have hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) := by
    have h := (RegularPairChart.coordinateSequence_of_flat (R := K) (A := A)
      (List.ofFn sel) (List.nodup_ofFn.mpr sel.injective)).2
    have hv (j : Fin n) : algebraMap (MvPolynomial (Fin n) K) A (MvPolynomial.X j) = E.v j := by
      change (MvPolynomial.aeval E.v) (MvPolynomial.X j) = E.v j
      exact MvPolynomial.aeval_X E.v j
    simpa only [hv, List.map_ofFn, Function.comp_def, f] using h
  have hgen : I.ideal E.U = Ideal.span (Set.range f) := by
    rw [ideal_eq_centerIdeal E, EtaleCoordinatesAdapted.centerIdeal]
    congr 1
    ext a
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨⟨j.val, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨sel j, j.isLt⟩, rfl⟩
  refine ⟨A, E.U.2.fromSpec, inferInstance, ?_, f, hreg, ?_⟩
  · simpa only [E.U.2.opensRange_fromSpec] using E.mem
  · exact (paired_c3_fromSpec_ideal I E.U).trans hgen

/-- Regular affine equations for a smooth subscheme can be chosen at every
scheme point, by closed-point coverage in the smooth ambient scheme.
Source: Hartshorne, Algebraic Geometry, II.3, II.5 and II.8. -/
theorem paired_c3_smooth_regular_chart
    {K : Type} [Field K] [PerfectField K]
    {X : Scheme.{0}} (g : X ⟶ Spec (.of K)) (n k : ℕ) (hk : k ≤ n)
    [SmoothOfRelativeDimension n g] (I : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - k) (I.subschemeι ≫ g)]
    (x : X) (hx : x ∈ I.support) :
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X) (_ : IsOpenImmersion j),
      x ∈ j.opensRange ∧ ∃ f : Fin k → A,
        RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f) := by
  letI : Smooth g := SmoothOfRelativeDimension.smooth n g
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  let 𝒜 : Set X.Opens := {U | ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X)
      (_ : IsOpenImmersion j), U = j.opensRange ∧
      ∃ f : Fin k → A, RingTheory.Sequence.IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range f)}
  let O : X.Opens := ⨆ U : 𝒜, U.val
  have hcov : (I.support : Set X) ⊆ (O : Set X) := by
    apply paired_c3_closed_point_cover I.support.isClosed O.isOpen
    intro z hz hc
    obtain ⟨A, j, hj, hzj, f, hreg, hI⟩ :=
      paired_c3_smooth_regular_chart_closed g n k hk I z hz hc
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨j.opensRange, A, j, hj, rfl, f, hreg, hI⟩, hzj⟩
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
  obtain ⟨A, j, hj, hU, f, hreg, hI⟩ := U.property
  exact ⟨A, j, hj, hU ▸ hxU, f, hreg, hI⟩

#print axioms paired_c3_smooth_regular_chart
#print axioms paired_c3_smooth_regular_chart_closed
#print axioms paired_c3_fromSpec_ideal
end HodgeLean.Foundations.Program.G32Native
