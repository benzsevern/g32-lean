import HodgeLean.Foundations.Program.SchoenTransferQ3bChecks
import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Boundary
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Ramified
import HodgeLean.Foundations.Program.SchoenTransferQ3a
import HodgeLean.Foundations.Program.SchoenTransferQ3BoundaryGeometry
import HodgeLean.Foundations.Program.SchoenTransferQ3NormalizationExtension
import HodgeLean.Foundations.Program.SchoenTransferQ3Purity

/-! Retained finite-map cycle comparison, as an implication from the displayed geometric inputs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace HodgeLean.Adapters HodgeLean.RealDefs
open AlgebraicGeometry.SingularCycles
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program
/-- Retained Q3b comparison on the actual inverse-image cycle.
Source: Fulton, Intersection Theory, second edition, §§19.1–19.2; Borel–Haefliger (1961), §2; a3b4a_cycleClass_unique_of_regularBoundary. -/
theorem s4_q3b_boundary_comparison_aux (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (k : ℕ) (hk : 0 < k)
    [IsIntegral (g3_power Y (2 * k)).left]
    [Smooth (g3_power Y (2 * k)).hom] [IsProjective (g3_power Y (2 * k)).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y (2 * k) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (2 * k) → ZMod S.m) (σ : Equiv.Perm (Fin (2 * k))),
      (∑ i, v i) = 0 → s2_action S Y a e (2 * k) v σ ≫ q = q)
    (hqfib : ∀ x y : ComplexPoint (g3_power Y (2 * k)),
      Point.map q x = Point.map q y →
        ∃ (v : Fin (2 * k) → ZMod S.m) (σ : Equiv.Perm (Fin (2 * k))),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e (2 * k) v σ) x = y)
    (z : AlgebraicCycle W.left ℚ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ U : W.left.Opens, x ∈ U ∧ Smooth (U.ι ≫ W.hom))
    (c : s2e_supportedClass W z k) (hc : a3b4_IsCycleClass W.hom z k c) :
    ∃ (γ : AlgebraicCycle (g3_power Y (2 * k)).left ℚ), γ = ccm3_flatPullback q.left z ∧
      (∀ x ∈ γ.support, Order.coheight x = k) ∧
      ∃ (hS : ∀ x, Point.map q x ∈ a3b4_cycleSupport W.hom z →
        x ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ),
      let β := relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
          (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ) (a3b4_cycleSupport W.hom z) hS) c
      ∃ (B : Closeds (g3_power Y (2 * k)).left),
        B ≤ a3b4a_classAlgebraicSupport (g3_power Y (2 * k)).hom γ ∧
        (∀ x ∈ a3b4a_classAlgebraicSupport (g3_power Y (2 * k)).hom γ,
          q.left x ∈ actualBadLocus W.hom q.left → x ∈ B) ∧
        (∀ x ∈ B, ((k + 1 : ℕ) : ℕ∞) ≤ Order.coheight x) ∧
        (∀ x ∈ γ.support, q.left x ∉ actualBadLocus W.hom q.left) ∧
        (∀ x ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ, x.underlying ∉ B →
          ∃ (r : ℕ)
            (e : OpenPartialHomeomorph (ComplexPoint (g3_power Y (2 * k))) ((Fin r → ℂ) × (Fin k → ℂ))),
            x ∈ e.source ∧ a3b4_IsHolChart (g3_power Y (2 * k)).hom e ∧
            ∀ y ∈ e.source, y ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ ↔ (e y).2 = 0) ∧
        (∀ (j : ℕ), j < 2 * k → IsZero
          (supportRelativeCohomologySheaf (a3b4_an (g3_power Y (2 * k)).hom)
            (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ) j)) ∧
        (let C : Closeds (a3b4_an (g3_power Y (2 * k)).hom) :=
            ⟨a3b4_cycleSupport (g3_power Y (2 * k)).hom γ,
              a3b4a_classSupport_isClosed (g3_power Y (2 * k)).hom γ⟩
         let O : Opens (a3b4_an (g3_power Y (2 * k)).hom) :=
            (B.preimage (ComplexPoint.continuous_underlying_to_zariski
              (g3_power Y (2 * k)))).compl
         Function.Injective (fun v => fun x : O =>
           supportRelativeCohomologyGerm (a3b4_an (g3_power Y (2 * k)).hom)
             C (2 * k) O x.1 x.2 v)) ∧
        Function.Injective (relativeCohomologyMap ℚ (2 * k)
          (a3b4_neighborhoodPairMap (Point.underlying ⁻¹' (B : Set (g3_power Y (2 * k)).left))ᶜ
            (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ))) ∧
        a3b4_IsCycleClass (g3_power Y (2 * k)).hom γ k β ∧
        ∃ β' : s2e_supportedClass (g3_power Y (2 * k)) γ k,
          a3b4_IsCycleClass (g3_power Y (2 * k)).hom γ k β' ∧
          (∀ (r : ℕ)
            (e : OpenPartialHomeomorph (ComplexPoint (g3_power Y (2 * k))) ((Fin r → ℂ) × (Fin k → ℂ)))
            (hflat : ∀ y ∈ e.source, y ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ ↔ (e y).2 = 0)
            (x : ComplexPoint (g3_power Y (2 * k))), x ∈ e.source → x ∈ a3b4_cycleSupport (g3_power Y (2 * k)).hom γ →
            x.underlying ∉ B → a3b4_IsHolChart (g3_power Y (2 * k)).hom e →
            ∃ (V : Set (ComplexPoint (g3_power Y (2 * k)))), IsOpen V ∧ x ∈ V ∧
              V ⊆ (Point.underlying ⁻¹' (B : Set (g3_power Y (2 * k)).left))ᶜ ∧
              relativeCohomologyMap ℚ (2 * k)
                (a3b4_neighborhoodPairMap V (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ)) β =
              relativeCohomologyMap ℚ (2 * k)
                (a3b4_neighborhoodPairMap V (a3b4_cycleSupport (g3_power Y (2 * k)).hom γ)) β') ∧
          β = β'  := by
  classical
  let X := g3_power Y (2 * k)
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  obtain ⟨U, hUdense, hUsmooth, hUflat, hzU, γ, hγ, hcodim, hcoeff, hpush,
      hsupport, hS, hnorm⟩ :=
    s4_q3a_local_multiplicities S Y hdim k hk a e ha1 hamul W q hqsurj hqinv hqfib z hz c hc
  let β := relativeCohomologyMap ℚ (2 * k)
    (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
      (a3b4_cycleSupport X.hom γ) (a3b4_cycleSupport W.hom z) hS) c
  have hopen := s4_q3_retained_schemeMap_isOpenMap S Y (2 * k) a e ha1 hamul
    W q hqsurj hqinv hqfib
  have hco : ∀ p ∈ γ.support, (k : ℕ∞) ≤ Order.coheight p :=
    fun p hp => le_of_eq (hcodim p hp).symm
  have hgenU : ∀ p ∈ γ.support, q.left p ∈ U := by
    intro p hp
    change γ p ≠ 0 at hp
    rw [hγ, s4_q3_flatPullback_coefficient_at_image q hopen z p] at hp
    exact hzU _ (mul_ne_zero_iff.mp hp).1
  have hUcanon : U ≤ W.hom.smoothLocus := by
    letI := hUsmooth
    intro p hp
    have hh : (⟨p, hp⟩ : U.toScheme) ∈ (U.ι ≫ W.hom).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]
      trivial
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hh
  let D : Closeds X.left := U.compl.preimage q.left.continuous
  obtain ⟨B, hBS, hBD, hBc, hcharts⟩ :=
    s4_q3_regular_boundary_with_closed_set X.hom γ k hco D
      (fun p hp hn => hn (hgenU p hp))
  have hbad : ∀ p ∈ a3b4a_classAlgebraicSupport X.hom γ,
      q.left p ∈ actualBadLocus W.hom q.left → p ∈ B := by
    intro p hp hpbad
    apply hBD
    refine ⟨hp, ?_⟩
    intro hpU
    exact s4_q3_smooth_point_not_bad q hqsurj _ (hUcanon hpU) hpbad
  have hNoBad : ∀ p ∈ γ.support, q.left p ∉ actualBadLocus W.hom q.left :=
    fun p hp => s4_q3_smooth_point_not_bad q hqsurj _ (hUcanon (hgenU p hp))
  have hoffU : ∀ x ∈ a3b4_cycleSupport X.hom γ, x.underlying ∉ B →
      (Point.map q x).underlying ∈ U := by
    intro x hx hxB
    by_contra hn
    exact hxB (hBD ⟨hx, hn⟩)
  have hβ : a3b4_IsCycleClass X.hom γ k β := by
    apply s4_q3_normalized_of_normalized_off_boundary X.hom γ k hco B hBS hBc hcharts β
    intro r e heflat x hxe hx hxB he
    obtain ⟨V, hVe, hVo, hxV, hVU, hV⟩ :=
      hnorm r e heflat x hxe hx (hoffU x hx hxB) he
    exact ⟨V, hVe, hVo, hxV, hV⟩
  have hlow (j : ℕ) (hj : j < 2 * k) : IsZero
      (supportRelativeCohomologySheaf (a3b4_an X.hom) (a3b4_cycleSupport X.hom γ) j) :=
    a3b4a_classSheaf_purity_vanishing X.hom (a3b4a_classAlgebraicSupport X.hom γ) k
      (a3b4a_classAlgebraicSupport_coheight X.hom γ k hco) j hj
  have hrestrict :=
    (a3b4a_classCycle_restriction_bijective_of_boundary_codimension X.hom γ k B hBS hBc).1
  refine ⟨γ, hγ, hcodim, hS, B, hBS, hbad, hBc, hNoBad, hcharts,
    hlow, ?_, hrestrict, hβ, β, hβ, ?_, rfl⟩
  · exact s4_q3_cycle_germs_injective X.hom γ k hco _
  · intro r e heflat x hxe hx hxB he
    let O := (Point.underlying ⁻¹' (B : Set X.left))ᶜ
    have hO : IsOpen O :=
      (B.isClosed.preimage (ComplexPoint.continuous_underlying_to_zariski X)).isOpen_compl
    exact ⟨O, hO, hxB, Set.Subset.rfl, rfl⟩

example := s4_q3b_boundary_comparison_falsification

end HodgeLean.Foundations.Program
