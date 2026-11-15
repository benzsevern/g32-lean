import HodgeLean.Foundations.RationalHomologyManifold.Basic
import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.Foundations.QuotientDuality.LocalTraceChecks
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility
import HodgeLean.Foundations.QuotientDuality.LocalOrientationSheaf
import HodgeLean.Foundations.QuotientDuality.LocalCapDuality
import HodgeLean.Foundations.QuotientDuality.LocalCompactGluing
import HodgeLean.Foundations.QuotientDuality.LocalCompactDetection
import HodgeLean.Foundations.QuotientDuality.LocalTriangulationConnectedness
import HodgeLean.Foundations.QuotientDuality.LocalZeroOrientation
import HodgeLean.Foundations.QuotientDuality.LocalZeroDuality
import HodgeLean.Foundations.QuotientDuality.LocalManifoldFundamental

/-! # Local orientation traces, duality and degree one

Geometric inputs refer to actual relative singular groups and maps.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Gluing the specified local orientation gives one global fundamental class.
Source: Hatcher, Algebraic Topology, Theorem 3.26; Bredon, Sheaf Theory, V.9. -/
theorem local_fundamental_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (n : ℕ) (o : LocalRationalOrientation X n) :
    ∃! c : Homology ℚ X n, ∀ x, localOrientation X n c x = o.generator x :=
  by
    let t : RationalHomologyManifold.FiniteTriangulation X := ⟨a, K, hK, eK⟩
    obtain ⟨c, hc⟩ := RationalHomologyManifold.fundamental_exists X t n o
    refine ⟨c, fun x => congrFun hc x, ?_⟩
    intro d hd
    let x : X := Classical.choice inferInstance
    exact RationalHomologyManifold.fundamental_unique_at_point X t n o d c x
      ((hd x).trans (congrFun hc x).symm)

example := LocalTraceChecks.check_local_fundamental

/-- A point-supported class with local value one has global trace one.
Source: Hatcher, Algebraic Topology, section 3.3, proof of Theorem 3.26. -/
theorem local_trace_normalization_aux (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n) (x : X)
    (v : RelativeCohomology ℚ (pointComplementPair x) n)
    (hv : relativeCohomologyEquivDualHomology ℚ (pointComplementPair x) n v
      (localOrientation X n c x) = 1) :
    orientationIntegral X n c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) n v) = 1 :=
  by
    change cohomologyEquivDualHomology ℚ X n
      (relativeCohomologyToAbsolute ℚ (pointComplementPair x) n v) c = 1
    exact (cohomologyEquivDualHomology_relativeCohomologyToAbsolute ℚ
      (pointComplementPair x) n v c).trans hv

example := LocalTraceChecks.check_local_trace_normalization

/-- The actual middle-degree cap pairing is perfect for a rational homology manifold.
Source: Bredon, Sheaf Theory, second edition, V.9 (duality for homology manifolds); Hatcher, section 3.3, Theorem 3.30 (manifold case). -/
theorem local_middle_duality_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (k : ℕ)
    (o : LocalRationalOrientation X (2 * k + 2 * k))
    (c : Homology ℚ X (2 * k + 2 * k))
    (hc : ∀ x, localOrientation X _ c x = o.generator x)
    [FiniteDimensional ℚ (Cohomology ℚ X (2 * k))] :
    Function.Bijective (localTracePairing X (2 * k) (2 * k) c) :=
  by
    apply localTracePairing_bijective_of_cap X (2 * k) c
    exact RationalHomologyManifold.cap_duality X ⟨a, K, hK, eK⟩
      (2 * k) (2 * k) o c (funext hc)

example := LocalTraceChecks.check_local_middle_duality

/-- Preserving local generators preserves the selected global class.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and naturality of relative homology. -/
theorem local_homeomorph_fundamental_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (n : ℕ) (o : LocalRationalOrientation X n)
    (c : Homology ℚ X n) (hc : ∀ x, localOrientation X n c x = o.generator x)
    (H : X ≃ₜ X)
    (hH : ∀ x, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (o.generator x) = o.generator (H x)) :
    homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c = c :=
  by
    obtain ⟨c₀, hc₀, hu⟩ := local_fundamental_aux X a K hK eK n o
    have hmap : ∀ y, localOrientation X n
        (homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c) y = o.generator y := by
      intro y
      obtain ⟨x, rfl⟩ := H.surjective y
      calc
        localOrientation X n
            (homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c) (H x) =
            relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
              (localOrientation X n c x) :=
          (localOrientation_map n x (H x) (pointComplementHomeomorphPairMap H x) c).symm
        _ = o.generator (H x) := by rw [hc]; exact hH x
    exact (hu _ hmap).trans (hu c hc).symm

example := LocalTraceChecks.check_local_homeomorph_fundamental

/-- Local orientation preservation gives trace and cup-pairing preservation by every deck map.
Source: Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, sections 3.2 and 3.3, naturality of cap and evaluation. -/
theorem local_deck_trace_pairing_aux (G : Type) [Group G] (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) [MulAction G X]
    [ContinuousConstSMul G X] (p q : ℕ)
    (o : LocalRationalOrientation X (p + q)) (c : Homology ℚ X (p + q))
    (hc : ∀ x, localOrientation X _ c x = o.generator x)
    (hdeck : ∀ (g : G) (x : X), relativeHomologyMap ℚ (p + q)
      (singletonFibrePairMap (deckMap G X g) x (deckMap G X g x)
        (fun z hz => (MulAction.injective g⁻¹) hz)) (o.generator x) =
      o.generator (deckMap G X g x)) :
    ∀ g : G,
      (∀ u, orientationIntegral X (p + q) c (deckRepresentation G X (p + q) g u) =
        orientationIntegral X (p + q) c u) ∧
      (∀ u v, localTracePairing X p q c
        (deckRepresentation G X p g u) (deckRepresentation G X q g v) =
        localTracePairing X p q c u v) :=
  by
    intro g
    let H : X ≃ₜ X := Homeomorph.smul g⁻¹
    have hH : ∀ x, relativeHomologyMap ℚ (p + q)
        (pointComplementHomeomorphPairMap H x) (o.generator x) = o.generator (H x) := by
      intro x
      exact hdeck g x
    have hfix : homologyMap ℚ (p + q) (deckMap G X g) c = c :=
      local_homeomorph_fundamental_aux X a K hK eK (p + q) o c hc H hH
    have htrace : ∀ u, orientationIntegral X (p + q) c
        (deckRepresentation G X (p + q) g u) = orientationIntegral X (p + q) c u := by
      intro u
      change cohomologyEquivDualHomology ℚ X (p + q)
        (cohomologyMap ℚ (p + q) (deckMap G X g) u) c = _
      rw [cohomologyEquivDualHomology_cohomologyMap, hfix]
      rfl
    refine ⟨htrace, ?_⟩
    intro u v
    have heval (u : Cohomology ℚ X p) (v : Cohomology ℚ X q) :
        localTracePairing X p q c u v = orientationIntegral X (p + q) c
          (HodgeLean.Foundations.Singular.cup X rfl u v) := by
      rw [← localTraceCup_eq_singularCup]
      change _ = cohomologyEquivDualHomology ℚ X (p + q)
        ((cohomologyEquivDualHomology ℚ X (p + q)).symm _) c
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [heval, heval]
    change orientationIntegral X (p + q) c
      (HodgeLean.Foundations.Singular.cup X rfl
        (cohomologyMap ℚ p (deckMap G X g) u)
        (cohomologyMap ℚ q (deckMap G X g) v)) = _
    rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
    exact htrace _

example := LocalTraceChecks.check_local_deck_trace_pairing

/-- A singleton fibre of local degree one establishes the actual degree-one equality and trace square.
Source: Hatcher, Algebraic Topology, section 2.2, Proposition 2.30; Bredon, Sheaf Theory, V.9. -/
theorem local_degree_one_trace_aux (X Y : TopCat.{0}) [CompactSpace X] [T2Space X] [CompactSpace Y]
    [T2Space Y] [ConnectedSpace Y]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ Y)
    (n : ℕ) (oY : LocalRationalOrientation Y n)
    (cX : Homology ℚ X n) (cY : Homology ℚ Y n)
    (hcY : ∀ y, localOrientation Y n cY y = oY.generator y)
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y)
    (hf : ∀ z, f z = y → z = x)
    (hlocal : relativeHomologyMap ℚ n (singletonFibrePairMap f x y hf)
      (localOrientation X n cX x) = oY.generator y) :
    homologyMap ℚ n f cX = cY ∧
      ∀ u, orientationIntegral X n cX (cohomologyMap ℚ n f u) =
        orientationIntegral Y n cY u :=
  by
    let c' := homologyMap ℚ n f cX
    obtain ⟨q, hq⟩ := local_values_constant Y n oY c'
    have hy : localOrientation Y n c' y = oY.generator y := by
      have hn := localOrientation_map n x y (singletonFibrePairMap f x y hf) cX
      exact hn.symm.trans hlocal
    have hq1 : q = 1 := (oY.generates y).1 (by
      change q • oY.generator y = (1 : ℚ) • oY.generator y
      rw [← hq, hy, one_smul])
    have heq : c' = cY := by
      obtain ⟨c₀, hc₀, hu⟩ := local_fundamental_aux Y a K hK eK n oY
      have hc' : ∀ z, localOrientation Y n c' z = oY.generator z := by
        intro z
        rw [hq, hq1, one_smul]
      exact (hu c' hc').trans (hu cY hcY).symm
    refine ⟨heq, ?_⟩
    intro u
    change cohomologyEquivDualHomology ℚ X n (cohomologyMap ℚ n f u) cX = _
    rw [cohomologyEquivDualHomology_cohomologyMap, show homologyMap ℚ n f cX = cY from heq]
    rfl

example := LocalTraceChecks.check_local_degree_one_trace

end HodgeLean.Foundations.QuotientDuality
