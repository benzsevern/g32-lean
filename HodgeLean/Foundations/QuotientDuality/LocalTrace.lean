import HodgeLean.Foundations.QuotientDuality.LocalTraceProofs

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
theorem local_fundamental (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (n : ℕ) (o : LocalRationalOrientation X n) :
    ∃! c : Homology ℚ X n, ∀ x, localOrientation X n c x = o.generator x :=
  local_fundamental_aux X a K hK eK n o

example := LocalTraceChecks.check_local_fundamental

/-- A point-supported class with local value one has global trace one.
Source: Hatcher, Algebraic Topology, section 3.3, proof of Theorem 3.26. -/
theorem local_trace_normalization (X : TopCat.{0}) (n : ℕ) (c : Homology ℚ X n) (x : X)
    (v : RelativeCohomology ℚ (pointComplementPair x) n)
    (hv : relativeCohomologyEquivDualHomology ℚ (pointComplementPair x) n v
      (localOrientation X n c x) = 1) :
    orientationIntegral X n c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) n v) = 1 :=
  local_trace_normalization_aux X n c x v hv

example := LocalTraceChecks.check_local_trace_normalization

/-- The actual middle-degree cap pairing is perfect for a rational homology manifold.
Source: Bredon, Sheaf Theory, second edition, V.9 (duality for homology manifolds); Hatcher, section 3.3, Theorem 3.30 (manifold case). -/
theorem local_middle_duality (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (k : ℕ)
    (o : LocalRationalOrientation X (2 * k + 2 * k))
    (c : Homology ℚ X (2 * k + 2 * k))
    (hc : ∀ x, localOrientation X _ c x = o.generator x)
    [FiniteDimensional ℚ (Cohomology ℚ X (2 * k))] :
    Function.Bijective (localTracePairing X (2 * k) (2 * k) c) :=
  local_middle_duality_aux X a K hK eK k o c hc

example := LocalTraceChecks.check_local_middle_duality

/-- Preserving local generators preserves the selected global class.
Source: Hatcher, Algebraic Topology, Theorem 3.26 and naturality of relative homology. -/
theorem local_homeomorph_fundamental (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (a : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) (eK : K.space ≃ₜ X) (n : ℕ) (o : LocalRationalOrientation X n)
    (c : Homology ℚ X n) (hc : ∀ x, localOrientation X n c x = o.generator x)
    (H : X ≃ₜ X)
    (hH : ∀ x, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (o.generator x) = o.generator (H x)) :
    homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c = c :=
  local_homeomorph_fundamental_aux X a K hK eK n o c hc H hH

example := LocalTraceChecks.check_local_homeomorph_fundamental

/-- Local orientation preservation gives trace and cup-pairing preservation by every deck map.
Source: Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, sections 3.2 and 3.3, naturality of cap and evaluation. -/
theorem local_deck_trace_pairing (G : Type) [Group G] (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
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
  local_deck_trace_pairing_aux G X a K hK eK p q o c hc hdeck

example := LocalTraceChecks.check_local_deck_trace_pairing

/-- A singleton fibre of local degree one establishes the actual degree-one equality and trace square.
Source: Hatcher, Algebraic Topology, section 2.2, Proposition 2.30; Bredon, Sheaf Theory, V.9. -/
theorem local_degree_one_trace (X Y : TopCat.{0}) [CompactSpace X] [T2Space X] [CompactSpace Y]
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
  local_degree_one_trace_aux X Y a K hK eK n oY cX cY hcY f x y hxy hf hlocal

example := LocalTraceChecks.check_local_degree_one_trace

end HodgeLean.Foundations.QuotientDuality
