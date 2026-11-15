import HodgeLean.Foundations.Program.SchoenInvariantRings

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The spectrum map of the invariant inclusion has the quotient topology. -/
theorem s2_fixedAlgebra_isQuotientMap (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    Topology.IsQuotientMap
      (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)) := by
  let q := Spec.map (CommRingCat.ofHom
    (algebraMap (FixedPoints.subalgebra R B G) B))
  have : IsFinite q := s2_fixedAlgebra_spec_finite R B G
  exact q.isClosedMap.isQuotientMap q.continuous
    (s2_fixedAlgebra_spec_surjective R B G)

/-- Invariant opens are saturated for the affine quotient map. -/
theorem s2_fixedAlgebra_preimage_image (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G R B] (U : Set (PrimeSpectrum B))
    (hU : ∀ (g : G) (x : PrimeSpectrum B), x ∈ U → g • x ∈ U) :
    let q := PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)
    q ⁻¹' (q '' U) = U := by
  dsimp only
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    obtain ⟨g, hg⟩ := (s2_fixedAlgebra_spec_fibres R B G y x).mp heq
    have hx : x = g • y := PrimeSpectrum.ext hg
    rw [hx]
    exact hU g y hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- An invariant open descends to an open of the affine quotient. -/
theorem s2_fixedAlgebra_isOpen_image (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (U : Set (PrimeSpectrum B)) (hopen : IsOpen U)
    (hU : ∀ (g : G) (x : PrimeSpectrum B), x ∈ U → g • x ∈ U) :
    IsOpen (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) '' U) := by
  apply (s2_fixedAlgebra_isQuotientMap R B G).isCoinducing.isOpen_preimage.mp
  rw [s2_fixedAlgebra_preimage_image R B G U hU]
  exact hopen

/-- Invariant principal opens refine every invariant open in an affine chart. -/
theorem s2_invariantAffineCover (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (U : Set (PrimeSpectrum B)) (hopen : IsOpen U)
    (hU : ∀ (g : G) (x : PrimeSpectrum B), x ∈ U → g • x ∈ U)
    (x : PrimeSpectrum B) (hx : x ∈ U) :
    ∃ f : FixedPoints.subalgebra R B G,
      x ∈ PrimeSpectrum.basicOpen (f : B) ∧
      (PrimeSpectrum.basicOpen (f : B) : Set (PrimeSpectrum B)) ⊆ U := by
  let q := PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)
  have hq : IsOpen (q '' U) := s2_fixedAlgebra_isOpen_image R B G U hopen hU
  obtain ⟨_, ⟨f, rfl⟩, hxf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hq (q x) ⟨x, hx, rfl⟩
  refine ⟨f, hxf, ?_⟩
  intro y hy
  have hy' : q y ∈ q '' U := hf hy
  have hsat := s2_fixedAlgebra_preimage_image R B G U hU
  exact hsat ▸ hy'

/-- Every group element acts by an open map on the affine spectrum. -/
theorem s2_primeSpectrum_smul_isOpenMap (B G : Type) [CommRing B]
    [Group G] [MulSemiringAction G B] (g : G) :
    IsOpenMap (fun x : PrimeSpectrum B => g • x) := by
  have heq : (fun x : PrimeSpectrum B => g • x) =
      PrimeSpectrum.homeomorphOfRingEquiv (MulSemiringAction.toRingEquiv G B g) := by
    funext x
    apply PrimeSpectrum.ext
    exact Ideal.pointwise_smul_eq_comap x.asIdeal
  rw [heq]
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (MulSemiringAction.toRingEquiv G B g)).isOpenMap

/-- The affine finite-group quotient is open, even on opens that are not invariant. -/
theorem s2_fixedAlgebra_isOpenMap (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)) := by
  intro U hU
  apply (s2_fixedAlgebra_isQuotientMap R B G).isCoinducing.isOpen_preimage.mp
  have heq : PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) ⁻¹'
      (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) '' U) =
      ⋃ g : G, (fun x : PrimeSpectrum B => g • x) '' U := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      obtain ⟨g, hg⟩ := (s2_fixedAlgebra_spec_fibres R B G y x).mp heq
      exact Set.mem_iUnion.mpr ⟨g, y, hy, (PrimeSpectrum.ext hg).symm⟩
    · intro hx
      obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨y, hy, (s2_fixedAlgebra_spec_fibres R B G y (g • y)).mpr ⟨g, rfl⟩⟩
  rw [heq]
  exact isOpen_iUnion (fun g => s2_primeSpectrum_smul_isOpenMap B G g U hU)

end HodgeLean.Foundations.Program
