import HodgeLean.Foundations.Program.SchoenAffineQuotientTopology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite-group invariant spectrum maps have the quotient topology without a
finite-generation premise on the coefficient algebra. -/
theorem s2_fixedAlgebra_isQuotientMap_integral (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    Topology.IsQuotientMap
      (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)) := by
  haveI : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B :=
    Algebra.IsInvariant.isIntegral _ _ G
  exact (PrimeSpectrum.isClosedMap_comap_of_isIntegral _
    (algebraMap_isIntegral_iff.mpr inferInstance)).isQuotientMap
    (PrimeSpectrum.continuous_comap _) (s2_fixedAlgebra_spec_surjective R B G)

/-- Invariant opens descend to opens without a finite-generation premise. -/
theorem s2_fixedAlgebra_isOpen_image_integral (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (U : Set (PrimeSpectrum B)) (hopen : IsOpen U)
    (hU : ∀ (g : G) (x : PrimeSpectrum B), x ∈ U → g • x ∈ U) :
    IsOpen (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B) '' U) := by
  apply (s2_fixedAlgebra_isQuotientMap_integral R B G).isCoinducing.isOpen_preimage.mp
  rw [s2_fixedAlgebra_preimage_image R B G U hU]
  exact hopen

/-- Invariant principal opens refine invariant opens for arbitrary coefficient algebras. -/
theorem s2_invariantPrincipal_refinement_integral (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
    (U : Set (PrimeSpectrum B)) (hopen : IsOpen U)
    (hU : ∀ (g : G) (x : PrimeSpectrum B), x ∈ U → g • x ∈ U)
    (x : PrimeSpectrum B) (hx : x ∈ U) :
    ∃ f : FixedPoints.subalgebra R B G,
      x ∈ PrimeSpectrum.basicOpen (f : B) ∧
      (PrimeSpectrum.basicOpen (f : B) : Set (PrimeSpectrum B)) ⊆ U := by
  let q := PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)
  have hq : IsOpen (q '' U) := s2_fixedAlgebra_isOpen_image_integral R B G U hopen hU
  obtain ⟨_, ⟨f, rfl⟩, hxf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hq (q x) ⟨x, hx, rfl⟩
  refine ⟨f, hxf, ?_⟩
  intro y hy
  have hy' : q y ∈ q '' U := hf hy
  exact (s2_fixedAlgebra_preimage_image R B G U hU) ▸ hy'

/-- An invariant spectrum projection is open on arbitrary opens without finite generation. -/
theorem s2_fixedAlgebra_isOpenMap_integral (R B G : Type) [CommRing R] [CommRing B]
    [Algebra R B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap (FixedPoints.subalgebra R B G) B)) := by
  intro U hU
  apply (s2_fixedAlgebra_isQuotientMap_integral R B G).isCoinducing.isOpen_preimage.mp
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
