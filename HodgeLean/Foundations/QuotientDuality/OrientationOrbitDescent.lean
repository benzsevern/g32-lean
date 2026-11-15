import HodgeLean.Foundations.QuotientDuality.OrientationPairSequence
import HodgeLean.Foundations.QuotientDuality.OrientationAbsoluteComparison
import HodgeLean.Foundations.QuotientDuality.OrientationComplementTopology
import HodgeLean.Foundations.QuotientDuality.OrientationOpenBasis
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.EMetricSpace.Paracompact

/-! Relative rational descent for the actual orbit-complement pair map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma orbit_relative_comparison_quasiIso
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (y : orbitSpace G X) :
    QuasiIso (invariantChainInclusion G
      (relativeChainShortComplex ℚ (orbitComplementPair G X y)).X₃
      (pairRelativeChainAction G (orbitComplementPair G X y) (orbitComplementAction G X y)) ≫
        (relativeChainFunctor ℚ).map (orbitComplementPairMap G X y)) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace (orbitSpace G X) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (orbitSpace G X)
  let A := (orbitComplementPair G X y).snd
  let B := (pointComplementPair y).snd
  letI : T2Space A := inferInstanceAs (T2Space {x : X // orbitMap G X x ≠ y})
  letI : T2Space B := inferInstanceAs (T2Space {z : orbitSpace G X // z ≠ y})
  letI : PseudoMetrizableSpace A := inferInstanceAs
    (PseudoMetrizableSpace {x : X // orbitMap G X x ≠ y})
  letI : PseudoMetrizableSpace B := inferInstanceAs
    (PseudoMetrizableSpace {z : orbitSpace G X // z ≠ y})
  letI : PseudoMetricSpace A := TopologicalSpace.pseudoMetrizableSpacePseudoMetric A
  letI : PseudoMetricSpace B := TopologicalSpace.pseudoMetrizableSpacePseudoMetric B
  let q := orbitComplementProjection G X y
  let U : Opens X := ⟨{x : X | orbitMap G X x ≠ y},
    isClosed_singleton.isOpen_compl.preimage (orbitMap G X).hom.continuous⟩
  let V : Opens (orbitSpace G X) := ⟨{z | z ≠ y}, isClosed_singleton.isOpen_compl⟩
  have hA : ∀ (x : A) (W : Opens A), x ∈ W →
      ∃ Z : Opens A, x ∈ Z ∧ ContractibleSpace Z ∧ Z ≤ W :=
    contractible_open_basis_on_open X hX U
  have hB : ∀ (x : B) (W : Opens B), x ∈ W →
      ∃ Z : Opens B, x ∈ Z ∧ ContractibleSpace Z ∧ Z ≤ W :=
    contractible_open_basis_on_open (orbitSpace G X) hY V
  have hiA : ∀ (g : G) (x : A), q (g • x) = q x := by
    intro g x
    apply Subtype.ext
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hoA : ∀ (x z : A), q x = q z → ∃ g : G, g • x = z := by
    intro x z hxz
    have hbase : orbitMap G X x.1 = orbitMap G X z.1 := congrArg Subtype.val hxz
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hbase.symm)
    exact ⟨g, Subtype.ext hg⟩
  have hqA : ∀ g, deckMap G A g ≫ q = q := by
    intro g
    ext x
    exact hiA g⁻¹ x
  have hqX : ∀ g, deckMap G X g ≫ orbitMap G X = orbitMap G X := by
    intro g
    ext x
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  apply relative_invariant_comparison_quasiIso G (orbitComplementAction G X y)
    (orbitComplementPairMap G X y)
  · intro i
    obtain ⟨hinj, hsurj⟩ := finite_quotient_transfer G A B q
      (orbitComplementProjection_isQuotientMap G X y)
      (orbitComplementProjection_isClosedMap G X y) hiA hoA hA hB i
    exact finite_quotient_chain_comparison_bijective G A B q hqA
      (pairSubspaceChainAction G (orbitComplementPair G X y) (orbitComplementAction G X y))
      (fun _ => rfl) i hinj hsurj
  · intro i
    obtain ⟨hinj, hsurj⟩ := orbit_transfer_noncompact G X hX hY i
    exact finite_quotient_chain_comparison_bijective G X (orbitSpace G X) (orbitMap G X) hqX
      (pairAmbientChainAction G (orbitComplementPair G X y) (orbitComplementAction G X y))
      (fun _ => rfl) i hinj hsurj

end HodgeLean.Foundations.QuotientDuality
