import HodgeLean.Foundations.QuotientDuality.OrientationRelative
import HodgeLean.Foundations.QuotientDuality.OrientationDescent
import Mathlib.Topology.LocalAtTarget

/-! The actual action and quotient map on an orbit complement. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable (G : Type) [Group G] (X : TopCat.{0}) [MulAction G X] (y : orbitSpace G X)

instance orbitComplementMulAction : MulAction G (orbitComplementPair G X y).snd where
  smul g x := ⟨g • x.1, by
    change orbitMap G X (g • x.1) ≠ y
    rw [show orbitMap G X (g • x.1) = orbitMap G X x.1 from
      MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

instance orbitComplementContinuousConstSMul [ContinuousConstSMul G X] :
    ContinuousConstSMul G (orbitComplementPair G X y).snd where
  continuous_const_smul g := by
    apply continuous_induced_rng.mpr
    exact (continuous_const_smul g).comp continuous_subtype_val

abbrev orbitComplementProjection :
    (orbitComplementPair G X y).snd ⟶ (pointComplementPair y).snd :=
  TopPair.Hom.snd (orbitComplementPairMap G X y)

lemma orbitComplementProjection_isClosedMap [Finite G] [ContinuousConstSMul G X] :
    IsClosedMap (orbitComplementProjection G X y) :=
  (orbitMap_isClosedMap G X).restrictPreimage {z : orbitSpace G X | z ≠ y}

lemma orbitComplementProjection_isQuotientMap [T1Space (orbitSpace G X)] :
    Topology.IsQuotientMap (orbitComplementProjection G X y) := by
  have hq : Topology.IsQuotientMap (orbitMap G X) := isQuotientMap_quotient_mk'
  exact hq.restrictPreimage_isOpen
    (show IsOpen {z : orbitSpace G X | z ≠ y} from isClosed_singleton.isOpen_compl)

end HodgeLean.Foundations.QuotientDuality
