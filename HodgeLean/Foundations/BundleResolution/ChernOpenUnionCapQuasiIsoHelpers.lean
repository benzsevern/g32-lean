import HodgeLean.Foundations.BundleResolution.ChernBinaryGlobalCapQuasiIsoHelpers
import HodgeLean.Foundations.BundleResolution.ChernDomainRebaseCapHelpers

/-! # Actual cap quasi-isomorphisms on unions of open domains

Viewing the union as the base of the binary open cover and retaining
its actual relative total domain gives the union result.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainEvenCapExtendedMap_quasiIso_union (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k))
    (hi : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z (U ∩ V) k φ))
    (hu : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z U k φ))
    (hv : QuasiIso (i1_domainEvenCapExtendedMap X Y f Z V k φ)) :
    QuasiIso (i1_domainEvenCapExtendedMap X Y f Z (U ∪ V) k φ) := by
  let W := U ∪ V
  let XW := TopCat.of (f ⁻¹' W)
  let YW := TopCat.of W
  let fW := i1_domainBaseProjection X Y f Z W
  let ZW : Set XW := {x | x.val ∈ Z}
  let UN : Set YW := {w | w.val ∈ U}
  let VN : Set YW := {w | w.val ∈ V}
  let φW := i1_relativeCocyclePullback (i1_subsetRelativePairInclusion X Z (f ⁻¹' W)) (2 * k) φ
  have hUN : IsOpen UN := hU.preimage continuous_subtype_val
  have hVN : IsOpen VN := hV.preimage continuous_subtype_val
  have hcover : UN ∪ VN = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    exact w.property
  have huN : QuasiIso (i1_domainEvenCapExtendedMap XW YW fW ZW UN k φW) :=
    (i1_domainEvenCapExtendedMap_rebase_quasiIso_iff X Y f Z
      (show U ⊆ W from Set.subset_union_left) k φ).mpr hu
  have hvN : QuasiIso (i1_domainEvenCapExtendedMap XW YW fW ZW VN k φW) :=
    (i1_domainEvenCapExtendedMap_rebase_quasiIso_iff X Y f Z
      (show V ⊆ W from Set.subset_union_right) k φ).mpr hv
  have hiN : QuasiIso (i1_domainEvenCapExtendedMap XW YW fW ZW (UN ∩ VN) k φW) :=
    (i1_domainEvenCapExtendedMap_rebase_quasiIso_iff X Y f Z
      (show U ∩ V ⊆ W from fun _ hx => Or.inl hx.1) k φ).mpr hi
  exact i1_globalEvenCapExtendedMap_quasiIso_of_binary_cover XW YW fW ZW
    UN VN hUN hVN hcover k φW hiN huN hvN

end HodgeLean.Foundations.BundleResolution
