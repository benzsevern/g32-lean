import HodgeLean.Foundations.BundleThom.RelativeSubcomplexSequenceHelpers
import HodgeLean.Foundations.BundleThom.SubcomplexChainIntersectionPullbackHelpers

/-! # Actual relative chain inclusions are monomorphisms

The fixed-subspace intersection square is a pullback before taking the actual cokernels.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- An actual specified subcomplex intersection gives the corresponding ambient rational chain pullback.
Source: Hatcher, Algebraic Topology, §2.2, intersection chain construction. -/
theorem i1_subcomplexChainPullback_of_inf_eq (X : SSet) (A U V : X.Subcomplex)
    (hA : U ⊓ V = A) :
    IsPullback
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (hA ▸ (inf_le_left : U ⊓ V ≤ U))) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (hA ▸ (inf_le_right : U ⊓ V ≤ V))) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap U.ι (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap V.ι (ModuleCat.of ℚ ℚ)) := by
  subst A
  exact i1_subcomplexChainIntersections_isPullback X U V

/-- Actual inclusion of ambient subcomplexes induces a monomorphism on rational chains relative to a fixed subcomplex.
Source: Hatcher, Algebraic Topology, §2.2, relative small-chain inclusions. -/
theorem i1_relativeSubcomplexChainMap_mono (X : SSet) (Z U V : X.Subcomplex) (hUV : U ≤ V) :
    Mono ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUV)) := by
  have hi : U ⊓ (V ⊓ Z) = U ⊓ Z := by
    ext n x
    change (x ∈ U.obj n ∧ x ∈ V.obj n ∧ x ∈ Z.obj n) ↔ (x ∈ U.obj n ∧ x ∈ Z.obj n)
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hUV n h.1, h.2⟩⟩
  have hp := i1_subcomplexChainPullback_of_inf_eq X (U ⊓ Z) U (V ⊓ Z) hi
  have hw :
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ Z ≤ U)) (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE hUV) (ModuleCat.of ℚ ℚ) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_inf hUV le_rfl)) (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : V ⊓ Z ≤ V)) (ModuleCat.of ℚ ℚ) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have hs := i1_isPullback_of_postcompose ⟨hw⟩
    (SSet.chainComplexMap V.ι (ModuleCat.of ℚ ℚ)) (by
      convert hp using 1 <;> rw [← Functor.map_comp] <;> rfl)
  change Mono (cokernel.map _ _ _ _ hs.w)
  exact Abelian.mono_cokernel_map_of_isPullback hs

/-- The actual relative rational intersection–union chain sequence is short exact.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain sequence. -/
theorem i1_relativeSubcomplexChainSequence_shortExact (X : SSet) (Z U V : X.Subcomplex) :
    (i1_relativeSubcomplexChainSequence X Z U V).ShortExact := by
  haveI := i1_relativeSubcomplexChainMap_mono X Z (U ⊓ V) U inf_le_left
  refine ShortComplex.ShortExact.mk'
    (i1_relativeSubcomplexChainSequence_exact X Z U V) ?_
    (i1_relativeSubcomplexChainSequence_epi X Z U V)
  change Mono (biprod.lift _ _)
  infer_instance

end HodgeLean.Foundations.BundleThom
