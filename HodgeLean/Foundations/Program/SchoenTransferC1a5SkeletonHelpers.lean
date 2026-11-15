import HodgeLean.Foundations.Program.SchoenTransferC1a5AttachmentHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5BasicHelpers
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! Dimension bounds and actual absolute skeletal attachment comparison.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- The relative skeleton for the initial subcomplex is the actual absolute skeleton.
Source: Mathlib skeletonOfMono and Subfunctor.range_ι. -/
lemma c1a5_initial_relative_skeleton (K : SSet.{0}) (n : ℕ) :
    SSet.skeletonOfMono (⊥ : K.Subcomplex).ι n = K.skeleton n := by
  change SSet.Subcomplex.range (⊥ : K.Subcomplex).ι ⊔ K.skeleton n = K.skeleton n
  have h : SSet.Subcomplex.range (⊥ : K.Subcomplex).ι = ⊥ := Subfunctor.range_ι _
  rw [h, bot_sup_eq]

/-- The actual absolute skeleton comparison passes across its cell attachment.
Source: Hatcher §2.1, Theorems 2.20 and 2.27; the initial relative skeletal presentation. -/
lemma c1a5_skeletal_attachment_comparison (K : SSet.{0}) [K.Finite] (n : ℕ)
    (hp : QuasiIso (c1a5Unit (K.skeleton n : SSet)))
    (hs : QuasiIso (c1a5Unit (Δ[n] : SSet.{0})))
    (hb : QuasiIso (c1a5Unit (SSet.boundary.{0} n : SSet))) :
    QuasiIso (c1a5Unit (K.skeleton (n + 1) : SSet)) := by
  have hp' := Eq.mpr (congrArg (fun A : SSet.{0} ↦ QuasiIso (c1a5Unit A))
    (congrArg SSet.Subcomplex.toSSet (c1a5_initial_relative_skeleton K n))) hp
  have hh := c1a5_relative_attachment_comparison (⊥ : K.Subcomplex).ι n hp' hs hb
  exact Eq.mp (congrArg (fun A : SSet.{0} ↦ QuasiIso (c1a5Unit A))
    (congrArg SSet.Subcomplex.toSSet (c1a5_initial_relative_skeleton K (n + 1)))) hh

end HodgeLean.Foundations.Program
