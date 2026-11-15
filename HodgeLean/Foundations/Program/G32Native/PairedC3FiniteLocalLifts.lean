import HodgeLean.Ported.NYLL.SchemeTheory.Modules.LocalMorphisms
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Finitely many quotient sections lift on a common neighborhood of a point.
Source: Hartshorne, Algebraic Geometry, II.1, exactness on stalks. -/
theorem paired_c3_finite_local_lifts {X : Scheme.{0}} {M N : X.Modules}
    (p : M ⟶ N) [Epi p] {I : Type} [Finite I]
    (U : X.Opens) (s : I → Γ(N, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : I → Γ(M, V), ∀ i,
        p.app V (t i) = N.presheaf.map (homOfLE hVU).op (s i) := by
  have h := (Hom.epi_iff_locallySurjective p).mp inferInstance
  choose V hVU hxV t ht using fun i => h U (s i) x hx
  let W : X.Opens := U ⊓ ⨅ i, V i
  have hW (i : I) : W ≤ V i := inf_le_right.trans (iInf_le V i)
  refine ⟨W, inf_le_left, ⟨hx, ?_⟩,
    (fun i => M.presheaf.map (homOfLE (hW i)).op (t i)), ?_⟩
  · change x ∈ ((⨅ i, V i : X.Opens) : Set X)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  · intro i
    have hn := p.val.naturality (homOfLE (hW i)).op
    have hn' := (ConcreteCategory.congr_hom hn (t i)).symm
    change p.app W (M.presheaf.map (homOfLE (hW i)).op (t i)) = _
    change N.presheaf.map (homOfLE (hW i)).op (p.app (V i) (t i)) =
      p.app W (M.presheaf.map (homOfLE (hW i)).op (t i)) at hn'
    rw [← hn', ht]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end HodgeLean.Foundations.Program.G32Native
