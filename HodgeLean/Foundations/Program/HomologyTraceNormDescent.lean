import HodgeLean.Foundations.Program.ResolutionTraceHomotopy
import HodgeLean.Foundations.Program.TraceNormDescent
import Mathlib.Algebra.Category.Grp.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Two-sided resolution traces give descent of homology classes fixed by the normalized norm.
Source: Bredon, Sheaf Theory, second edition, Chapter V, rational finite quotient comparison. -/
theorem homology_descent_of_two_sided_trace
    {K M I J : CochainComplex AddCommGrpCat ℕ}
    (f : K ⟶ M) (cK : K ⟶ I) [QuasiIso cK] (cM : M ⟶ J) [QuasiIso cM]
    (t : M ⟶ I) (l : I ⟶ J) (N : M ⟶ M)
    (hcompat : Homotopy (f ≫ cM) (cK ≫ l))
    (hnorm : Homotopy (t ≫ l) (N ≫ cM))
    (d n : ℕ) (hd : Function.Bijective (fun x : M.homology n => d • x))
    (z : M.homology n) (hz : HomologicalComplex.homologyMap N n z = d • z) :
    ∃ x, HomologicalComplex.homologyMap f n x = z := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
  haveI : IsIso (H.map cK) := by
    change IsIso (HomologicalComplex.homologyMap cK n)
    infer_instance
  haveI : IsIso (H.map cM) := by
    change IsIso (HomologicalComplex.homologyMap cM n)
    infer_instance
  have hcK : Function.Bijective (H.map cK) := ConcreteCategory.bijective_of_isIso _
  have hcM : Function.Injective (H.map cM) := (ConcreteCategory.bijective_of_isIso _).injective
  let e := AddEquiv.ofBijective (H.map cK).hom hcK
  apply additive_descent_of_trace_norm (H.map f).hom e (H.map cM).hom hcM
    (H.map t).hom (H.map l).hom (H.map N).hom _ _ d hd z hz
  · intro x
    have h := hcompat.homologyMap_eq n
    change H.map (f ≫ cM) = H.map (cK ≫ l) at h
    rw [H.map_comp, H.map_comp] at h
    exact congrArg (fun v => v x) h
  · intro x
    have h := hnorm.homologyMap_eq n
    change H.map (t ≫ l) = H.map (N ≫ cM) at h
    rw [H.map_comp, H.map_comp] at h
    exact congrArg (fun v => v x) h

end HodgeLean.Foundations.Program
