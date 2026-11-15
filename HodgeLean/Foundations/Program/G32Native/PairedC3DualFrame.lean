import HodgeLean.Foundations.Program.G32Native.PairedC3DualPresheaf
import HodgeLean.Foundations.Program.G32Native.PairedC3FrameCoordinates

/-! # Local dual functionals from actual frame coordinates -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- The local functional with specified value on a frame, on every
smaller open, using its actual frame coefficient. -/
def pairedC3FrameFunctional {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) (r : Γ(X, U)) :
    Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U) :=
  ⟨fun {Y} f => (LinearMap.mulLeft (Γ(X, Y.unop)) (X.presheaf.map f r)).comp
      (pairedC3FrameEquiv hs f.unop.le f.unop.le).symm.toLinearMap, by
    intro Y Z f g x
    change X.presheaf.map g (X.presheaf.map f r *
        (pairedC3FrameEquiv hs f.unop.le f.unop.le).symm x) =
      X.presheaf.map (f ≫ g) r *
        (pairedC3FrameEquiv hs (f ≫ g).unop.le (f ≫ g).unop.le).symm
          (M.presheaf.map g x)
    rw [map_mul]
    have hc := paired_c3_frame_coordinate_restrict hs f.unop.le f.unop.le g.unop.le x
    change (pairedC3FrameEquiv hs (f ≫ g).unop.le (f ≫ g).unop.le).symm
        (M.presheaf.map g x) = _ at hc
    rw [hc, Functor.map_comp]
    rfl⟩

#print axioms pairedC3FrameFunctional
/-- A natural local linear functional is determined by its value on
an actual frame, including its values on every smaller open. -/
theorem paired_c3_frame_functional_expansion {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    (φ : Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U))
    {W : X.Opens} (f : op U ⟶ op W) (x : Γ(M, W)) :
    φ.1 f x = X.presheaf.map f (φ.1 (𝟙 (op U)) s) *
      (pairedC3FrameEquiv hs f.unop.le f.unop.le).symm x := by
  let c := (pairedC3FrameEquiv hs f.unop.le f.unop.le).symm x
  have hx : c • M.presheaf.map f s = x :=
    (pairedC3FrameEquiv hs f.unop.le f.unop.le).apply_symm_apply x
  have hn := φ.2 (𝟙 (op U)) f s
  change X.presheaf.map f (φ.1 (𝟙 (op U)) s) =
    φ.1 ((𝟙 (op U)) ≫ f) (M.presheaf.map f s) at hn
  rw [Category.id_comp] at hn
  calc
    φ.1 f x = φ.1 f (c • M.presheaf.map f s) := congrArg (φ.1 f) hx.symm
    _ = c • φ.1 f (M.presheaf.map f s) := map_smul (φ.1 f) c _
    _ = c * X.presheaf.map f (φ.1 (𝟙 (op U)) s) := by rw [← hn]; rfl
    _ = _ := mul_comm _ _

#print axioms paired_c3_frame_functional_expansion
/-- Evaluation at the actual frame, with its full local scalar action. -/
def pairedC3FrameEvaluation {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} (s : Γ(M, U)) :
    Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U) →ₗ[Γ(X, U)]
      Γ(X, U) where
  toFun φ := φ.1 (𝟙 (op U)) s
  map_add' _ _ := rfl
  map_smul' r φ := by
    let a : Γ(X, U) := φ.1 (𝟙 (op U)) s
    change X.presheaf.map (𝟙 (op U)) r * a = r * a
    exact congrArg (fun z : Γ(X, U) => z * a)
      (ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) r)

/-- Frame evaluation is injective on all natural local functionals. -/
theorem paired_c3_frame_evaluation_injective {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) :
    Function.Injective (pairedC3FrameEvaluation s) := by
  intro φ ψ h
  apply PresheafOfModules.InternalHom.naturalFamilies_ext
  intro Y f x
  obtain ⟨W⟩ := Y
  rw [paired_c3_frame_functional_expansion hs φ f x,
    paired_c3_frame_functional_expansion hs ψ f x]
  change φ.1 (𝟙 (op U)) s = ψ.1 (𝟙 (op U)) s at h
  rw [h]

#print axioms pairedC3FrameEvaluation
#print axioms paired_c3_frame_evaluation_injective
/-- The constructed functional takes the specified scalar value on its frame. -/
theorem paired_c3_frame_functional_value {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) (r : Γ(X, U)) :
    pairedC3FrameEvaluation s (pairedC3FrameFunctional hs r) = r := by
  have he : (pairedC3FrameEquiv hs le_rfl le_rfl).symm s = 1 := by
    apply (pairedC3FrameEquiv hs le_rfl le_rfl).injective
    rw [LinearEquiv.apply_symm_apply]
    change s = (1 : Γ(X, U)) • M.presheaf.map (𝟙 (op U)) s
    rw [M.presheaf.map_id]
    exact (one_smul _ _).symm
  change X.presheaf.map (𝟙 (op U)) r *
    (pairedC3FrameEquiv hs le_rfl le_rfl).symm s = r
  rw [he, X.presheaf.map_id]
  exact mul_one _

#print axioms paired_c3_frame_functional_value
/-- Evaluation on an actual frame identifies all local functionals with scalars. -/
def pairedC3DualFrameEquiv {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) :
    Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U) ≃ₗ[Γ(X, U)]
      Γ(X, U) :=
  LinearEquiv.ofBijective (pairedC3FrameEvaluation s)
    ⟨paired_c3_frame_evaluation_injective hs,
      fun r => ⟨pairedC3FrameFunctional hs r, paired_c3_frame_functional_value hs r⟩⟩

/-- The same frame coordinates on the original native dual. -/
def pairedC3NativeDualFrameEquiv {X : Scheme.{0}} {M : X.Modules}
    {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U) :
    Γ(M.dual, U) ≃ₗ[Γ(X, U)] Γ(X, U) := by
  let e : Γ(M.dual, U) ≃ₗ[Γ(X, U)]
      Γ(pairedC3HomSheaf M (SheafOfModules.unit X.ringCatSheaf), U) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso
      (pairedC3DualPresheafIso M)).toLinearEquiv
  exact e.trans (pairedC3DualFrameEquiv hs)

#print axioms pairedC3DualFrameEquiv
#print axioms pairedC3NativeDualFrameEquiv
end HodgeLean.Foundations.Program.G32Native
