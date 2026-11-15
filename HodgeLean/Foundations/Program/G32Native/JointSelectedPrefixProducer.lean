import HodgeLean.Foundations.Program.G32Native.SelectedPrimitiveNativeModels
import HodgeLean.Foundations.Program.G32Native.SelectedPairIndices
import HodgeLean.Foundations.Program.G32Native.SelectedPowerQuotients
import HodgeLean.Foundations.Program.G32Native.SelectedCoverDescent
import HodgeLean.Foundations.Program.G32Native.SelectedResidualDeckNative
import HodgeLean.Foundations.Program.G32Native.SelectedCurveQuotientRows
import HodgeLean.Foundations.Program.G32Native.JointSelectedPrefix

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped BigOperators Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Jointly retain the stored primitive part, curve models and both power quotients. -/
theorem jointSelectedPrefix_exists {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (f : g32p_G → AbelianEnd (g32x_J D t))
    (hf : ∀ a, homPullback (f a).hom 1 = g32x_deck D t a)
    {A : g32t_Sixfold} (X : g32p_Cover A)
    (hJ : X.J = g32x_J D t) (hAut : HEq X.aut (fun a ↦ (f a).hom))
    (hGrp : HEq X.grp (inferInstance : GrpObj (g32x_J D t)))
    (S : g32p_Supplier) (hS : g32p_Admissible X.aut S) :
    ∃ R : G32JointPrefix X.J X.aut S, R.P = X.part S hS := by
  classical
  have hCurve := s0_supplier_algebraic_aux D t hg S f hf
  obtain ⟨C₀, Y, Z, hCi, hCs, hCp, hYi, hYs, hYp, hZi, hZs, hZp,
    hCd, hYd, hZd, qC, p₀, j, a, e, eC, eY, eZ, he, ha1, hamul, hinj,
    hp₀, hqC, hpC, hpointAction, hj, cy, cz, hyMan, hzMan,
    hC, hCi', hY, hYi', hZ, hZi', hbranch, jC, hjCeq,
    hqC', hpC', hχ, hjC, primitive, hprimitive, hscalar, hrank, hgenus⟩ :=
      selectedPrimitiveNativeModels D t hg S f hf X hJ hAut hGrp hS hCurve
  letI := hCi
  letI := hCs
  letI := hCp
  letI := hYi
  letI := hYs
  letI := hYp
  letI := hZi
  letI := hZs
  letI := hZp
  letI := cy
  letI := cz
  letI := hyMan
  letI := hzMan
  let P := X.part S hS
  obtain ⟨y, rot, hy, hrot, hb⟩ := hbranch
  have hy' : Function.Injective (fun i => Point.map p₀ (eY (y i))) := by
    intro i j hij
    apply hy
    exact eZ.injective ((hpC (y i)).symm.trans (hij.trans (hpC (y j))))
  have hb' : ∀ z, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p₀ (eY z) = Point.map p₀ (eY (y i)) := by
    intro z
    rw [hb z]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hpC z).trans ((congrArg eZ hi).trans (hpC (y i)).symm)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, eZ.injective ((hpC z).symm.trans (hi.trans (hpC (y i))))⟩
  obtain ⟨hpfin, hpsurj, hporbit⟩ :=
    selectedCurveQuotientRows S Y Z (b65z_fibre c D.C t) a p₀ hp₀ eY eZ hpC hpointAction
  letI := hpfin
  obtain ⟨r, σ, hexp, hpair, h, hh, hselected, _⟩ := selectedPairIndices S hS P
  obtain ⟨W₀, B₀, hWi, hWp, hBi, hBs, hBp, q₀, hqf, hqsurj, hqinv, hq,
    gamma, hγf, hγsurj, hγinv, hγ⟩ :=
      g32n_selected_power_quotients S Y Z hZd a e ha1 hamul h
  letI := hWi
  letI := hWp
  letI := hBi
  letI := hBs
  letI := hBp
  letI := hqf
  letI := hγf
  obtain ⟨β₀, hβf, hβ₀⟩ := g32w_selectedCoverDescent S Y Z W₀ B₀ a e p₀ hp₀ h
    q₀ hqsurj hq gamma hγinv
  letI := hβf
  obtain ⟨d₀, hd₀, hgenerator, horder₀⟩ :=
    g32w_selectedResidualDeck S Y a e ha1 hamul (h + 1) q₀ hqinv hq p₀ hp₀ gamma β₀ hβ₀ hh
  refine ⟨{
    Y := Y, Z := Z, W₀ := W₀, B₀ := B₀
    inst1 := hYi, inst2 := hYs, inst3 := hYp
    inst4 := hZi, inst5 := hZs, inst6 := hZp
    inst7 := hWi, inst8 := hWp, inst9 := hBi, inst10 := hBs, inst11 := hBp
    inst12 := hpfin
    inst13 := inferInstance, inst14 := inferInstance, inst15 := cy, inst16 := hyMan
    inst17 := hqf, inst18 := hγf, inst19 := hβf
    inst25 := hCi, inst26 := hCs, inst27 := hCp, inst28 := cz, inst29 := hzMan
    hdimY := hYd, hdimZ := hZd, a := a, e := e
    ha1 := ha1, hamul := hamul, hinj := hinj, p₀ := p₀, hp₀ := hp₀
    hpsurj := hpsurj, hporbit := hporbit, C := b65z_fibre c D.C t
    eY := eY, hpointAction := hpointAction, r := r, σ := σ, y := y, rot := rot
    hrot := hrot, hy := hy', hbranch := hb', hexp := hexp, hpair := hpair
    h := h, hh := hh, q₀ := q₀, hqsurj := hqsurj, hqinv := hqinv, hq := hq
    «γ» := gamma, hγsurj := hγsurj, hγinv := hγinv, hγ := hγ
    β₀ := β₀, hβ₀ := hβ₀, d₀ := d₀, hd₀ := hd₀, hgenerator := hgenerator
    C₀ := C₀, P := P, qC := qC, jC := jC, eC := eC, eZ := eZ
    hqC := hqC', hpC := hpC', hχ := hχ, hjC := hjC
    primitive := primitive, hprimitive := hprimitive, hscalar := hscalar
    hrank := hrank, hselected := hselected, hgenus := hgenus, horder₀ := horder₀ }, rfl⟩

#print axioms jointSelectedPrefix_exists
end HodgeLean.Foundations.Program
