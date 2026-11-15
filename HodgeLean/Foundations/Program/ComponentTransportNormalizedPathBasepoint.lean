import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathWord

/-! # Postcomposition of based transport -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Transport along a mapped path commutes with the induced group homomorphism.
Source: Mathlib `FundamentalGroup.fundamentalGroupMulEquivOfPath`; path concatenation. -/
theorem rtc_transport_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (β : Path x y) (η : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
      (FundamentalGroup.map f x η) =
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath β η) := by
  change FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
    (FundamentalGroup.map f x (FundamentalGroup.fromPath η.toPath)) =
      FundamentalGroup.map f y
        (FundamentalGroup.fundamentalGroupMulEquivOfPath β (FundamentalGroup.fromPath η.toPath))
  induction η.toPath using Path.Homotopic.Quotient.ind with
  | mk p =>
    change FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.map f.continuous))) = _
    rw [b65v_path_change, b65v_path_change]
    change FundamentalGroup.fromPath _ = FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((β.symm.trans (p.trans β)).map f.continuous))
    congr 1
    congr 1
    simp only [Path.map_trans, Path.map_symm]

/-- Casting the endpoint of a transport path agrees with the specified based map.
Source: Mathlib `FundamentalGroup.mapOfEq_apply`. -/
theorem rtc_transport_mapOfEq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} {z : Y} (β : Path x y) (h : f y = z)
    (η : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
      ((β.map f.continuous).cast rfl h.symm)
      (FundamentalGroup.map f x η) =
    FundamentalGroup.mapOfEq f h (FundamentalGroup.fundamentalGroupMulEquivOfPath β η) := by
  subst z
  simpa [FundamentalGroup.mapOfEq] using rtc_transport_map f β η

/-- A common comparison path remains common after postcomposition and endpoint identification.
Source: `rtc_transport_map`; `rtc_map_comp`; Mathlib `FundamentalGroup.mapOfEq`. -/
theorem rtc_postcompose_action {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (R A : C(X, Y)) (f : C(Y, Z)) (S T : C(X, Z)) (x : X) {y : Z}
    (hS : ∀ z, S z = f (R z)) (hT : ∀ z, T z = f (A z)) (hb : T x = y)
    (β : Path (R x) (A x))
    (hβ : ∀ η : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β (FundamentalGroup.map R x η) =
        FundamentalGroup.map A x η) :
    ∃ β' : Path (S x) y, ∀ η : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath β' (FundamentalGroup.map S x η) =
        FundamentalGroup.mapOfEq T hb η := by
  have hS' : S = f.comp R := ContinuousMap.ext hS
  have hT' : T = f.comp A := ContinuousMap.ext hT
  subst S T y
  refine ⟨β.map f.continuous, fun η ↦ ?_⟩
  rw [rtc_map_comp, rtc_transport_map, hβ, ← rtc_map_comp]
  simp [FundamentalGroup.mapOfEq]

end HodgeLean.Foundations.Program
