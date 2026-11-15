import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeRegularPoint

/-! # Length one for regular values of the actual section parameter map

Subtracting the fibre value gives the shifted sections defining the literal
slice. Evaluation and its local derivative identify the same parameter map.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters Point Filter Topology
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem sliceLength_one_of_regular_parameter_value
    {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) (d : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (i ≫ q)).hom]
    [LocallyOfFiniteType (Over.mk (i ≫ q)).hom]
    (w j : ComplexPoint (Over.mk (i ≫ q)))
    (hwj : w ∈ (chartAt (Fin d → ℂ) j).source)
    (U : Z.Opens) (g : Fin d → Γ(Z, U)) (a : Fin d → ℂ)
    (hwU : i w.underlying ∈ U)
    (hvalue : ∀ k, evaluate (X := Over.mk q) U (g k)
      (Point.map (Over.homMk i rfl) w) = a k)
    (hunit : IsUnit (fderiv ℂ (fun v k => evaluate (X := Over.mk q) U (g k)
      (Point.map (Over.homMk i rfl) ((chartAt (Fin d → ℂ) j).symm v)))
      ((chartAt (Fin d → ℂ) j) w))) :
    a3b4a_gysin_sliceLength q i U g a w = 1 := by
  let X := Over.mk (i ≫ q)
  let f : X ⟶ Over.mk q := Over.homMk i rfl
  let e := chartAt (Fin d → ℂ) j
  let s : Fin d → Γ(K, i ⁻¹ᵁ U) :=
    fun k => i.app U (g k - a3b4a_gysin_sectionConst q U (a k))
  have heval (k : Fin d) (z : ComplexPoint X) (hz : i z.underlying ∈ U) :
      evaluate (i ⁻¹ᵁ U) (s k) z =
        evaluate (X := Over.mk q) U (g k) (Point.map f z) - a k := by
    change evaluate (i ⁻¹ᵁ U) (i.app U (g k - a3b4a_gysin_sectionConst q U (a k))) z = _
    have hmap := (Point.evaluate_map f U
      (g k - a3b4a_gysin_sectionConst q U (a k)) z).symm
    change evaluate (i ⁻¹ᵁ U) (i.app U (g k - a3b4a_gysin_sectionConst q U (a k))) z =
      evaluate (X := Over.mk q) U (g k - a3b4a_gysin_sectionConst q U (a k)) (Point.map f z) at hmap
    refine hmap.trans ?_
    rw [a3b4g_evaluate_sub,
      a3b4a_gysin_evaluate_sectionConst q U (Point.map f z) hz]
  apply sliceLength_one_of_invertible_jacobian q i d w j hwj U g a hwU
  · intro k
    rw [heval k w hwU, hvalue k, sub_self]
  · have hnear : ∀ᶠ v in 𝓝 (e w), i (e.symm v).underlying ∈ U := by
      have hopen := Point.isOpen_overOpen (X := X) (i ⁻¹ᵁ U)
      have hmem : e.symm (e w) ∈ Point.overOpen (X := X) (i ⁻¹ᵁ U) := by
        rw [e.left_inv hwj]
        exact hwU
      exact (e.continuousAt_symm (e.map_source hwj)).eventually (hopen.mem_nhds hmem)
    have heq : (fun v k => evaluate (i ⁻¹ᵁ U) (s k) (e.symm v)) =ᶠ[𝓝 (e w)]
        (fun v => (fun k => evaluate (X := Over.mk q) U (g k) (Point.map f (e.symm v))) - a) := by
      filter_upwards [hnear] with v hv
      funext k
      exact heval k (e.symm v) hv
    rw [heq.fderiv_eq, fderiv_sub_const]
    exact hunit

end AlgebraicGeometry.SingularCycles
