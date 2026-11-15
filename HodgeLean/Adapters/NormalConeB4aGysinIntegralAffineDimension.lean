import HodgeLean.Adapters.NormalConeB4aClassComponentDimension

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The dimension of a nonempty integral affine region of a finite type complex
scheme is the intrinsic coheight of each of its globally closed points. -/
theorem a3b4a_gysin_integral_affine_closed_point_dimension
    (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : IsAffineOpen U)
    (z : X.left) (hzU : z ∈ U) (hz : IsClosed {z}) :
    ringKrullDim Γ(X.left, U) = (↑(Order.coheight z) : WithBot ℕ∞) := by
  letI : Nonempty U := ⟨⟨z, hzU⟩⟩
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  letI : Algebra.FiniteType ℂ Γ(X.left, U) := by
    rw [← RingHom.finiteType_algebraMap]
    change (algebraMap ℂ Γ(X.left, U)).FiniteType
    apply (X.hom.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hU
      (by simp)).comp
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective
  let P : Ideal Γ(X.left, U) := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
  haveI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨z, hzU⟩ hz
  have hP := Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal (k := ℂ) P
  have hheight : P.height = Order.coheight z := by
    have hp := hU.primeIdealOf_height_eq_coheight (⟨z, hzU⟩ : U.toScheme)
    have ho := coheight_eq_of_isOpenImmersion (x := (⟨z, hzU⟩ : U.toScheme)) U.ι
    exact hp.trans ho.symm
  rw [hheight] at hP
  exact hP.symm

/-- Nonempty affine opens in an integral finite type complex scheme have the
same ring dimension, without an affine or smooth assumption on the scheme. -/
theorem a3b4a_gysin_integral_affine_dimensions_eq
    (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (U V : X.left.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) [Nonempty U] [Nonempty V] :
    ringKrullDim Γ(X.left, U) = ringKrullDim Γ(X.left, V) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hgU : genericPoint X.left ∈ U :=
    ((genericPoint_spec X.left).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hgV : genericPoint X.left ∈ V :=
    ((genericPoint_spec X.left).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  obtain ⟨z, ⟨hzU, hzV⟩, hz⟩ := nonempty_inter_closedPoints
    (Z := (U : Set X.left) ∩ V) ⟨genericPoint X.left, hgU, hgV⟩
    (U.isOpen.inter V.isOpen).isLocallyClosed
  exact (a3b4a_gysin_integral_affine_closed_point_dimension X U hU z hzU hz).trans
    (a3b4a_gysin_integral_affine_closed_point_dimension X V hV z hzV hz).symm

/-- One nonempty affine region bounds the dimension of an entire integral
finite type complex scheme. -/
theorem a3b4a_gysin_integral_dimension_bound_of_affine
    (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (D : ℕ) (hD : ringKrullDim Γ(X.left, U) ≤ (D : ℕ)) :
    topologicalKrullDim X.left ≤ (D : ℕ) := by
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X.left) (U := ⊤) (x := x) (by simp)
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hco : P.height = Order.coheight x := by
    have hp := hV.primeIdealOf_height_eq_coheight (⟨x, hxV⟩ : V.toScheme)
    have ho := coheight_eq_of_isOpenImmersion (x := (⟨x, hxV⟩ : V.toScheme)) V.ι
    exact hp.trans ho.symm
  calc
    (↑(Order.coheight x) : WithBot ℕ∞) = ↑P.height := congrArg _ hco.symm
    _ ≤ ringKrullDim Γ(X.left, V) := Ideal.height_le_ringKrullDim_of_isPrime
    _ = ringKrullDim Γ(X.left, U) := a3b4a_gysin_integral_affine_dimensions_eq X V U hV hU
    _ ≤ D := hD

end HodgeLean.Adapters
