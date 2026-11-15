import HodgeLean.Foundations.Curves.CurveDivisorsDefs
import HodgeLean.Foundations.Curves.CubicDivisor
import HodgeLean.Foundations.Curves.CurveDegree

/-! # Proof obligations for the frozen curve-divisor spec -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace HodgeLean.Foundations.Curves

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left]
  [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
  [IsLocallyNoetherian X.left] [CompactSpace X.left]

/-- A divisor on a projective curve has finite support. -/
theorem divisor_support_finite_aux (D : Divisor X.left) :
    (Function.support (D : X.left → ℤ)).Finite := by
  exact D.1.finite_support

/-- The orders of a nonzero rational function on a smooth projective curve have finite support. -/
theorem ord_support_finite_aux (f : X.left.functionField) (hf : f ≠ 0) :
    (Function.support (ordAt X.left f)).Finite := by
  letI : IsNoetherian X.left :=
   {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance
   }
  obtain ⟨U, _, g, hU, hfg, hg⟩ := exists_isUnit_germ_eq X.left f hf
  let p : Set X.left := (U : Set X.left)ᶜ
  have hsub : Function.support (ordAt X.left f) ⊆ p := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hxU : x ∉ U := by
      intro hxU
      apply hx
      rw [← hfg]
      exact Scheme.ord_of_isUnit hg hxU
    exact hxU
  have hpclosed : IsClosed p := by
    exact U.isOpen.isClosed_compl
  letI : QuasiSober p := Topology.IsClosedEmbedding.quasiSober
    hpclosed.isClosedEmbedding_subtypeVal
  have hclosure : closure p ≠ Set.univ := by
    intro h
    let y : X.left := hU.some.1
    have hyU : y ∈ (U : X.left.Opens) := by simpa [y] using hU.some.2
    have hu : y ∈ p := by
      rw [← hpclosed.closure_eq, h]
      exact Set.mem_univ _
    have hnot : y ∉ p := by simpa [p] using hyU
    exact hnot hu
  have hfinite := TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    (X := X.left) (p := p) hclosure
  refine hfinite.subset ?_
  intro x hx
  have hx' : x ∈ p := hsub hx
  have hcoh : Order.coheight x = 1 := by
    by_contra hn
    exact hx (Scheme.ord_eq_zero_of_coheight_neq_one hn f)
  exact ⟨hx', hcoh⟩

/-- The principal divisor has the expected coefficient at every point. -/
theorem principalDivisor_apply_aux (f : X.left.functionField) (hf : f ≠ 0) (P : X.left) :
    (principalDivisor X.left f).1 P = ordAt X.left f P := by
  rw [principalDivisor, dite_eq_left (ord_support_finite_aux f hf)]
  rfl

/-- Principal divisors turn multiplication into addition. -/
theorem principalDivisor_mul_aux (f g : X.left.functionField) (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor X.left (f * g) = principalDivisor X.left f + principalDivisor X.left g := by
  ext P
  simp only [principalDivisor, dite_eq_left (ord_support_finite_aux f hf),
    dite_eq_left (ord_support_finite_aux g hg),
    dite_eq_left (ord_support_finite_aux (f * g) (mul_ne_zero hf hg))]
  change ordAt X.left (f * g) P = ordAt X.left f P + ordAt X.left g P
  exact Scheme.ord_mul hf hg

/-- A nonzero constant rational function has zero divisor. -/
theorem principalDivisor_constant_aux (c : ℂ) (hc : c ≠ 0) :
    principalDivisor X.left (constantFunction X c) = 0 := by
  have hord : ∀ P : X.left, ordAt X.left (constantFunction X c) P = 0 := by
    intro P
    letI : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
    let s : Γ(X.left, ⊤) := X.hom.appTop ((Scheme.ΓSpecIso ↧ℂ).inv c)
    have hs : IsUnit s := by
      apply IsUnit.map X.hom.appTop.hom
      exact IsUnit.map (Scheme.ΓSpecIso ↧ℂ).inv.hom (isUnit_iff_ne_zero.mpr hc)
    have htop : P ∈ (⊤ : X.left.Opens) := trivial
    change X.left.ord (X.left.germToFunctionField ⊤ s) P = 0
    exact Scheme.ord_of_isUnit hs htop
  have hfin : (Function.support (ordAt X.left (constantFunction X c))).Finite := by
    have hempty : Function.support (ordAt X.left (constantFunction X c)) = ∅ := by
      ext P
      simp [Function.mem_support, hord P]
    rw [hempty]
    exact Set.finite_empty
  ext P
  simp only [principalDivisor, dite_eq_left hfin]
  exact hord P

/-- On the fixed cubic, `x` has a double zero at `(0,0)` and a double pole at infinity. -/
theorem cubicX_principalDivisor_aux :
    (principalDivisor E.left cubicX : AlgebraicCycle E.left ℤ) =
      2 • pointCycle E.left (finitePoint.base default) 1 -
        2 • pointCycle E.left (infinity.base default) 1 := by
  ext P
  rw [principalDivisor_apply_aux (X := E) cubicX CubicDivisor.cubicX_ne_zero P]
  change E.left.ord cubicX P = _
  rw [CubicDivisor.ord_cubicX]
  classical
  simp only [pointCycle, Function.locallyFinsuppWithin.coe_sub,
    Function.locallyFinsuppWithin.coe_nsmul, Pi.sub_apply, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply]
  have hne := CubicDivisor.finitePoint_ne_infinity
  split_ifs with h1 h2 h2 <;> simp_all

end HodgeLean.Foundations.Curves
