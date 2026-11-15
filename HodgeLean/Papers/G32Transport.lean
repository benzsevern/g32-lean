import HodgeLean.Papers.G32TransportProofs

/-! # G32 isogeny transport, first stage (FROZEN)

This specification records one direction: a `K`-linear polarized isogeny between polarized
Weil-type sixfolds carries algebraicity of Weil classes from the target to the source.  It
isolates scheme-smooth pullback, preservation of the algebraic cycle-class span, and the
one-way Weil-plane comparison.  Cup-product naturality is already available and is not
restated.  HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Papers

/-- A homomorphism of complex abelian varieties that is an isogeny on complex points is smooth.
Source: Mumford, *Abelian Varieties*, §18 (an isogeny in characteristic zero is finite étale). -/
theorem g32tr_isogeny_smooth {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X)
    [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) : Smooth f.left :=
  g32tr_isogeny_smooth_aux f hf

example {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X) [IsMonHom f]
    (hf : ccm2_IsogenyOnPoints f) : Flat f.left :=
  letI := g32tr_isogeny_smooth f hf
  inferInstance

/-- Pullback by an isogeny preserves every algebraic cycle-class span.  This is the cycle-theory
input needed in both directions of transport.
Source: Fulton, *Intersection Theory*, Ch. 1, §1.7 and Ch. 8; `ccm6_homPullback_cycleClass`. -/
theorem g32tr_isogeny_pullback_span {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X)
    [IsMonHom f] (hf : ccm2_IsogenyOnPoints f) (p : ℕ) :
    (algebraicCycleClassSpan Q.X p).map (homPullback f (2 * p)) ≤
      algebraicCycleClassSpan P.X p :=
  g32tr_isogeny_pullback_span_aux f hf p

example {P Q : g32t_Sixfold} (f : P.X ⟶ Q.X) [IsMonHom f]
    (hf : ccm2_IsogenyOnPoints f) (p : ℕ) (x : HQ Q.X (2 * p))
    (hx : x ∈ algebraicCycleClassSpan Q.X p) :
    homPullback f (2 * p) x ∈ algebraicCycleClassSpan P.X p :=
  g32tr_isogeny_pullback_span f hf p (Submodule.mem_map_of_mem hx)

/-- Weil algebraicity pulls back along a `K`-linear polarized isogeny.  The non-formal content is
that the exterior power of the `K`-linear map on `H¹` carries the Weil plane of the target onto
the Weil plane of the source; algebraic classes then pull back by
`g32tr_isogeny_pullback_span`.
Source: G32 v0.16, Lemma 2.2 (pullback direction); Fulton, *Intersection Theory*, Ch. 1 and 8. -/
theorem g32tr_weilAlg_pullback (P Q : g32t_Sixfold)
    (hP : g32t_PolarizedWeil P) (hQ : g32t_PolarizedWeil Q)
    (h : g32t_KIsog P Q) (hAlg : g32t_WeilAlg Q) : g32t_WeilAlg P :=
  g32tr_weilAlg_pullback_aux P Q hP hQ h hAlg

example (P Q : g32t_Sixfold) (hP : g32t_PolarizedWeil P)
    (hQ : g32t_PolarizedWeil Q) (h : g32t_KIsog P Q) (hAlg : g32t_WeilAlg Q) :
    g32t_WeilAlg P :=
  g32tr_weilAlg_pullback P Q hP hQ h hAlg

end HodgeLean.Papers
