import HodgeLean.Foundations.BundleThom.RelativeFinsetSuccessorCoclassGluingHelpers

/-! # Finite relative gluing in a supplied positive degree

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Compatible relative coclasses in a positive degree glue on a finite family when every finite intersection vanishes in all lower degrees.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris. -/
theorem i1_relativeSubcomplexFinsetPositiveCoclass_gluing {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (N : ℕ) (hN : 0 < N) (U : ι → X.Subcomplex)
    (w : ∀ i, ((i1_relativeSubcomplexChainFunctor X Z).obj (U i)).linearDualCochainComplex.homology N)
    (s : Finset ι) (hs : s.Nonempty)
    (hh : ∀ t : Finset ι, t.Nonempty → ∀ m, m < N →
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (t.inf U)).homology m))
    (hc : ∀ i ∈ s, ∀ j ∈ s, i1_chainDualPullback N
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))) (w i) =
      i1_chainDualPullback N
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))) (w j)) :
    ∃ z : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology N,
      ∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U),
        i1_chainDualPullback N ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) z = w i := by
  cases N with
  | zero => omega
  | succ n =>
    exact i1_relativeSubcomplexFinsetSuccessorCoclass_gluing X Z n U w s hs
      (fun t ht m hm => hh t ht m (by omega)) hc

/-- Finite restrictions detect positive-degree relative coclasses when all actual finite intersections vanish in lower degrees.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, finite relative Mayer–Vietoris detection. -/
theorem i1_relativeSubcomplexFinsetPositiveCoclass_ext {ι : Type}
    (X : SSet) (Z : X.Subcomplex) (N : ℕ) (hN : 0 < N) (U : ι → X.Subcomplex)
    (s : Finset ι) (hs : s.Nonempty)
    (hh : ∀ t : Finset ι, t.Nonempty → ∀ m, m < N →
      IsZero (((i1_relativeSubcomplexChainFunctor X Z).obj (t.inf U)).homology m))
    (u v : ((i1_relativeSubcomplexChainFunctor X Z).obj (s.sup U)).linearDualCochainComplex.homology N)
    (hr : ∀ (i : ι) (_ : i ∈ s) (hUi : U i ≤ s.sup U), i1_chainDualPullback N
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) u =
      i1_chainDualPullback N
        ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE hUi)) v) : u = v := by
  cases N with
  | zero => omega
  | succ n =>
    exact i1_relativeSubcomplexFinsetSuccessorCoclass_ext X Z n U s hs
      (fun t ht m hm => hh t ht m (by omega)) u v hr

end HodgeLean.Foundations.BundleThom
