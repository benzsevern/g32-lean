import HodgeLean.Foundations.Program.G32Native.ConormalPointClassSpan
import HodgeLean.Foundations.Program.G32Native.SmoothConormalPointFrame

/-! # Point bases supplied by actual local ideal equations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- A finite-dimensional spanning family contains a basis with the prescribed
finite index. The basis vectors retain their actual indices in that family. -/
theorem exists_fin_basis_in_spanning_family {M S : Type*}
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (v : S → M) (k : ℕ) (hk : Module.finrank ℂ M = k)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    ∃ (s : Fin k → S) (b : Module.Basis (Fin k) ℂ M), ∀ j, b j = v (s j) := by
  classical
  let J : Set M := (linearIndepOn_empty ℂ (id : M → M)).extend (Set.empty_subset (Set.range v))
  let b : Module.Basis J ℂ M := Module.Basis.ofSpan (show ⊤ ≤ Submodule.span ℂ (Set.range v) by rw [hv])
  letI : Finite J := Module.Finite.finite_basis b
  letI : Fintype J := Fintype.ofFinite J
  have hcard : Fintype.card J = k := (Module.finrank_eq_card_basis b).symm.trans hk
  let e : J ≃ Fin k := (Fintype.equivFin J).trans (finCongr hcard)
  have hb : ∀ j : Fin k, ∃ s : S, v s = (b.reindex e) j := by
    intro j
    have hm : b (e.symm j) ∈ Set.range v :=
      Module.Basis.ofSpan_subset
        (show ⊤ ≤ Submodule.span ℂ (Set.range v) by rw [hv])
        (Set.mem_range_self (e.symm j))
    rcases hm with ⟨s, hs⟩
    exact ⟨s, hs.trans (Module.Basis.reindex_apply b e j).symm⟩
  choose s hs using hb
  exact ⟨s, b.reindex e, fun j => (hs j).symm⟩

/-- On every containing affine ambient open, actual ideal equations supply a
basis of the smooth conormal point fibre with its expected finite index. -/
theorem conormalLocalClasses_exists_fin_basis {Q W : Over (Spec ↧ℂ)}
    (n k : ℕ) [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) :
    ∃ (s : Fin k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)))
      (b : Module.Basis (Fin k) ℂ
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
          ((Scheme.Modules.pullback x.left).obj (Conormal.sheaf i.left)))),
      ∀ j, b j = conormalLocalClass i U (s j) x hx := by
  let e := smoothConormalPointFrameEquiv Q W n k i x
  letI := FiniteDimensional.of_injective e.toLinearMap e.injective
  apply exists_fin_basis_in_spanning_family
    (fun s => conormalLocalClass i U s x hx) k
  · exact e.finrank_eq.trans (Module.finrank_fin_fun (n := k) ℂ)
  · exact conormalLocalClasses_span i (n + k) x U hU hx

#print axioms exists_fin_basis_in_spanning_family
#print axioms conormalLocalClasses_exists_fin_basis

/-- Actual local ideal equations supply finite dual coordinates at the point;
each coordinate is evaluation on the corresponding original equation class. -/
theorem conormalLocalClasses_exists_dual_coordinates {Q W : Over (Spec ↧ℂ)}
    (n k : ℕ) [SmoothOfRelativeDimension n Q.hom]
    [SmoothOfRelativeDimension (n + k) W.hom]
    (i : Q ⟶ W) [IsClosedImmersion i.left]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) :
    ∃ (s : Fin k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left)))
      (e : normalFibreOfModule (Conormal.sheaf i.left) x ≃ₗ[ℂ] (Fin k → ℂ)),
      ∀ ν j, e ν j = ν (conormalLocalClass i U (s j) x hx) := by
  obtain ⟨s, b, hb⟩ := conormalLocalClasses_exists_fin_basis n k i x U hU hx
  refine ⟨s, b.dualBasis.equivFun, ?_⟩
  intro ν j
  exact (Module.Basis.dualBasis_equivFun b ν j).trans (congrArg ν (hb j))

#print axioms conormalLocalClasses_exists_dual_coordinates

end HodgeLean.Foundations.Program.G32Native
