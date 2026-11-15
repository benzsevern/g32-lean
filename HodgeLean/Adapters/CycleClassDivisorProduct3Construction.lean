import HodgeLean.Adapters.CycleClassDivisorProduct3Proofs

/-! # Relative cup on cohomology
The construction uses the explicit cycle and boundary obligations in the proof module.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Adapters

/-- Inverse cohomology comparison from small relative cochains to genuine relative cohomology.
Source: Spanier, Algebraic Topology, chapter 5, exact duality over a field and excision. -/
def ccm15_dualTransport (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) (n : ℕ) :
    (ccm15_smallDual Y S T n).homology ≃ₗ[ℚ]
      RelativeCohomology ℚ (TopPair.ofSubset (S ∩ T)ᶜ) n := by
  letI := ccm15_dualComparison_quasiIso_aux Y S T hS hT
  exact (ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso
      (ccm14_smallRelativeComplex Y S T) n)).toLinearEquiv.symm.trans
    (asIso (HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) n)).toLinearEquiv.symm

/-- The descended product of explicit cycles.
Source: Hatcher, Algebraic Topology, §3.2, cocycle cup product. -/
def ccm15_cycleCup (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) :
    LinearMap.ker (ccm15_relativeDual Y S p).g.hom →ₗ[ℚ]
      LinearMap.ker (ccm15_relativeDual Y T q).g.hom →ₗ[ℚ]
        LinearMap.ker (ccm15_smallDual Y S T (p + q)).g.hom where
  toFun u :=
    { toFun := fun v => ⟨ccm15_smallCupLinear Y S T p q u.1 v.1,
        ccm15_smallCup_closed_aux Y S T p q u v⟩
      map_add' := fun v w => Subtype.ext (map_add _ v.1 w.1)
      map_smul' := fun a v => Subtype.ext (map_smul _ a v.1) }
  map_add' u v := by
    ext w : 1
    exact Subtype.ext (LinearMap.congr_fun (map_add (ccm15_smallCupLinear Y S T p q) u.1 v.1) w.1)
  map_smul' a u := by
    ext v : 1
    exact Subtype.ext (LinearMap.congr_fun (map_smul (ccm15_smallCupLinear Y S T p q) a u.1) v.1)

/-- Product of cycles followed by the target quotient by boundaries.
Source: Hatcher, Algebraic Topology, §3.2, descent modulo coboundaries. -/
def ccm15_cycleCupClass (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) :=
  (ccm15_cycleCup Y S T p q).compr₂
    ((LinearMap.range (ccm15_smallDual Y S T (p + q)).moduleCatToCycles).mkQ)

private theorem ccm15_boundary_class_zero (Y : TopCat.{0}) (S T : Set Y) (n : ℕ)
    (w : LinearMap.ker (ccm15_smallDual Y S T n).g.hom)
    (h : w.1 ∈ LinearMap.range (ccm15_smallDual Y S T n).f.hom) :
    (LinearMap.range (ccm15_smallDual Y S T n).moduleCatToCycles).mkQ w = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  obtain ⟨a, ha⟩ := h
  exact ⟨a, Subtype.ext ha⟩

/-- Cup product on the actual quotients of cycles by boundaries.
Source: Hatcher, Algebraic Topology, §3.2, well-defined relative cup product. -/
def ccm15_quotientCup (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ) :=
  LinearMap.liftQ₂
    (LinearMap.range (ccm15_relativeDual Y S p).moduleCatToCycles)
    (LinearMap.range (ccm15_relativeDual Y T q).moduleCatToCycles)
    (ccm15_cycleCupClass Y S T p q)
    (by
      rintro _ ⟨a, rfl⟩
      apply LinearMap.ext
      intro v
      exact ccm15_boundary_class_zero Y S T (p + q) _
        (ccm15_smallCup_boundary_left_aux Y S T p q a v))
    (by
      rintro _ ⟨b, rfl⟩
      apply LinearMap.ext
      intro u
      exact ccm15_boundary_class_zero Y S T (p + q) _
        (ccm15_smallCup_boundary_right_aux Y S T p q u b))

/-- Relative cup with intersection support, obtained by quotient descent and inverse excision.
Source: Hatcher, Algebraic Topology, §3.2; Bredon, Topology and Geometry, VI.4. -/
def ccm15_relativeCup (Y : TopCat.{0}) (S T : TopologicalSpace.Closeds Y) (p q : ℕ) :
    RelativeCohomology ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p →ₗ[ℚ]
      RelativeCohomology ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q →ₗ[ℚ]
        RelativeCohomology ℚ (TopPair.ofSubset ((S ⊓ T : TopologicalSpace.Closeds Y) : Set Y)ᶜ)
          (p + q) :=
  let eS := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (S : Set Y)ᶜ) p).symm.toLinearMap
  let eT := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (T : Set Y)ᶜ) q).symm.toLinearMap
  let iS := (ccm15_relativeDual Y S p).moduleCatHomologyIso.hom.hom.comp eS
  let iT := (ccm15_relativeDual Y T q).moduleCatHomologyIso.hom.hom.comp eT
  let o := (ccm15_dualTransport Y S T S.isClosed T.isClosed (p + q)).toLinearMap.comp
    (ccm15_smallDual Y S T (p + q)).moduleCatHomologyIso.inv.hom
  ((ccm15_quotientCup Y S T p q).compl₁₂ iS iT).compr₂ o

/-- Source: degree-zero full-support product accepts actual relative cohomology classes. -/
example : ccm15_relativeCup (TopCat.of PUnit) ⊤ ⊤ 0 0 0 0 = 0 := by
  exact map_zero _

end HodgeLean.Adapters
