import HodgeLean.Foundations.Program.SchoenFiniteSchemeProductMaps
import HodgeLean.Foundations.SegreProjectiveProofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual ordered power of integral projective space for the finite-factor Segre construction. -/
abbrev s2_segrePower (d n : ℕ) : Scheme.{0} :=
  s2_schemeProduct n (fun _ => g3c_P d)

/-- The actual affine product chart selected by a tuple of projective coordinates. -/
abbrev s2_segrePowerChart (d n : ℕ) (a : Fin n → Fin (d + 1)) : Scheme.{0} :=
  s2_schemeProduct n (fun i =>
    Spec (.of (Away (UniversalGrading d) (X (a i) : UniversalRing d))))

/-- The coordinatewise actual chart immersion into the finite projective-space power. -/
def s2_segrePowerChartι (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    s2_segrePowerChart d n a ⟶ s2_segrePower d n :=
  s2_schemeProductMap n _ _ (fun i => g3c_chartι d (a i))

/-- Each actual tuple chart of the finite projective-space power is affine. -/
instance s2_segrePowerChart_isAffine (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    IsAffine (s2_segrePowerChart d n a) := s2_schemeProduct_isAffine n _

/-- The actual tuple-chart morphisms are scheme open immersions. -/
instance s2_segrePowerChartι_isOpenImmersion (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    IsOpenImmersion (s2_segrePowerChartι d n a) := s2_schemeProductMap_isOpenImmersion n _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual affine tuple charts cover every scheme point of the finite projective-space power. -/
theorem s2_segrePowerChart_covers (d n : ℕ) (x : s2_segrePower d n) :
    ∃ a : Fin n → Fin (d + 1), x ∈ Set.range (s2_segrePowerChartι d n a) := by
  induction n with
  | zero => exact ⟨Fin.elim0, x, rfl⟩
  | succ n ih =>
    let f := terminal.from (g3c_P d)
    let g := terminal.from (s2_segrePower d n)
    obtain ⟨i, hi⟩ := g3c_chartι_covers d ((pullback.fst f g) x)
    obtain ⟨a, ha⟩ := ih ((pullback.snd f g) x)
    refine ⟨Fin.cons i a, ?_⟩
    change (x : (pullback f g : Scheme)) ∈ Set.range (pullback.map
      (terminal.from (Spec (.of (Away (UniversalGrading d) (X i : UniversalRing d)))))
      (terminal.from (s2_segrePowerChart d n a)) f g
      (g3c_chartι d i) (s2_segrePowerChartι d n a) (𝟙 (terminal Scheme))
      (terminal.hom_ext _ _) (terminal.hom_ext _ _))
    rw [Scheme.Pullback.range_map]
    exact ⟨hi, ha⟩

/-- The actual affine open cover of a finite integral projective-space power by tuple charts. -/
def s2_segrePowerCover (d n : ℕ) : (s2_segrePower d n).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin n → Fin (d + 1)) (s2_segrePowerChart d n)
    (s2_segrePowerChartι d n) (s2_segrePowerChart_covers d n)

end HodgeLean.Foundations.Program
