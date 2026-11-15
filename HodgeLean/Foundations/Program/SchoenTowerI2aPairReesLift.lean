import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesGeneration
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A specified ratio over an integral affine coefficient ring factors uniquely
through the actual paired Rees chart when its denominator is nonzero.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `RingHom.liftOfSurjective` and `IsFractionRing.injective`. -/
theorem s2v_i2a_pair_rees_lift_to_domain
    (R S : Type) [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (x y : R) (t : S) (hx : φ x ≠ 0) (hy : φ y = φ x * t) :
    let I := Ideal.span {x, y}
    ∃! ψ : s2t_reesChart I x →+* S,
      ψ.comp (algebraMap R (s2t_reesChart I x)) = φ ∧
      ψ (s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩) = t := by
  classical
  intro I
  let C := s2t_reesChart I x
  let F := FractionRing S
  let incl : S →+* F := algebraMap S F
  have hinj : Function.Injective incl := IsFractionRing.injective S F
  let φF := incl.comp φ
  have hxF : φF x ≠ 0 := by
    intro h
    exact hx (hinj (h.trans incl.map_zero.symm))
  obtain ⟨ψF, hψF, hfields⟩ := s2v_i2a_rees_chart_original_field I φF x hxF
  obtain ⟨z, hz, hyz, hsur⟩ := s2t_pairChart_coordinate R x y
  have hzactual : z = s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩ :=
    Subtype.ext hz
  have hψz : ψF z = incl t := by
    rw [hzactual, s2v_i2a_reesFraction_field_value I x _ φF hxF ψF hψF]
    apply (div_eq_iff hxF).mpr
    change incl (φ y) = incl t * incl (φ x)
    rw [hy, map_mul, mul_comm]
  let q := (Polynomial.aeval (R := R) z).toRingHom
  let r := Polynomial.eval₂RingHom φ t
  have hcomp : incl.comp r = ψF.comp q := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [q, r, φF, I, Polynomial.eval₂RingHom] using (RingHom.congr_fun hψF a).symm
    · simpa [q, r, Polynomial.eval₂RingHom] using hψz.symm
  have hker : RingHom.ker q ≤ RingHom.ker r := by
    intro p hp
    apply hinj
    change incl (r p) = incl 0
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      (show q p = 0 from hp), map_zero, map_zero]
  let ψ : C →+* S := q.liftOfSurjective hsur ⟨r, hker⟩
  have hψq : ψ.comp q = r := q.liftOfSurjective_comp hsur ⟨r, hker⟩
  have hbase : ψ.comp (algebraMap R C) = φ := by
    apply RingHom.ext
    intro a
    simpa [q, r, Polynomial.eval₂RingHom] using RingHom.congr_fun hψq (Polynomial.C a)
  have hψt : ψ (s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩) = t := by
    rw [← hzactual]
    simpa [q, r, Polynomial.eval₂RingHom] using RingHom.congr_fun hψq Polynomial.X
  refine ⟨ψ, ⟨hbase, hψt⟩, ?_⟩
  intro ψ' hψ'
  have hcomp' : ψ'.comp q = r := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [q, r, Polynomial.eval₂RingHom] using RingHom.congr_fun hψ'.1 a
    · simpa [q, r, Polynomial.eval₂RingHom, hzactual] using hψ'.2
  apply RingHom.ext
  intro v
  obtain ⟨p, rfl⟩ := hsur v
  exact (RingHom.congr_fun hcomp' p).trans (RingHom.congr_fun hψq p).symm

end HodgeLean.Foundations.Program
