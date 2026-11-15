import HodgeLean.Foundations.Program.G32Native.PairedC3EtaleNodeSequence
import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleBinomialChart

/-! # Regular total-transform equations in a supplied binomial chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open RingTheory.Sequence Polynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- On a Rees chart of two étale coordinates, the pullback of a slice cut
by one centre coordinate and distinct transverse coordinates is weakly
regular, in the original chart quotient ring.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8;
Matsumura, Commutative Ring Theory, §16. -/
theorem paired_c3_binomial_total_sequence
    {k R σ : Type u} [CommRing k] [CommRing R] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    (a b : σ) (hab : a ≠ b) (l : List σ) (hl : l.Nodup)
    (ha : a ∉ l) (hb : b ∉ l) :
    let f := algebraMap (MvPolynomial σ k) R
    let Q := s2v_L1bChart (f (MvPolynomial.X a)) (f (MvPolynomial.X b))
    let q := Ideal.Quotient.mk (Ideal.span
      {C (f (MvPolynomial.X a)) - X * C (f (MvPolynomial.X b))})
    IsWeaklyRegular Q
      (l.map (fun j => q (C (f (MvPolynomial.X j)))) ++
        [q (C (f (MvPolynomial.X a)))]) := by
  dsimp only
  let f := algebraMap (MvPolynomial σ k) R
  let Q := s2v_L1bChart (f (MvPolynomial.X a)) (f (MvPolynomial.X b))
  let q := Ideal.Quotient.mk (Ideal.span
    {C (f (MvPolynomial.X a)) - X * C (f (MvPolynomial.X b))})
  obtain ⟨z, het, hz⟩ := s2v_l1b_etale_binomial_chart (k := k) (R := R) a b hab
  have hnode := paired_c3_etale_node_sequence
    ((q.comp C).comp (f.comp MvPolynomial.C)) z het l hl a b ha hb
  have hlist : l.map (fun j => q (C (f (MvPolynomial.X j)))) = l.map z := by
    apply List.map_congr_left
    intro j hj
    have hja : j ≠ a := by rintro rfl; exact ha hj
    simpa only [if_neg hja] using hz j
  rw [hlist]
  have hqa : q (C (f (MvPolynomial.X a))) = z a * z b := by
    have h := hz a
    rw [if_pos rfl] at h
    exact h
  rw [hqa]
  exact hnode

#print axioms paired_c3_binomial_total_sequence
end HodgeLean.Foundations.Program.G32Native
