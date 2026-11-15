module

public import HodgeLean.Foundations.Program.SchoenCycleS2Proofs

/-! # S2 affine residue intersection infrastructure
Implication from distinct coordinate equations to their actual quotient ring.
This is the first affine piece; projective gluing, conormal sheaves and tower
compatibility are separate review units. HC no distance; AV milestone no distance.
-/
public section

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program
/-- The residue chart equations retain their full ideal, including multiplicity.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(iv,vi),
printed pp. 13–14; Lemma 2.4 proof, printed p. 15.
This is the polynomial chart calculation, before identification with the slice. -/
theorem s2e_chain_residue_coordinate_kernel
    (n : ℕ) (T : Finset (Fin n)) :
    RingHom.ker (MvPolynomial.killCompl
      (R := ℂ) (f := fun i : {i : Fin n // i ∉ T} => i.val)
      Subtype.val_injective).toRingHom =
      Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n))) :=
  s2e_chain_residue_coordinate_kernel_aux n T

example := @s2e_chain_residue_coordinate_kernel

/-- The affine intersection has precisely the remaining polynomial coordinates.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(vi),
printed pp. 13–14; Lemma 2.4 proof, printed p. 15.
This is an affine coordinate-ring assertion, without projective gluing. -/
theorem s2e_chain_residue_coordinate_quotient
    (n : ℕ) (T : Finset (Fin n)) :
    ∃ e : (MvPolynomial (Fin n) ℂ ⧸
        Ideal.span ((MvPolynomial.X (R := ℂ)) '' (↑T : Set (Fin n)))) ≃ₐ[ℂ]
          MvPolynomial {i : Fin n // i ∉ T} ℂ,
      ∀ p, e (Ideal.Quotient.mk _ p) =
        MvPolynomial.killCompl (R := ℂ)
          (f := fun i : {i : Fin n // i ∉ T} => i.val) Subtype.val_injective p :=
  s2e_chain_residue_coordinate_quotient_aux n T

example := @s2e_chain_residue_coordinate_quotient

end HodgeLean.Foundations.Program
