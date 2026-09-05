(** * model.tests_slow_group: seconds-scale known-answer checks for [model.group]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The [model/tests_group.v] checks that cost more than one field inversion
    ([fe_inv]/[fe_sqrt], each about 6 seconds under [vm_compute] on the
    reference machine -- see that file's header) each: small multiples of
    [G] (two to three [padd]/[pdouble] calls apiece) and the [lift_x_even]
    round trip (one [fe_sqrt]). Deliberately NOT in [_RocqProject].
    VST-free, no axioms. *)

From Stdlib Require Import ZArith.

Require Import secp256k1.model.constants.
Require Import secp256k1.model.group.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Small multiples of [G] -- cross-checked against an independent
    implementation (Python's [cryptography] library, OpenSSL-backed EC point
    multiplication on SECP256K1, itself cross-checked against a from-scratch
    Python double-and-add / Fermat-inverse implementation over the same SEC2
    parameters).  [2*G]'s x coordinate also matches the widely published
    secp256k1 test vector for private key 2 (compressed pubkey
    [02c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5]). *)

(** [2*G] -- one [pdouble], one [fe_inv]. *)
Lemma chk_smul_2G :
  point_coords (smul 2 G)
  = Some (89565891926547004231252920425935692360644145829622209833684329913297188986597,
          12158399299693830322967808612713398636155367887041628176798871954788371653930).
Proof. vm_compute. reflexivity. Qed.

(** [3*G] -- one [pdouble] plus [padd]'s generic chord case, two [fe_inv]. *)
Lemma chk_smul_3G :
  point_coords (smul 3 G)
  = Some (112711660439710606056748659173929673102114977341539408544630613555209775888121,
          25583027980570883691656905877401976406448868254816295069919888960541586679410).
Proof. vm_compute. reflexivity. Qed.

(** [4*G] -- two nested [pdouble] calls, two [fe_inv]. *)
Lemma chk_smul_4G :
  point_coords (smul 4 G)
  = Some (103388573995635080359749164254216598308788835304023601477803095234286494993683,
          37057141145242123013015316630864329550140216928701153669873286428255828810018).
Proof. vm_compute. reflexivity. Qed.

(** [padd] agrees with [pdouble] on equal arguments: the tangent/chord
    identity [model.group]'s [padd] documents (equal-x, equal-y delegates to
    [pdouble]).  Compared via [point_eqb] (see [model/tests_group.v]'s
    [chk_pneg_involution] for why raw [=] does not [vm_compute]-convert
    across two independently-computed [Fe] range proofs).  Two independent
    [fe_inv] evaluations (one per side of the equation), not one --
    [vm_compute] does not share work between the two sides of an equality
    goal. *)
Lemma chk_padd_double_agree : point_eqb (padd G G) (pdouble G) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(** ** [lift_x_even] / [has_even_y] round trip -- [model.bip340]'s
    [xonly_parse] / [xonly_serialize] are built from exactly this pair. *)

(** Extracting the x coordinate of [pneg G] is literally [fe_G_x]: [pneg]
    only negates y ([model.group]'s [pneg] definition), so this holds by
    plain reduction, no [fe_inv]/[fe_sqrt] involved.  This is the "on
    [pneg G]" half of the round trip below: since the x coordinate [pneg G]
    contributes is the SAME term as [G]'s, a second [lift_x_even] call on it
    would be the identical (already 6-7 second) computation
    [chk_liftx_even_G] performs, so it is not duplicated as a second
    [vm_compute] here. *)
Lemma chk_negG_x_is_Gx :
  match pneg G with
  | PAff x _ => x
  | PInf => fe_G_x
  end = fe_G_x.
Proof. reflexivity. Qed.

(** [lift_x_even] of [G]'s x coordinate reproduces [G] -- the one [fe_sqrt]
    call in this file.  Combined with [chk_negG_x_is_Gx], this also answers
    the round trip starting from [pneg G]: lifting the x coordinate either
    point contributes returns the even-y representative [G], regardless of
    which point's y parity started the computation. *)
Lemma chk_liftx_even_G :
  match lift_x_even fe_G_x with
  | Some p => point_eqb p G
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
