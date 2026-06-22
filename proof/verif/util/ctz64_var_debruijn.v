(** * verif.util.ctz64_var_debruijn: body proof for secp256k1_ctz64_var_debruijn. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/verif_modinv64_impl.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Split out from the upstream-ported verif_modinv64_impl.v (one semax_body
    per file, per the project convention). *)

Require Import secp256k1.vst.base.
Require Import secp256k1.contract.util.
Require Import secp256k1.contract.gprog.util.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.theory.modinv.divsteps.theory.
Require Import secp256k1.theory.modinv.divsteps.bound724.
Require Import secp256k1.theory.modinv.construction.inverse.
Require secp256k1.theory.modinv.construction.divstep.
Require Import secp256k1.tactics.core.
Require Import secp256k1.tactics.hygiene.

(** [secp256k1_ctz64_var_debruijn(a)] returns [Z_ctz a] via a de Bruijn sequence:
    [(a & -a)] isolates the lowest set bit, the multiply-and-shift maps it to a
    6-bit index, and the [debruijn] table translates that index to the bit position. *)
Lemma body_secp256k1_ctz64_var_debruijn: semax_body Vprog Gprog f_secp256k1_ctz64_var_debruijn spec_secp256k1_ctz64_var_debruijn.
Proof.
  start_function.

  (* ===== Setup: expose the C body and the de Bruijn lookup table ===== *)

  (* Name the 64-entry de Bruijn lookup table [l64]. *)
  unfold debruijn64_array.
  set (l64 := cons (Vint (Int.repr 0)) _).

  (* The C index (a & -a) * C >> 58 is 6 bits wide, so it subscripts the table. *)
  assert (Hctz64: 0 <= Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod 2 ^ 64) 58 < 64).
  { assert (Hm : 0 <= Z.shiftl 157587932685088877 (Z_ctz a) mod 2 ^ 64 < 2 ^ 64)
      by (apply Z.mod_pos_bound; lia).

    rewrite Z.shiftr_div_pow2 by lia.
    split.
    - (* lower: the quotient of a nonnegative dividend *)
      apply Z.div_pos; lia.
    - (* upper: 2^64 / 2^58 = 64 *)
      apply Z.div_lt_upper_bound; lia. }

  (* ===== The C index expression (a & -a) * C >> 58 equals debruijn[Z_ctz a] ===== *)

  assert_PROP (force_val
     (sem_add_ptr_long tuchar (gv _debruijn)
        (Vlong
           (Int64.shru
              (Int64.mul
                 (Int64.and (Int64.repr a)
                    (Int64.neg (Int64.repr a)))
                 (Int64.repr 157587932685088877))
              (Int64.repr 58)))) =
   field_address (tarray tuchar 64)
     [ArraySubsc (Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod (2^64)) 58)]
     (gv _debruijn)).
  { autorewrite with int_to_z.
    rewrite (Int64.unsigned_repr 58) by rep_lia.
    rewrite Int64.unsigned_repr_eq.
    change Int64.modulus with (2 ^ 64).

    entailer!.

    rewrite arr_field_address by auto.
    change (sizeof tuchar) with 1.
    rewrite Z.mul_1_l.

    destruct (Zle_lt_or_eq _ _ (proj1 H)) as [Ha0| <- ].
    - (* branch: 0 < a -- (a & -a) = 2^Z_ctz a, so the product is C << Z_ctz a *)
      rewrite Z_x_and_opp_x by lia.
      rewrite Z.shiftl_mul_pow2 by apply Z_ctz_non_neg.
      rewrite Z.mul_comm.
      reflexivity.
    - (* branch: a = 0 -- both index expressions are the same ground term *)
      reflexivity. }

  rename H0 into Haddr.

  (* [Z_ctz a] is a legal subscript too: a 64-bit input has under 64 trailing zeros. *)
  assert (Hctz : 0 <= Z_ctz a < 64).
  { split.
    - (* lower: [Z_ctz] is nonnegative *)
      apply Z_ctz_non_neg.
    - (* upper: [Z_ctz_bound] for 0 < a, and [Z_ctz 0 = 0] otherwise *)
      destruct (Zle_lt_or_eq _ _ (proj1 H)) as [Ha0| <- ].
      + apply Z_ctz_bound; rep_lia.
      + simpl.
        lia. }

  (* The table entry at that index is [Z_ctz a] -- checked over all 64 indices. *)
  assert (Hl64 :
    (@Znth val Vundef (Z.shiftr (Z.shiftl 157587932685088877 (Z_ctz a) mod 2 ^ 64) 58) l64) =
    (Vint (Int.repr (Z_ctz a)))).
  { revert Hctz.
    generalize (Z_ctz a).
    intros z [Hz Hz64].

    do 64 (apply Zle_lt_or_eq in Hz;
           destruct Hz as [Hz| <- ];
           [apply Zlt_le_succ in Hz; simpl in Hz | reflexivity]).
    lia. }

  (* ===== zeros = debruijn[(a & -a) * C >> 58] ===== *)

  (* _t'1 = debruijn[(x & -x) * C >> 58] *)
  forward.
  { (* side: the loaded table byte is a well-typed [tuchar] *)
    rewrite Hl64.
    entailer!.
    rep_lia. }

  { (* side: the subscripted lvalue is a valid pointer *)
    entailer!.
    rewrite Haddr.
    apply field_address_isptr.
    apply arr_field_compatible; auto. }

  (* ===== Postcondition: the returned byte is Vint (Int.repr (Z_ctz a)) ===== *)

  (* return _t'1 *)
  forward.
  fold l64.
  rewrite Hl64.
  entailer!.
Qed.
