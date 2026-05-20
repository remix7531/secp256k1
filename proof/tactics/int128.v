(** * tactics.int128: forward_call wrappers for the int128 helpers. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** One [forward_call_*] wrapper per u128/i128 helper, bundling the call with
    the [Intros] / [rename] / [deadvars!] boilerplate (see [tactics.core] for
    the shared automation), plus [mul_set], the manual set rule the signed
    [mul128] partial products need. *)

Require Export secp256k1.tactics.core.
Require Import secp256k1.contract.helper.repr.

(** u128 helpers. *)

Ltac forward_call_u128_mul r_ptr a b sh r Hr :=
  forward_call (r_ptr, a, b, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_from_u64 r_ptr a sh r Hr :=
  forward_call (r_ptr, a, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_accum_u64 r_ptr r a sh r' Hr' :=
  forward_call (r_ptr, r, a, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_accum_mul r_ptr r a b sh r' Hr' :=
  forward_call (r_ptr, r, a, b, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_to_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_hi_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_rshift r_ptr r sh r' Hr' :=
  forward_call (r_ptr, r, 64, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

(** umul128: compute a*b, return lo, write hi to *hi_ptr. *)

Ltac forward_call_umul128 a b hi_ptr sh result Hresult :=
  forward_call (a, b, hi_ptr, sh);
  [.. | Intros result; rename H into Hresult; try deadvars!].

(* ----------------------------------------------------------------- *)
(** *** Manual set for a signed-shift multiplicand -- [mul_set].

    Plain [forward] diverges on the [hl]/[hh] assignments, where a signed
    arithmetic shift [(a >> 32)] is the LEFT operand of [*]: VST's automatic
    [tc_expr] reduction loops on the [tc_nobinover] no-signed-overflow check
    (the [lh] case, with the cast on the left, is handled fine by plain
    [forward]).  This tactic runs the set rule [semax_SC_set] by hand and
    discharges the [tc_expr] obligation WITHOUT [entailer!] (which would also
    loop on this expression shape): it reduces [tc_expr] to its [tc_nobinover]
    + [tc_initialized] conjuncts, evaluates the operands against the [temp _a]
    / [temp _b] LOCALs, reduces the shift/cast operations with a targeted
    [cbn], and closes the no-overflow conjunct with [ovf_lemma] (stated in the
    post-[cbn] shape).  The two [tc_initialized] conjuncts are the [is_long]
    facts, read off from the [temp] LOCALs.  The trailing
    [simpl remove_localdef_temp] re-normalises the LOCAL list so a following
    [mul_set] / [forward] sees a clean [LOCALx]. *)
Ltac mul_set ovf_lemma :=
  eapply semax_seq';
  [ hoist_later_in_pre;
    eapply semax_SC_set;
    [ reflexivity
    | reflexivity
    | entailer!
    | unfold tc_expr;
      simpl typecheck_expr;
      simpl denote_tc_assert;
      go_lowerx;
      super_unfold_lift;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      unfold int64_to_val in *;
      repeat match goal with
      | Heq : Vlong _ = eval_id ?i ?rho |- _ => rewrite <- Heq
      end;
      cbn [force_val sem_shift_li sem_cast_l2i];
      repeat apply andp_right;
      [ apply prop_right;
        apply ovf_lemma; rep_lia
      | apply prop_right;
        match goal with
        | Heq : Vlong _ = eval_id ?i ?rho |- context [Map.get (te_of ?rho) ?i] =>
            unfold eval_id in Heq;
            destruct (Map.get (te_of rho) i) as [vv|];
            [ exists vv; split; [reflexivity | simpl in Heq; rewrite <- Heq; exact I]
            | simpl in Heq; discriminate ]
        end
      | apply prop_right;
        match goal with
        | Heq : Vlong _ = eval_id ?i ?rho |- context [Map.get (te_of ?rho) ?i] =>
            unfold eval_id in Heq;
            destruct (Map.get (te_of rho) i) as [vv|];
            [ exists vv; split; [reflexivity | simpl in Heq; rewrite <- Heq; exact I]
            | simpl in Heq; discriminate ]
        end ] ]
  | abbreviate_semax; simpl remove_localdef_temp ].
