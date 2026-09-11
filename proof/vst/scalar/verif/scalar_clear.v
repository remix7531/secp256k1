(** * vst.scalar.verif.scalar_clear: Proof of body_secp256k1_scalar_clear. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_scalar.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.gprog.
Require Import secp256k1.vst.tactics.core.
Require Import secp256k1.vst.tactics.int128.
Require Import secp256k1.vst.tactics.scalar.

(* ================================================================= *)
(** ** secp256k1_scalar_clear -- [*r = 0]. *)

(** The body is now a plain [memclear] call: under [SECP256K1_NO_LIBC]
    the zeroing lowers to a pure-C byte loop (no [EF_vstore] / [EF_vload]
    volatile builtins), so VST executes it via the [memclear_explicit]
    funspec.  That funspec yields a zeroed byte array
    [data_at sh (tarray tuchar 32) (Zrepeat (Vint Int.zero) 32) r],
    while clear's POST wants [scalar_at .. scalar_zero], i.e.
    [data_at sh t_secp256k1_scalar (scalar_to_val scalar_zero) r].
    The bridge from the zeroed byte array to the zeroed struct goes
    through [mapsto_zeros]: the helper [data_at_tuchar_zeros_mapsto_zeros]
    (zeroed [tuchar] array |-- [mapsto_zeros]) feeds VST's
    [mapsto_zero_data_at_zero] ([mapsto_zeros] |-- [data_at .. (zero_val)]),
    and [scalar_to_val scalar_zero = zero_val t_secp256k1_scalar]. *)

(* ================================================================= *)
(** ** Bridge helpers -- zeroed [tuchar] array to [mapsto_zeros]. *)

(** [field_compatible] for a [tuchar] array at a concrete in-range
    offset.  Byte arrays are [1]-aligned, so the only real obligation
    is the size bound. *)
Lemma field_compatible_tarray_tuchar_repr {cs : compspecs} (b : block) (z m : Z) :
  0 <= z ->
  0 <= m ->
  z + m < Ptrofs.modulus ->
  field_compatible (tarray tuchar m) [] (Vptr b (Ptrofs.repr z)).
Proof.
  intros Hz Hm Hzm.
  repeat split; auto.
  - unfold size_compatible.
    simpl.
    rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    rewrite Z.max_r by lia.
    lia.
  - unfold align_compatible.
    rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    apply align_compatible_rec_Tarray.
    intros i Hi.
    eapply align_compatible_rec_by_value; [ reflexivity |].
    simpl.
    apply Z.divide_1_l.
Qed.

(** A zeroed [tuchar] array entails [mapsto_zeros] over the same
    extent.  There is no off-the-shelf VST lemma for this direction
    (every [mapsto_zeros] lemma runs [mapsto_zeros |-- ..]); we prove
    it by peeling one byte at a time.  Each zeroed byte's [data_at]
    is a [mapsto] whose readable-share unfolding is exactly the
    [address_mapsto Mint8unsigned (Vint Int.zero)] that one step of
    [address_mapsto_zeros] expects. *)
Lemma data_at_tuchar_zeros_mapsto_zeros {cs : compspecs} (sh : share) (n : Z) (p : val) :
  readable_share sh ->
  0 <= n ->
  data_at sh (tarray tuchar n) (Zrepeat (Vint Int.zero) n) p |-- mapsto_zeros n sh p.
Proof.
  intros Hsh Hn.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as Hfc by entailer!.
  assert (Hp : isptr p) by (apply field_compatible_isptr in Hfc; auto).
  destruct p as [| | | | | b ofs]; try contradiction Hp.
  clear Hp.
  (* the array size bound, freed from the [field_compatible] record *)
  assert (Hsz : Ptrofs.unsigned ofs + n < Ptrofs.modulus).
  {
    destruct Hfc as [_ [_ [Hsc _]]].
    unfold size_compatible in Hsc.
    simpl in Hsc.
    rewrite Z.max_r in Hsc by lia.
    rewrite Z.mul_1_l in Hsc.
    lia.
  }
  clear Hfc.
  (* normalise the pointer offset to [Ptrofs.repr z] with [0 <= z] *)
  remember (Ptrofs.unsigned ofs) as z eqn:Hzeq.
  assert (Hz0 : 0 <= z) by (subst z; apply Ptrofs.unsigned_range).
  assert (Hofs : ofs = Ptrofs.repr z) by (subst z; rewrite Ptrofs.repr_unsigned; reflexivity).
  rewrite Hofs.
  clear Hofs Hzeq ofs.
  (* induct on the byte count as a [nat], generalising the offset *)
  rewrite <- (Z2Nat.id n) in Hsz, Hn |- * by lia.
  remember (Z.to_nat n) as k eqn:Hkeq.
  clear Hkeq Hn n.
  revert z Hz0 Hsz.
  induction k as [| k IHk]; intros z Hz0 Hsz.
  - (* base: the empty array is [emp], as is [mapsto_zeros 0] *)
    change (Z.of_nat 0) with 0.
    rewrite data_at_zero_array_eq by (simpl; auto).
    unfold mapsto_zeros.
    simpl.
    apply andp_right.
    + apply prop_right.
      pose proof (Ptrofs.unsigned_range (Ptrofs.repr z)).
      lia.
    + apply derives_refl.
  - (* step: peel the first byte off both sides *)
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat k)) with (1 + Z.of_nat k) by lia.
    rewrite (aggregate_pred.mapsto_zeros_split sh b z 1 (Z.of_nat k)) by lia.
    rewrite (split2_data_at_Tarray_tuchar sh (1 + Z.of_nat k) 1)
      by (try lia; rewrite Zlength_Zrepeat by lia; lia).
    replace (1 + Z.of_nat k - 1) with (Z.of_nat k) by lia.
    rewrite sublist_one by (try rewrite Zlength_Zrepeat; lia).
    rewrite Znth_Zrepeat by lia.
    rewrite sublist_Zrepeat by lia.
    replace (1 + Z.of_nat k - 1) with (Z.of_nat k) by lia.
    (* the tail's pointer is [Vptr b (Ptrofs.repr (z + 1))] *)
    assert (Hfc : field_compatible (Tarray tuchar (1 + Z.of_nat k) noattr) []
                    (Vptr b (Ptrofs.repr z))).
    { apply field_compatible_tarray_tuchar_repr; lia. }
    assert (Hfa : field_address0 (Tarray tuchar (1 + Z.of_nat k) noattr) (SUB 1)
                    (Vptr b (Ptrofs.repr z)) = Vptr b (Ptrofs.repr (z + 1))).
    {
      rewrite field_address0_offset.
      - simpl.
        unfold offset_val.
        rewrite ptrofs_add_repr.
        reflexivity.
      - apply field_compatible0_cons.
        simpl.
        split; [lia | apply Hfc].
    }
    rewrite Hfa.
    apply sepcon_derives.
    { (* head: a single zeroed byte *)
      rewrite data_at_tuchar_singleton_array_eq.
      assert (Hfct : field_compatible tuchar [] (Vptr b (Ptrofs.repr z))).
      {
        apply (field_compatible_tarray_tuchar_repr b z 1) in Hz0 as Htmp; [| lia | lia].
        clear Htmp.
        repeat split; auto.
        - unfold size_compatible.
          simpl.
          rewrite Ptrofs.unsigned_repr
            by (unfold Ptrofs.max_unsigned; rewrite Nat2Z.inj_succ in Hsz; lia).
          rewrite Nat2Z.inj_succ in Hsz.
          lia.
        - unfold align_compatible.
          rewrite Ptrofs.unsigned_repr
            by (unfold Ptrofs.max_unsigned; rewrite Nat2Z.inj_succ in Hsz; lia).
          eapply align_compatible_rec_by_value; [ reflexivity |].
          simpl.
          apply Z.divide_1_l.
      }
      rewrite <- (mapsto_data_at' sh tuchar (Vint Int.zero) (Vint Int.zero)
                    (Vptr b (Ptrofs.repr z)));
        auto; try reflexivity.
      unfold mapsto, mapsto_zeros.
      simpl.
      rewrite if_true by auto.
      apply orp_left.
      - (* the read-value disjunct: matches the single [address_mapsto] *)
        Intros.
        apply andp_right.
        + apply andp_left1.
          apply prop_right.
          split.
          apply Ptrofs.unsigned_range.
          rewrite Ptrofs.unsigned_repr
            by (unfold Ptrofs.max_unsigned; rewrite Nat2Z.inj_succ in Hsz; lia).
          rewrite Nat2Z.inj_succ in Hsz.
          lia.
        + apply andp_left2.
          rewrite predicates_sl.sepcon_emp.
          apply derives_refl.
      - (* the [Vundef] disjunct is impossible: the byte value is [0] *)
        Intros.
        discriminate.
    }
    { (* tail: the inductive hypothesis at offset [z + 1] *)
      apply IHk; [lia |].
      rewrite Nat2Z.inj_succ in Hsz.
      lia.
    }
Qed.

(** [scalar_to_val scalar_zero] is the all-zero struct representation. *)
Lemma scalar_to_val_scalar_zero :
  scalar_to_val scalar_zero = zero_val t_secp256k1_scalar.
Proof.
  rewrite zero_val_eq.
  unfold t_secp256k1_scalar.
  unfold scalar_to_val, scalar_zero, scalar_val.
  simpl.
  apply JMeq_eq.
  eapply JMeq_trans; [| apply JMeq_sym; apply fold_reptype_JMeq].
  apply eq_JMeq.
  rewrite zero_val_tarray.
  unfold Zrepeat, tulong.
  simpl.
  rewrite zero_val_Tlong.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Body proof. *)

Lemma body_secp256k1_scalar_clear:
  semax_body Vprog Gprog
    f_secp256k1_scalar_clear spec_secp256k1_scalar_clear.
Proof.
  start_function.

  (* ===== Stage 0: reinterpret the struct as bytes, then memclear ===== *)

  (* capture the struct's [field_compatible] before the SEP is rebuilt as bytes *)
  assert_PROP (field_compatible t_secp256k1_scalar [] r_ptr) as Hfc by entailer!.
  (* reinterpret the uninitialised struct as a raw byte block *)
  sep_apply (data_at__memory_block sh t_secp256k1_scalar r_ptr).
  (* secp256k1_memclear_explicit(r, sizeof *r) -- clears all 32 bytes *)
  forward_call (sh, r_ptr, sizeof t_secp256k1_scalar).
  { entailer!. }

  (* ===== Postcondition: the zeroed byte array bridges to [scalar_at .. scalar_zero] ===== *)

  Exists scalar_zero.
  entailer!.
  change (scalar_at sh r_ptr scalar_zero)
    with (data_at sh t_secp256k1_uint256 (scalar_to_val scalar_zero) r_ptr).
  rewrite scalar_to_val_scalar_zero.
  change t_secp256k1_uint256 with t_secp256k1_scalar.
  eapply derives_trans; [ | apply mapsto_zero_data_at_zero ].
  - apply data_at_tuchar_zeros_mapsto_zeros.
    + apply writable_readable; auto.
    + pose proof (sizeof_pos t_secp256k1_scalar).
      lia.
  - apply writable_readable; auto.
  - reflexivity.
  - reflexivity.
  - apply Hfc.
Qed.
