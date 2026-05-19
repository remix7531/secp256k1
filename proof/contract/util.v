(** * contract.util: funspecs for the byte-order helpers in [src/util.h]. *)
(** Copyright (C) 2026 remix7531
    [debruijn64_array] is ported from BlockstreamResearch/simplicity
    Coq/C/secp256k1/spec_modinv64.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** [secp256k1_read_be64] / [secp256k1_write_be64]: big-endian (de)serialization
    of a 64-bit word over an 8-byte buffer.  Pulled into the AST transitively by
    [secp256k1_scalar_set_b32] / [secp256k1_scalar_get_b32], which are the only
    in-scope callers.  The byte<->Z math is [theory.bytes]. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.bytes.
Require Import secp256k1.model.int128.
Require Import secp256k1.theory.extra_math.
Require Import secp256k1.contract.helper.notations.

(* ================================================================= *)
(** ** Byte-order helper funspecs -- [secp256k1_read_be64] / [secp256k1_write_be64]. *)

(** [secp256k1_read_be64]: decode 8 big-endian bytes at [p] to a [uint64_t]. *)
Definition spec_secp256k1_read_be64 : ident * funspec :=
  DECLARE _secp256k1_read_be64
  WITH p : val, bs : list Z, sh : share
  PRE [ tptr tuchar ]
    PROP (readable_share sh;
          Zlength bs = 8;
          Forall (fun b => (0 <= b < 256)%Z) bs)
    PARAMS (p)
    SEP (bytes8_at sh p bs)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (Z_of_be_bytes bs)))
    SEP (bytes8_at sh p bs).

(** [secp256k1_write_be64]: store [x] as 8 big-endian bytes at [p]. *)
Definition spec_secp256k1_write_be64 : ident * funspec :=
  DECLARE _secp256k1_write_be64
  WITH p : val, x : UInt64, sh : share
  PRE [ tptr tuchar, tulong ]
    PROP (writable_share sh)
    PARAMS (p; uint64_to_val x)
    SEP (bytes8_at_ sh p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (bytes8_at sh p (be_bytes_of_Z (u64_val x) 8%nat)).

(* ================================================================= *)
(** ** Secure-clear funspecs -- [memzero_explicit] / [memclear_explicit]. *)

(** [secp256k1_memzero_explicit(p, n)]: zero the [n] bytes at [p] (won't be
    optimized out). Under [SECP256K1_NO_LIBC] the body is a pure-C byte loop (no
    libc dependency); the result is the buffer filled with zero bytes. *)
Definition spec_secp256k1_memzero_explicit : ident * funspec :=
  DECLARE _secp256k1_memzero_explicit
  WITH sh : share, p : val, n : Z
  PRE [ tptr tvoid, tulong ]
    PROP (writable_share sh;
          0 <= n <= Ptrofs.max_unsigned)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (memory_block sh n p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (zeros_at sh p n).

(** [secp256k1_memclear_explicit(p, n)]: cleanse the [n] bytes at [p]. The
    current implementation just zeroes (callers must not rely on it), so the
    spec matches [memzero_explicit]. *)
Definition spec_secp256k1_memclear_explicit : ident * funspec :=
  DECLARE _secp256k1_memclear_explicit
  WITH sh : share, p : val, n : Z
  PRE [ tptr tvoid, tulong ]
    PROP (writable_share sh;
          0 <= n <= Ptrofs.max_unsigned)
    PARAMS (p; Vlong (Int64.repr n))
    SEP (memory_block sh n p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (zeros_at sh p n).

(* ================================================================= *)
(** ** The de Bruijn lookup table -- [debruijn64_array]. *)

(** The read-only [debruijn] lookup table (a [const unsigned char[64]]
    global) used by [secp256k1_ctz64_var_debruijn] (declared in [util.h]).
    Reconstructs the [mpred] for the global directly from its [Init_int8]
    initializer data in the Clight AST, so the spec carries the exact byte
    contents.  Lives in the util layer with the [ctz64_var(_debruijn)] specs
    (header-faithful: both are declared in [util.h], not [modinv64_impl.h]). *)
Definition debruijn64_array (sh: share) (gv: globals) : mpred :=
  Eval cbn in
  let
    is_all_init_int8 := fix is_all_init_int8 (l : list init_data) :=
      match l with
      | [] => True
      | Init_int8 _ :: l' => is_all_init_int8 l'
      | _ => False
      end
  in let
    uninit_int8s := fix uninit_int8s (l: list init_data) :
        is_all_init_int8 l -> list int :=
      match l with
      | [] => fun _ => []
      | x :: l' =>
        match x with
        | Init_int8 i => fun pf => i :: uninit_int8s l' pf
        | _ => False_rec (list int)
        end
      end
  in data_at sh (gvar_info v_debruijn)
    (map Vint (uninit_int8s (gvar_init v_debruijn) I)) (gv _debruijn).

(* ================================================================= *)
(** ** Count-trailing-zeros funspecs -- [ctz64_var] / [ctz64_var_debruijn]. *)

(** Both are declared in [src/util.h] (not [modinv64_impl.h]), so they are
    public-util funspecs even though only the modinv safegcd path calls them. *)

(** [secp256k1_ctz64_var_debruijn]: count trailing zeros of [a] via the
    de Bruijn lookup table. Returns [Z_ctz a] (defined for [a = 0] here, as
    the table-based routine takes any 64-bit input). *)
Definition spec_secp256k1_ctz64_var_debruijn : ident * funspec :=
  DECLARE _secp256k1_ctz64_var_debruijn
  WITH a : Z, sh_debruijn : share, gv : globals
  PRE [ tulong ]
    PROP (0 <= a < Int64.modulus;
          readable_share sh_debruijn)
    PARAMS (Vlong (Int64.repr a))
    GLOBALS (gv)
    SEP (debruijn64_array sh_debruijn gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z_ctz a)))
    SEP (debruijn64_array sh_debruijn gv).

(** [secp256k1_ctz64_var]: count trailing zeros of [a], returning [Z_ctz a].
    The PRE requires [0 < a]: the underlying routine is undefined for 0. *)
Definition spec_secp256k1_ctz64_var : ident * funspec :=
  DECLARE _secp256k1_ctz64_var
  WITH a : Z, sh_debruijn : share, gv : globals
  PRE [ tulong ]
    PROP (0 < a < Int64.modulus;
          readable_share sh_debruijn)
    PARAMS (Vlong (Int64.repr a))
    GLOBALS (gv)
    SEP (debruijn64_array sh_debruijn gv)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (Z_ctz a)))
    SEP (debruijn64_array sh_debruijn gv).
