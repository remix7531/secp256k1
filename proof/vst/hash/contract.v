(** * vst.hash.contract: funspecs for src/hash.h. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The contract describes memory ownership and the function signature.
    [memory_block] leaves the hash context and hash state contents
    unconstrained. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.vst.composites.
Require secp256k1.specification.
Import specification.Math.
Import specification.Math.sha256.

Definition t_secp256k1_hash_context : type :=
  Tstruct ltac:(derive_struct_id
    (cons (_fn_sha256_compression, @None type) nil)) noattr.

Definition t_secp256k1_sha256 : type :=
  Tstruct ltac:(derive_struct_id
    (cons (_s, Some (tarray tuint 8))
      (cons (_buf, Some (tarray tuchar 64))
        (cons (_bytes, Some tulong) nil)))) noattr.

(* ================================================================= *)
(** ** [secp256k1_sha256_write]: absorb bytes into a running hash.

    The context selects the compression function through a function pointer.
    The contract preserves the input bytes and ownership of the context and
    hash state. It does not specify a hash state transition. *)

Definition spec_secp256k1_sha256_write : ident * funspec :=
  DECLARE _secp256k1_sha256_write
  WITH h_ptr : val, hash_ptr : val, d_ptr : val, data : list Z,
       sh_h : share, sh_hash : share, sh : share
  PRE [ tptr t_secp256k1_hash_context, tptr t_secp256k1_sha256,
        tptr tuchar, tulong ]
    PROP (readable_share sh_h;
          writable_share sh_hash;
          readable_share sh;
          (0 <= Zlength data <= Int64.max_unsigned)%Z;
          Forall (fun b => (0 <= b < 256)%Z) data)
    PARAMS (h_ptr; hash_ptr; d_ptr; Vlong (Int64.repr (Zlength data)))
    SEP (memory_block sh_h (sizeof t_secp256k1_hash_context) h_ptr;
         memory_block sh_hash (sizeof t_secp256k1_sha256) hash_ptr;
         data_at sh (tarray tuchar (Zlength data))
                 (map (fun b => Vint (Int.repr b)) data) d_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (memory_block sh_h (sizeof t_secp256k1_hash_context) h_ptr;
         memory_block sh_hash (sizeof t_secp256k1_sha256) hash_ptr;
         data_at sh (tarray tuchar (Zlength data))
                 (map (fun b => Vint (Int.repr b)) data) d_ptr).

(* ================================================================= *)
(** ** Hash contracts for the full extraction. *)
Definition Gprog_hash_scaffold : funspecs := [
  spec_secp256k1_sha256_write
].
