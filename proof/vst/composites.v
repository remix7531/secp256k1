(** * vst.composites: derive the anonymous composite ids by member signature. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** Anonymous struct numbers can change on extraction. Match structs by
    member names and optional exact types, requiring a unique match.
    Exact types distinguish structs with the same names, such as field
    elements and field storage. Nested struct members match by name to
    avoid depending on their generated numbers. *)

From Stdlib Require Import PArith.
From compcert Require Import AST Ctypes.
Require Import secp256k1.clight.extraction.

(* ================================================================= *)
(** ** Signature matching -- [members_match] over [(ident * option type)]. *)

(** One member matches one signature entry: names must agree; the type is
    checked only when the signature pins it. *)
Definition member_matches (m : member) (s : ident * option type) : bool :=
  match m, s with
  | Member_plain mid mty, (sid, oty) =>
      Pos.eqb mid sid &&
      match oty with
      | None => true
      | Some ty => if type_eq mty ty then true else false
      end
  | _, _ => false
  end.

Fixpoint members_match (ms : members) (sig : list (ident * option type))
  : bool :=
  match ms, sig with
  | nil, nil => true
  | cons m ms', cons s sig' => andb (member_matches m s) (members_match ms' sig')
  | _, _ => false
  end.

(** The ids of every Struct in the extraction whose member list matches. *)
Definition find_matches (sig : list (ident * option type)) : list ident :=
  List.fold_right
    (fun c acc =>
       match c with
       | Composite id Struct ms _ =>
           if members_match ms sig then cons id acc else acc
       | _ => acc
       end)
    nil composites.

(* ================================================================= *)
(** ** The deriver -- [derive_struct_id] (unique match or compile error). *)

Ltac derive_struct_id sig :=
  let r := eval vm_compute in (find_matches sig) in
  lazymatch r with
  | cons ?id nil => exact id
  | nil => fail "derive_struct_id: no composite matches the signature"
  | _ => fail "derive_struct_id: ambiguous signature -- pin a member type"
  end.
