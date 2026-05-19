(** * vst.composites: derive the anonymous composite ids by member signature. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** clightgen numbers the extraction's anonymous structs ([__755], [__837],
    ...) and renumbers them whenever the identifier set changes -- the [_acc]
    id alone has drifted [__1234 -> __1238 -> __1251 -> __1191] across feature
    additions.  The member NAMES ([_d], [_lo]/[_hi], [_n], ...) are stable
    Coq identifiers, so instead of hand-pinning the numbers, the
    [contract/helper/structs_*.v] files derive them: [derive_struct_id]
    scans [extraction.composites] for the unique Struct whose member list
    matches a given [(name, optional exact type)] signature.

    - A non-match or an ambiguous match is a COMPILE ERROR at the structs
      file, not a silent mismatch at proof time.
    - When two structs share member names (e.g. a future [fe] vs
      [fe_storage], both [{ _n }]), disambiguate with the exact member type
      ([Some (tarray tulong 5)] vs [Some (tarray tulong 4)]).
    - Nested composites are matched by member name only, so inner-id drift
      never propagates into a signature. *)

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
