(** * vst.scaffold: body obligations for extracted functions. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

Require Import secp256k1.vst.gprog.

Definition FullVprog : varspecs.
  mk_varspecs extraction.prog.
Defined.

(** These obligations use the full extraction and the arithmetic contracts. *)
Definition Pending (spec : ident * funspec) : Prop :=
  match initial_world.find_id (fst spec) extraction.global_definitions with
  | Some (Gfun (Internal body)) =>
      semax_body FullVprog (Gprog ++ [spec]) body spec
  | _ => False
  end.
