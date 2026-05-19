(** * vst.base: floyd + the Clight AST + [CompSpecs]/[Vprog] -- the VST root. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The single file through which the proof tree sees the toolchain: floyd's
    proof automation, CompCert's [Zbits], and the extracted Clight AST
    ([prog]).  Everything under [vst/] is toolchain glue with zero trusted
    content; [theory/] and [model/] never import it. *)

Require Export VST.floyd.proofauto.
Require Export compcert.lib.Zbits.
Require Export secp256k1.clight.extraction.

(* ================================================================= *)
(** ** CompSpecs / Vprog -- VST [compspecs] / [varspecs] from the AST [prog]. *)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Struct type aliases.

    The clightgen anonymous-composite ids (t_secp256k1_scalar / _uint128 / _acc /
    _modinv64_* etc.) are not defined here.  They are quarantined into the
    per-subsystem files [contract/helper/structs_int128.v],
    [contract/helper/structs_scalar.v], [contract/helper/structs_field.v], and
    [contract/helper/structs_modinv.v] so that a re-extraction's id renumber
    touches only the owning subsystem, not the ~100 importers of this file.
    Require the relevant structs_* file in the subsystem contract that needs
    the alias. *)
