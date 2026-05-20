(** * tactics.hygiene: simpl-never / opacity hygiene for shift/pow-heavy proofs. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** [forward] DIVERGES on a shift store/return (the value-eval [simpl]-unfolds
    [Int64.Z_mod_modulus] over [Z.shiftr]/[Z.shiftl] and blows up), and the field
    subsystem is wall-to-wall [& M] / [>> 52] / [<< 12].  This file hoists the
    [simpl never] + [Opaque] directives -- otherwise re-declared per proof file --
    into one place that field (and any other shift/pow-heavy) verif file can
    [Require Import].

    SCOPE NOTE: [Arguments ... : simpl never] persists in the .vo and applies to
    every file that (transitively) Requires this one; a bare [Opaque] does NOT
    survive a [Require] in Rocq 9, so the opacity is declared [#[global]] below
    to get the same reach.  That is the intent.  Neither affects
    [vm_compute]/[native_compute] (which bypass opacity), so concrete reflection
    proofs are unaffected -- only [simpl]/[cbn]/[unfold]/[compute] are.

    Verif files get these settings by Requiring this module LAST in their
    Require block (see STYLE.md); contract files that need [Z.shiftr]/[Z.pow]
    opaque during their own elaboration keep a local [Opaque] line. *)

Require Import VST.floyd.proofauto.
Require Import compcert.lib.Zbits.

Arguments Int64.Z_mod_modulus : simpl never.
Arguments Z.shiftr : simpl never.
Arguments Z.shiftl : simpl never.
#[global] Opaque Z.shiftl Z.shiftr Z.pow.
