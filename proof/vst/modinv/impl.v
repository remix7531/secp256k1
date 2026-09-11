(** * vst.modinv.impl: INTERNAL funspecs for the safegcd modular inverse. *)
(** Copyright (C) 2026 remix7531
    Ported from BlockstreamResearch/simplicity Coq/C/secp256k1/spec_modinv64.v
    (commit c1dddedd), Copyright (c) 2018 Blockstream, originally MIT.
    Upstream notice reproduced in proof/README.md.
    SPDX-License-Identifier: MIT *)

(** Mirrors [src/modinv64_impl.h]: the funspecs here are for the [static]
    helpers that are NOT part of the public [modinv64.h] surface
    ([signed62_assign], [normalize_62], [divsteps_59], [divsteps_62_var],
    [update_de_62], [update_de_limb], [update_fg_62], [update_fg_62_var]) plus
    the internal [Trans_repr] representation glue.  The public driver funspecs
    ([secp256k1_modinv64] / [_var]) live in [vst/modinv/contract.v] (re-exported
    here), in its [Gprog_modinv_public]; the internal ones below are listed in
    this file's [Gprog_modinv_impl].

    Adapted for Rocq 9.0 / VST 2.16 against this repo's single extraction AST. *)

Require Import VST.floyd.proofauto.
Require Import secp256k1.vst.base.
Require Import secp256k1.vst.helper.structs_int128.
Require Import secp256k1.vst.helper.structs_modinv.
Require Import secp256k1.theory.int128.int128.
Require Import secp256k1.vst.helper.notations.
Require Import secp256k1.vst.int128.contract.
Require Import secp256k1.vst.int128.impl.
Require Import secp256k1.vst.scalar.contract.
Require Import secp256k1.vst.scalar.impl.
Require secp256k1.theory.modinv.construction.divstep.
Require secp256k1.theory.modinv.construction.divstep_trans.
Require secp256k1.theory.modinv.construction.divstep_zeta.
(* Public driver specs ([modinv64] / [_var]) live in [vst/modinv/contract.v]; re-export
   them -- and, transitively, [signed62] / [util] -- so the modinv body proofs
   that [Require Import contract.impl.modinv] get the whole modinv funspec
   context + [Gprog] from a single import. *)
Require Export secp256k1.vst.modinv.contract.

Opaque Z.shiftr Z.pow.

(* ================================================================= *)
(** ** C representation of a 2x2 transition matrix -- [Trans_repr]. *)

(** C representation of a [2x2] transition matrix: the four limbs [u,v,q,r]
    of the model [M2x2], each as a [Vlong], in the [secp256k1_modinv64_trans2x2]
    struct layout.  Used only by the internal modinv helper specs. *)
Definition Trans_repr (m: divstep_trans.Trans.M2x2) : reptype t_secp256k1_modinv64_trans2x2 :=
( Vlong (Int64.repr (divstep_trans.Trans.u m))
, (Vlong (Int64.repr (divstep_trans.Trans.v m))
, (Vlong (Int64.repr (divstep_trans.Trans.q m))
, Vlong (Int64.repr (divstep_trans.Trans.r m))
))).

(** A [secp256k1_modinv64_trans2x2] buffer holding the matrix [m]; the [_at]
    shorthand for [Trans_repr], mirroring [signed62_at] / [modinfo_at]. *)
Notation "'trans2x2_at' sh p m" :=
  (data_at sh t_secp256k1_modinv64_trans2x2 (Trans_repr m) p)
  (at level 20, sh at level 0, p at level 0, m at level 0).

(** A [secp256k1_modinv64_signed62] buffer holding the zero-padded [len]-limb
    form of [x] -- the variable-length counterpart of [signed62_at] used by
    the [update_fg_62_var] driver ([len] active limbs, padded out to 5). *)
Notation "'signed62_var_at' sh p len x" :=
  (data_at sh t_secp256k1_modinv64_signed62 (Signed62.pad (Signed62.reprn len x)) p)
  (at level 20, sh at level 0, p at level 0, len at level 0, x at level 0).

(** [secp256k1_modinv64_signed62_assign]: limb-by-limb copy [*r = *a] of a
    5-limb signed62 number (explicit copy, not an aggregate assignment). *)
Definition spec_secp256k1_modinv64_signed62_assign : ident * funspec :=
  DECLARE _secp256k1_modinv64_signed62_assign
  WITH x : Z, ptr_dst : val, ptr_src : val, sh_dst : share, sh_src : share
  PRE [ tptr t_secp256k1_modinv64_signed62, tptr t_secp256k1_modinv64_signed62 ]
    PROP (writable_share sh_dst;
          readable_share sh_src)
    PARAMS (ptr_dst; ptr_src)
    SEP (data_at_ sh_dst t_secp256k1_modinv64_signed62 ptr_dst;
         signed62_at sh_src ptr_src x)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_at sh_dst ptr_dst x;
         signed62_at sh_src ptr_src x).

(* ================================================================= *)
(** ** Helper funspecs -- [from vst/modinv/verif/modinv64.v]. *)

(** The helper-function funspecs were defined inline in the monolithic
    [vst/modinv/verif/modinv64.v].  Moved here so the body proof of each C function
    gets its own verif file (the project one-semax_body-per-file rule).
    ([Trans_repr] now lives in [vst.modinv.impl].)  These bodies are proved
    against the one global [Gprog] of [vst/gprog.v]. *)

(** [secp256k1_ctz64_var] / [secp256k1_ctz64_var_debruijn] are public-util
    funspecs (both declared in [src/util.h]) -- now in [vst/util/contract.v],
    whose [Gprog_util] the global table already carries (this file requires
    [vst/util/contract.v], re-exported above). *)

(** [secp256k1_modinv64_normalize_62]: bring [r] from range
    [(-2*modulus, modulus)] into [[0, modulus)] by adding a multiple of the
    modulus, optionally negating first when [sign < 0]. The result is the
    5-limb form of [(if sign<0 then -r else r) mod m].  The sign argument is a
    mathematical integer [sign : Z], constrained to the [int64] range and
    passed as [Int64.repr sign]. *)
Definition spec_secp256k1_modinv64_normalize_62 : ident * funspec :=
  DECLARE _secp256k1_modinv64_normalize_62
  WITH r : Z, sign : Z, m : Z,
       ptrr : val, ptrm : val, shr : share, shm : share
  PRE [ tptr t_secp256k1_modinv64_signed62,
        tlong,
        tptr t_secp256k1_modinv64_modinfo ]
    PROP (0 <= m <= 2^310 - 2 ^ 248;
          -2^310 + 2^248 <= r;
          -2 * m < r < m;
          Int64.min_signed <= sign <= Int64.max_signed;
          writable_share shr;
          readable_share shm)
    PARAMS (ptrr; Vlong (Int64.repr sign); ptrm)
    SEP (signed62_at shr ptrr r;
         modinfo_at shm ptrm m)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_at shr ptrr ((if sign <? 0 then -r else r) mod m);
         modinfo_at shm ptrm m).

(** [secp256k1_modinv64_divsteps_62_var]: run 62 variable-time divsteps from
    state [st], writing the accumulated transition matrix [trans_n 62 st] to
    [*t] and returning the final [eta]. Models [step_n 62] / [trans_n 62]. *)
Definition spec_secp256k1_modinv64_divsteps_62_var : ident * funspec :=
  DECLARE _secp256k1_modinv64_divsteps_62_var
  WITH st : divstep.State, t : val, sh : share,
       sh_debruijn : share, gv : globals
  PRE [ tlong, tulong, tulong, tptr t_secp256k1_modinv64_trans2x2 ]
    PROP (-683 <= divstep.eta st < 683;
          writable_share sh;
          readable_share sh_debruijn)
    PARAMS (Vlong (Int64.repr (divstep.eta st)); Vlong (Int64.repr (divstep.f st)); Vlong (Int64.repr (divstep.g st)); t)
    GLOBALS (gv)
    SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t;
         debruijn64_array sh_debruijn gv)
  POST [ tlong ]
    PROP ()
    RETURN (Vlong (Int64.repr (divstep.eta (fst (divstep.step_n 62 st)))))
    SEP (trans2x2_at sh t (divstep_trans.Trans.trans_n 62 st);
         debruijn64_array sh_debruijn gv).

(** [secp256k1_modinv64_divsteps_59]: the CONSTANT-time divstep core.  Runs 59
    zeta-divsteps from the [ZState] [st] (built from the bottom limbs
    [f.v[0]] / [g.v[0]] and the running [zeta]), writing the accumulated
    transition matrix to [*t] and returning the new [zeta].  Unlike the
    variable-time [divsteps_62_var], it takes NO debruijn table / GLOBALS (it
    runs a fixed 59-iteration loop, no [ctz64] lookup), and the output matrix is
    SCALED BY [2^62] not [2^59]: the C seeds [u,v,q,r] with [8*I] (det [2^6]),
    so after 59 unit-determinant divsteps the matrix is [scale_m 8 (ztrans_n 59
    st)] (det [2^65]) and [ap (scale_m 8 (ztrans_n 59 st)) (zfg st) =
    scale (2^62) (zfg (fst (zstep_n 59 st)))] (since [8 * 2^59 = 2^62]).

    Bounds rationale (settled here for the Wave B-2 body prover to target):
    - [zeta]: input envelope [-1063 <= zeta <= 1063].  This is what the
      [modinv64] driver can supply -- [zeta_bounds] gives [|zeta| <= 1 + 2*59*i]
      at iteration [i], maximal at [i = 9] ([1 + 118*9 = 1063]).  It is faithful
      to the C (the true [zeta] stays inside the dropped [VERIFY_CHECK]'s
      [[-591,591]], which lies within this coarse envelope); the body needs only
      this loose range to keep the [u,v,q,r] accumulators inside [int64] (the
      tight [591] check was a dropped [VERIFY_CHECK], so the body does not need
      it).  Symmetric, generous, and exactly the driver's reachable set.
    - No explicit [zf]/[zg] range (mirrors [divsteps_62_var_spec]): the bottom
      limbs are passed as [Vlong (Int64.repr (zf st))] / [Vlong (Int64.repr
      (zg st))]; their values are limbs in [[0, 2^62)] but the spec leaves them
      abstract -- the body reasons over the C's [uint64] arithmetic directly.

    Note: [divstep_zeta.scale_m] lives in [theory/modinv/construction/divstep_zeta.v] (the
    [Trans] module lives in [theory/modinv/construction/divstep_trans.v]), so the matrix
    is [divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 st)]. *)
Definition spec_secp256k1_modinv64_divsteps_59 : ident * funspec :=
  DECLARE _secp256k1_modinv64_divsteps_59
  WITH st : divstep_zeta.ZState, t : val, sh : share
  PRE [ tlong, tulong, tulong, tptr t_secp256k1_modinv64_trans2x2 ]
    PROP (-1063 <= divstep_zeta.zeta st <= 1063;
          writable_share sh)
    PARAMS (Vlong (Int64.repr (divstep_zeta.zeta st)); Vlong (Int64.repr (divstep_zeta.zf st)); Vlong (Int64.repr (divstep_zeta.zg st)); t)
    SEP (data_at_ sh t_secp256k1_modinv64_trans2x2 t)
  POST [ tlong ]
    PROP ()
    RETURN (Vlong (Int64.repr (divstep_zeta.zeta (fst (divstep_zeta.zstep_n 59 st)))))
    SEP (trans2x2_at sh t
           (divstep_zeta.scale_m 8 (divstep_zeta.ztrans_n 59 st))).

(** [secp256k1_modinv64_update_de_62]: compute [(t/2^62) * [d,e] mod modulus],
    updating [*d] and [*e] in place to [fst]/[snd] of [update_de m d e mtx].
    Both [d] and [e] stay in [(-2*modulus, modulus)]. *)
Definition spec_secp256k1_modinv64_update_de_62 : ident * funspec :=
  DECLARE _secp256k1_modinv64_update_de_62
  WITH d : Z, e : Z, mtx : divstep_trans.Trans.M2x2, m : Z,
       ptrd : val, ptre : val, ptrt : val, ptrm : val, shd : share, she : share, sht : share, shm : share
  PRE [ tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_trans2x2,
        tptr t_secp256k1_modinv64_modinfo ]
    PROP (Z.Odd m;
          0 <= m <= 2^308;
          -2 * m < d < m;
          -2 * m < e < m;
          divstep_trans.Trans.bounded (2 ^ 62) mtx;
          writable_share shd;
          writable_share she;
          readable_share sht;
          readable_share shm)
    PARAMS (ptrd; ptre; ptrt; ptrm)
    SEP (signed62_at shd ptrd d;
         signed62_at she ptre e;
         trans2x2_at sht ptrt mtx;
         modinfo_at shm ptrm m)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_at shd ptrd (fst (divstep_zeta.update_de m d e mtx));
         signed62_at she ptre (snd (divstep_zeta.update_de m d e mtx));
         trans2x2_at sht ptrt mtx;
         modinfo_at shm ptrm m).

(** [secp256k1_modinv64_update_fg_62_var]: compute [(mtx * [f,g]) / 2^62],
    updating [*f] and [*g] in place.  The contract is arithmetic rather than
    divstep-shaped: the caller supplies the matrix [mtx] together with the
    pre-image [(f0, g0)] and the post-image [(f1, g1)] it maps to, related by
    [ap mtx (f0, g0) = scale (2^62) (f1, g1)] with [mtx] bounded by [2^62].
    Every driver -- the divstep one and the positive-divstep (Jacobi) one --
    instantiates that identity from its own transition lemmas.
    Variable-length version operating on [len] active limbs. *)
Definition spec_secp256k1_modinv64_update_fg_62_var : ident * funspec :=
  DECLARE _secp256k1_modinv64_update_fg_62_var
  WITH len : nat, f0 : Z, g0 : Z, f1 : Z, g1 : Z,
       mtx : divstep_trans.Trans.M2x2,
       ptrf : val, ptrg : val, ptrt : val,
       shf : share, shg : share, sht : share
  PRE [ tint,
        tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_trans2x2 ]
    PROP ((1 <= len <= 5)%nat;
          divstep_trans.Trans.ap mtx
            {| divstep_trans.Trans.x := f0; divstep_trans.Trans.y := g0 |}
            = divstep_trans.Trans.scale (2 ^ 62)
                {| divstep_trans.Trans.x := f1; divstep_trans.Trans.y := g1 |};
          divstep_trans.Trans.bounded (2 ^ 62) mtx;
          -2^(62 * Z.of_nat len + 1) <= f0 <= 2^(62 * Z.of_nat len + 1) - 1;
          -2^(62 * Z.of_nat len + 1) <= g0 <= 2^(62 * Z.of_nat len + 1) - 1;
          writable_share shf;
          writable_share shg;
          readable_share sht)
    PARAMS (Vint (Int.repr (Z.of_nat len)); ptrf; ptrg; ptrt)
    SEP (signed62_var_at shf ptrf len f0;
         signed62_var_at shg ptrg len g0;
         trans2x2_at sht ptrt mtx)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_var_at shf ptrf len f1;
         signed62_var_at shg ptrg len g1;
         trans2x2_at sht ptrt mtx).

(* ================================================================= *)
(** ** update_de_limb -- [cd += u*dn+v*en (+mod_n*md); ce += q*dn+r*en (+mod_n*me)]. *)

(** One limb-n step of [secp256k1_modinv64_update_de_62], folding the limb-n
    products of [t*[d,e]+modulus*[md,me]] into the running 128-bit accumulators
    [cd],[ce]. The [mod_n*md],[mod_n*me] terms are added only when [mod_n <> 0].
    The PRE carries the per-accumulation overflow bounds the caller already
    proves, so the body is a straight chain of [i128_accum_mul] calls. *)
Definition spec_secp256k1_modinv64_update_de_limb : ident * funspec :=
  DECLARE _secp256k1_modinv64_update_de_limb
  WITH ptrcd : val, ptrce : val, shcd : share, shce : share,
       cd0 : Int128, ce0 : Int128, u : Int64, v : Int64, q : Int64, r : Int64,
       dn : Int64, en : Int64, md : Int64, me : Int64, mod_n : Int64
  PRE [ tptr t_secp256k1_u128, tptr t_secp256k1_u128,
        tlong, tlong, tlong, tlong, tlong, tlong, tlong, tlong, tlong ]
    PROP (writable_share shcd;
          writable_share shce;
          (* per-accumulation overflow bounds (the [Int64]/[Int128] inputs carry
             their own ranges via [i64_range]/[i128_range], so only the running
             sums need stating -- these are exactly the [i128_accum_mul] PREs) *)
          (-2^127 <= i128_val cd0 + i64_val u * i64_val dn <= 2^127 - 1)%Z;
          (-2^127 <= i128_val cd0 + i64_val u * i64_val dn + i64_val v * i64_val en <= 2^127 - 1)%Z;
          (-2^127 <= i128_val ce0 + i64_val q * i64_val dn <= 2^127 - 1)%Z;
          (-2^127 <= i128_val ce0 + i64_val q * i64_val dn + i64_val r * i64_val en <= 2^127 - 1)%Z;
          (i64_val mod_n <> 0 -> -2^127 <= i128_val cd0 + i64_val u * i64_val dn + i64_val v * i64_val en + i64_val mod_n * i64_val md <= 2^127 - 1)%Z;
          (i64_val mod_n <> 0 -> -2^127 <= i128_val ce0 + i64_val q * i64_val dn + i64_val r * i64_val en + i64_val mod_n * i64_val me <= 2^127 - 1)%Z)
    PARAMS (ptrcd; ptrce; int64_to_val u; int64_to_val v; int64_to_val q;
            int64_to_val r; int64_to_val dn; int64_to_val en;
            int64_to_val md; int64_to_val me; int64_to_val mod_n)
    SEP (i128_at shcd ptrcd cd0;
         i128_at shce ptrce ce0)
  POST [ tvoid ]
    EX cd' : Int128, EX ce' : Int128,
    PROP ((i128_val cd' = i128_val cd0 + i64_val u * i64_val dn + i64_val v * i64_val en
             + (if Z.eqb (i64_val mod_n) 0 then 0 else i64_val mod_n * i64_val md))%Z;
          (i128_val ce' = i128_val ce0 + i64_val q * i64_val dn + i64_val r * i64_val en
             + (if Z.eqb (i64_val mod_n) 0 then 0 else i64_val mod_n * i64_val me))%Z)
    RETURN ()
    SEP (i128_at shcd ptrcd cd';
         i128_at shce ptrce ce').

(* ================================================================= *)
(** ** update_fg_62 -- [(t/2^62) * [f,g]] on a fixed 5 limbs. *)

(** [secp256k1_modinv64_update_fg_62]: apply the divstep transition matrix
    [mtx = (u,v;q,r)] in place to the 5-limb [f,g], computing
    [(mtx * [f,g]) / 2^62] limb by limb -- the fixed 5-limb, fully unrolled
    counterpart of [..._update_fg_62_var] at [len = 5].  Generic in the matrix:
    the result is [reprn 5 ((u*f+v*g)/2^62)] / [reprn 5 ((q*f+r*g)/2^62)] with
    floor division.  (The dropped [VERIFY_CHECK] that the low 62 bits vanish is
    not needed: the C discards them either way, matching floor division.) *)
Definition spec_secp256k1_modinv64_update_fg_62 : ident * funspec :=
  DECLARE _secp256k1_modinv64_update_fg_62
  WITH ff : Z, gg : Z, mtx : divstep_trans.Trans.M2x2,
       ptrf : val, ptrg : val, ptrt : val, shf : share, shg : share, sht : share
  PRE [ tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_signed62,
        tptr t_secp256k1_modinv64_trans2x2 ]
    PROP ((-2^(62 * 5 + 1) <= ff <= 2^(62 * 5 + 1) - 1)%Z;
          (-2^(62 * 5 + 1) <= gg <= 2^(62 * 5 + 1) - 1)%Z;
          divstep_trans.Trans.bounded (2 ^ 62) mtx;
          writable_share shf;
          writable_share shg;
          readable_share sht)
    PARAMS (ptrf; ptrg; ptrt)
    SEP (signed62_at shf ptrf ff;
         signed62_at shg ptrg gg;
         trans2x2_at sht ptrt mtx)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (signed62_at shf ptrf ((divstep_trans.Trans.u mtx * ff + divstep_trans.Trans.v mtx * gg) / 2 ^ 62);
         signed62_at shg ptrg ((divstep_trans.Trans.q mtx * ff + divstep_trans.Trans.r mtx * gg) / 2 ^ 62);
         trans2x2_at sht ptrt mtx).

(* ================================================================= *)
(** ** The module's internal funspec list -- the safegcd divstep stack.

    The signed [i128_*] and [ctz64] helpers these bodies call live in
    [Gprog_int128_impl] / [Gprog_util], so they are not repeated here. *)

Definition Gprog_modinv_impl : funspecs := [
  spec_secp256k1_modinv64_signed62_assign;
  spec_secp256k1_modinv64_normalize_62;
  spec_secp256k1_modinv64_divsteps_62_var;
  spec_secp256k1_modinv64_divsteps_59;
  spec_secp256k1_modinv64_update_de_limb;
  spec_secp256k1_modinv64_update_de_62;
  spec_secp256k1_modinv64_update_fg_62_var;
  spec_secp256k1_modinv64_update_fg_62
].
