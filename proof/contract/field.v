(** * contract.field: representation predicate + funspecs for the field subsystem. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: MIT *)

(** The field's lazy-reduction discipline lives here: [fe_repr m v ls] says the C
    limb list [ls] is a magnitude-[m] representation of the residue [v].  The
    [model.field] value [Fe] is just [v] (the residue); the magnitude [m] and the
    raw limbs [ls] are representation detail, never part of the model value. *)

Require Import secp256k1.vst.base.
Require Import secp256k1.theory.arithmetic.
Require Import secp256k1.theory.field.field_bits.
Require Import secp256k1.contract.helper.structs_field.
Require Import secp256k1.model.field.
Require Import secp256k1.contract.helper.notations.

(* ================================================================= *)
(** ** Field representation bridge -- [fe_to_val] / [fe_at].

    Subsystem-owned (the convention: each subsystem's contract file carries its
    own representation bridges + [_at] notations; [contract/helper/{repr,
    notations}] stay frozen to the machine words + bytes). *)

(** Represent the limbs of a [secp256k1_fe] (the [n[5]] array of the one-field
    struct, [reptype = list val]).  Unlike [scalar_to_val], a field element's
    stored limbs are NOT a function of its residue: an un-normalized magnitude-m
    element has limbs exceeding [2^52].  So this carries the actual limb list and
    the value/magnitude tie-in is a side-condition ([fe_repr] in contract/field). *)
Definition fe_to_val (ls : list Z) : list val :=
  map (fun l => Vlong (Int64.repr l)) ls.

(** Per-limb bridge for [fe_to_val]: reading the [i]-th C limb yields the stored
    limb value.  Trivial (it is a [map]), but lets [forward] on an [n[i]] load
    rewrite the loaded value in one step. *)
Lemma fe_to_val_Znth : forall (ls : list Z) i,
  0 <= i < Zlength ls ->
  Znth i (fe_to_val ls) = Vlong (Int64.repr (Znth i ls)).
Proof. intros ls i Hi. unfold fe_to_val. rewrite Znth_map by lia. reflexivity. Qed.

(** A [secp256k1_fe] holding the limb list [ls] (the one-field [{ uint64 n[5] }]
    struct; [reptype = list val], so [fe_to_val ls] is its [data_at] value). *)
Notation "'fe_at' sh p ls" :=
  (data_at sh t_secp256k1_fe (fe_to_val ls) p)
  (at level 20, sh at level 0, p at level 0, ls at level 0).
Notation "'fe_at_' sh p" :=
  (data_at_ sh t_secp256k1_fe p)
  (at level 20, sh at level 0, p at level 0).


(* ================================================================= *)
(** ** Representation predicate. *)

(** [fe_repr m v ls]: [ls] is a 5-limb (base [2^52]) magnitude-[m] encoding whose
    evaluation is the residue [v].  Limb [i] is bounded by [fe_limb_mag_bound m i]
    (limbs 0..3 by [2*m*(2^52-1)], limb 4 by [2*m*(2^48-1)]). *)
Definition fe_repr (m v : Z) (ls : list Z) : Prop :=
  Zlength ls = 5 /\
  (forall i, 0 <= i < 5 ->
     0 <= Znth i ls <= fe_limb_mag_bound m (Z.to_nat i)) /\
  eval5 (2 ^ 52) (Znth 0 ls) (Znth 1 ls) (Znth 2 ls) (Znth 3 ls) (Znth 4 ls)
    mod secp256k1_P = v.

(* ================================================================= *)
(** ** Funspecs. *)

(** [secp256k1_fe_add] (= leaf [secp256k1_fe_impl_add] when VERIFY-off): the
    carry-free [r += a].  Magnitudes add ([mr + ma], capped at 32 -- the
    VERIFY-only check that keeps each limb sum below [2^64]); the residue becomes
    [(vr + va) mod p].  The [alias] flag covers the in-place doubling [fe_add(r,r)],
    where the single object [r] supplies both operands (so [la = lr], etc.). *)
Definition spec_secp256k1_fe_impl_add : ident * funspec :=
  DECLARE _secp256k1_fe_impl_add
  WITH r_ptr : val, a_ptr : val, lr : list Z, la : list Z,
       mr : Z, ma : Z, vr : Z, va : Z,
       sh_r : share, sh_a : share, alias : bool
  PRE [ tptr t_secp256k1_fe, tptr t_secp256k1_fe ]
    PROP (writable_share sh_r;
          (0 <= mr)%Z;
          (0 <= ma)%Z;
          (mr + ma <= 32)%Z;
          fe_repr mr vr lr;
          fe_repr ma va la;
          alias = true -> (a_ptr = r_ptr /\ la = lr /\ ma = mr /\ va = vr);
          alias = false -> readable_share sh_a)
    PARAMS (r_ptr; a_ptr)
    SEP (if alias
         then fe_at sh_r r_ptr lr
         else (fe_at sh_r r_ptr lr * fe_at sh_a a_ptr la))
  POST [ tvoid ]
    EX ls : list Z,
    PROP (fe_repr (Z.add mr ma) (Z.modulo (Z.add vr va) secp256k1_P) ls;
          forall i, (0 <= i < 5)%Z ->
            Znth i ls = Z.add (Znth i lr) (Znth i la))
    RETURN ()
    SEP (if alias
         then fe_at sh_r r_ptr ls
         else (fe_at sh_r r_ptr ls * fe_at sh_a a_ptr la)).
