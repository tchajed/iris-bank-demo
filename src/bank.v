(*! A simple demo of ghost state and lock reasoning in Iris *)

(* To compile this demo you'll just need Iris, which can be installed from opam
(follow the instructions in the README: https://gitlab.mpi-sws.org/iris/iris) *)

(* meta point: standard coqdoc syntax uses square brackets to surround Coq code,
like [forall x, x = x]. *)

(* we'll write this demo in HeapLang, a simple ML-like language shipped with
Iris *)
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
(* we'll use this library to set up ghost state later *)
From iris.algebra Require Import lib.excl_auth.

(* set some Coq options for basic sanity *)
Set Default Proof Using "Type".
Set Printing Projections.
Open Scope Z_scope.

(** The idea of this proof is to have a bank that stores user balances in
accounts which are protected by locks. We want to show that in some sense
transfers preserve the sum of balances.

First, we make some radical simplifications to focus on the essential
difficulty: we only have two accounts (but still two locks), and only transfer
from one to the other. The balances are represented as mathematical integers [Z]
and their sum will be 0. We'll also write this code in Iris using just HeapLang
rather than in Go using GooseLang.

The difficulty these simplifications leave is that the balances don't
necessarily sum to zero at any instant in time; to observe their sum is 0, we
have to acquire locks. Thus here we write a program that acquires all (both)
locks and checks that the sum is zero.

We won't prove anything else about the bank functionality or implement anything
else (like reading balances).

 *)

(* some notes on syntax for reading this code:

- ref allocates a new reference with an initial value
- # is the constructor to turn something into a value, for example #0 is an
    integer ([Z]) value, and #() is a unit
- !l dereferences a pointer l (we use "l" for "location")
- many constructs have a colon to disambiguate them from the analogous Coq
  syntax
- this language has no static type system
- [λ: <>, ...] uses <> for an anonymous binder, much like _ in Coq and other
  languages.

 *)

(** new_bank constructs a bank with two accounts that both have zero balance,
which initially satisfies the desired invariant *)
Definition new_bank: val :=
  λ: <>,
     let: "a_bal" := ref #0 in
     let: "b_bal" := ref #0 in
     let: "lk_a" := newlock #() in
     let: "lk_b" := newlock #() in
    (* the bank is represented as a pair of accounts, each of which is a pair of
    a lock and a pointer to its balance *)
     (("lk_a", "a_bal"), ("lk_b", "b_bal")).

(** transfer is what we want to prove safe, but we won't prove that it actually
modifies the bank state correctly because it requires more setup. *)
Definition transfer: val :=
  λ: "bank" "amt",
  let: "a" := Fst "bank" in
  let: "b" := Snd "bank" in
  acquire (Fst "a");;
  acquire (Fst "b");;
  Snd "a" <- !(Snd "a") - "amt";;
  Snd "b" <- !(Snd "b") + "amt";;
  release (Fst "b");;
  release (Fst "a");;
  #().

(** this is the core function of interest: we will prove that even in the
presence of [transfer]s, this function always returns true *)
Definition check_consistency: val :=
  λ: "bank",
  let: "a" := Fst "bank" in
  let: "b" := Snd "bank" in
  acquire (Fst "a");;
  acquire (Fst "b");;
  let: "a_bal" := !(Snd "a") in
  let: "b_bal" := !(Snd "b") in
  let: "ok" := "a_bal" + "b_bal" = #0 in
  release (Fst "b");;
  release (Fst "a");;
  "ok".

(** to tie everything together we'll specifically prove this function returns
true, even though the check races with a transfer. *)
Definition demo_check_consistency: val :=
  λ: <>,
  let: "bank" := new_bank #() in
  Fork (transfer "bank" #5);;
  check_consistency "bank".


(* We'll now switch over to reasoning in the logic.

The syntax for separation logic stuff here includes:
- [P ∗ Q] (note that's a unicode symbol) is separating conjunction. This binds
  weakly so that we don't need parentheses around every conjunct.
- [P -∗ Q] is separating implication (think of it as P implies Q and just
  remember that (P -∗ Q) ∗ P ⊢ Q)
- [⌜φ⌝] embeds a "pure" (Coq) proposition [φ: Prop] into separation logic
- [∃ (x:T), ...] is overloaded to also work within separation logic. This is so
  natural you can easily forget that separation logic and Coq exists aren't the
  same thing.
- [|==> P] uses a "modality" (the [|==>] part) to say that after some change in
  ghost state, it produces resources satisfying P.
*)

Section heap.

  (* to do this proof we need some simple ghost state - the details of the
  construction aren't very important, but we'll explain what properties these
  resources have *)

  (* The two resources are written [own γ (●E a)] and [own γ (◯E a)], where
  [(a:A)] is an element of an arbitrary type. We pronounce the first one
  "authoritative ownership" and the second the "fragmentary ownership", but
  because this is exclusive ownership (represented by the E), these two are
  symmetric. Generally the authoritative goes in an invariant and we hand out
  the fragment in lock invariants and such. There's also a _ghost name_, which
  uses the metavariable [γ], to identify this particular variable.

  We can do three things with these: allocate a pair of them (at any step in the
  proof, since this is ghost state), derive that the fragment and authority
  agree on the same value, and update the variable if we have both *)

  (* Iris has very general support for user-extensible ghost state. We won't
  explain how that works here, so you can ignore the proofs of this library and
  just look at the specs for this particular type of ghost state. Other forms of
  ghost state let you express more complicated protocols and sharing patterns
  between threads. *)

(* you can ignore these; this mini-library is parameterized by a bunch of very
general things *)
Definition ghostR (A: ofeT) := authR (optionUR (exclR A)).
Context {A: ofeT} `{Hequiv: @LeibnizEquiv _ A.(ofe_equiv)} `{Hdiscrete: OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

(* Allocation is an update to ghost state, represented by the [|==>] (the
"update modality"). Basically during a program proof (a WP) we have the right to
do this. *)
Lemma ghost_var_alloc (a: A) :
  ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
Proof using.
  iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
  { apply excl_auth_valid. }
  iModIntro. iExists γ. iFrame.
Qed.

(* This says the two parts agree, written using _separating implication_ (also
pronounced "magic wand" but that obscures its meaning). You can read [-∗]
exactly like [->] and you'll basically have the right intuition. *)
Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (●E a1) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
Proof using All.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %<-%excl_auth_agree%leibniz_equiv.
  done.
Qed.

(* This theorem lets us change ghost state. It requires the right to change
ghost state, this time represented by the [==∗]. Unlike the previous theorem
this consumes the old ownership and gives new resources, having modified the
ghost variable. *)
Lemma ghost_var_update {γ} (a1' a1 a2 : A) :
  own γ (●E a1) -∗ own γ (◯E a2) ==∗
    own γ (●E a1') ∗ own γ (◯E a1').
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E a1' ⋅ ◯E a1') with "Hγ● Hγ◯") as "[$$]".
  { apply excl_auth_update. }
  done.
Qed.

(* it's also true that two auth or fragments for the same ghost name are
contradictory, but we don't need that *)

End heap.

Section heap.

(* mostly standard boilerplate *)
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (ghostR ZO)}.
Let N := nroot.@"bank".

(* We can now talk about [iProp Σ], the type of Iris propositions. This includes
the [own] fact we saw above for ghost resources, [l ↦ v] for the usual points-to
in HeapLang, and all the separation logic connectives. You can ignore the [Σ]
which is there for technical reasons. *)

(** account_inv is the lock invariant associated with each account. It exposes a
ghost name [γ] used to tie the account balance to a ghost variable. *)
Definition account_inv γ bal_ref : iProp Σ :=
  ∃ (bal: Z), bal_ref ↦ #bal ∗ own γ (◯E bal).

(** an account is a pair of a lock and an account protected by the lock *)
Definition is_account (acct: val) γ : iProp Σ :=
  ∃ (bal_ref: loc) lk,
    ⌜acct = (lk, #bal_ref)%V⌝ ∗
    (* The important part of [is_lock] is the lock invariant, expressed as an
    arbitrary Iris proposition [iProp Σ]. The idea of lock invariants is that
    first we associate a lock invariant [P] with the lock (we're doing that
    here). Then when we acquire the lock we get (resources satisfying) [P], and
    when we release it we have to give back (resources satisfying) [P].
    Crucially during the critical section we have access to [P] and can violate
    this proposition freely. *)
    ∃ (γl: gname), is_lock γl lk (account_inv γ bal_ref).

(** bank_inv is the invariant (the usual one that holds at all intermediate
points) that holds the authoritative fragments for the account balances and
importantly states that they are always equal. Any thread can open the invariant
to "read" the logical balances, but modifications must respect the constraint
here.

We need to say where the logical account balances are so this definition also
takes two ghost names.

 *)
Definition bank_inv (γ: gname * gname) : iProp Σ :=
  (* the values in the accounts are arbitrary... *)
  ∃ (bal1 bal2: Z),
     own γ.1 (●E bal1) ∗
     own γ.2 (●E bal2) ∗
     (* ... except that they add up to 0 *)
     ⌜(bal1 + bal2)%Z = 0⌝.

(** finally [is_bank] ties everything together, the accounts and invariant *)
Definition is_bank (b: val): iProp Σ :=
  ∃ (acct1 acct2: val) (γ: gname*gname),
  ⌜b = (acct1, acct2)%V⌝ ∗
  is_account acct1 γ.1 ∗
  is_account acct2 γ.2 ∗
  inv N (bank_inv γ).

(* Importantly [is_bank b] is _persistent_, which means we can share it among
threads. We'll see this used in [wp_demo_check_consistency].

This proofs goes through because the components of [is_bank] are persistent.
These include the pure facts (it should be intuitive that these are persistent,
since they don't talk about resources at all), the invariant (because [inv N P]
is just knowledge of an invariant, which can and should be shared) and [is_lock
γl lk P] (similarly, this is knowledge that there is a lock at lk and is
shareable) *)
Instance is_bank_Persistent b : Persistent (is_bank b).
Proof. apply _. (* this proof is actually automatic *) Qed.

(* [new_bank] is actually interesting because we have to create all the ghost
state, lock invariants, and invariant, and of course when you create an
invariant holding [P] you have to prove [P].

These ghost operations correspond to [iMod] in these proofs, which uses theorems
with [|==>] and [==∗]. *)
Theorem wp_new_bank :
  (* This is a Hoare triple using Iris's program logic. *)
  {{{ True }}}
    new_bank #()
    (* the [b,] part is a shorthand for [∃ b, ...] in the postcondition, and RET
    b says the function returns b. *)
  {{{ b, RET b; is_bank b }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_alloc a_ref as "Ha".
  wp_alloc b_ref as "Hb".
  iMod (ghost_var_alloc (0: ZO)) as (γ1) "(Hown1&Hγ1)".
  wp_apply (newlock_spec (account_inv γ1 a_ref) with "[Ha Hγ1]").
  { iExists _; iFrame. }
  iIntros (lk_a γlk1) "Hlk1".
  iMod (ghost_var_alloc (0: ZO)) as (γ2) "(Hown2&Hγ2)".
  wp_apply (newlock_spec (account_inv γ2 b_ref) with "[Hb Hγ2]").
  { iExists _; iFrame. }
  iIntros (lk_b γlk2) "Hlk2".
  iMod (inv_alloc N _ (bank_inv (γ1,γ2)) with "[Hown1 Hown2]") as "Hinv".
  { iNext. iExists _, _; iFrame.
    iPureIntro; auto. }
  wp_pures.
  iApply "HΦ".
  iExists _, _, (γ1,γ2); iFrame.
  iSplit; first eauto.
  simpl.
  iSplitL "Hlk1".
  - iExists _; eauto with iFrame.
  - iExists _; eauto with iFrame.
Qed.

(** As mentioned above, we don't prove anything except for safety for
[transfer]. This still has to prove that we follow the lock invariants and
global invariant - after [is_bank] is created we can no longer add to a single
account, for example.

You might expect because this is separation logic that we should return [is_bank
b] here. It turns out we don't need to since the fact is persistent, so the
caller will never lose this fact. *)
Theorem wp_transfer b (amt: Z) :
  {{{ is_bank b }}}
    transfer b #amt
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hb HΦ".
  (* breaking apart the above definitions is really quite painful - I have
  better infrastructure for this in Perennial but it isn't quite ready for this
  example and would be annoying to import here *)
  iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
  iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
  iDestruct "Hlk" as (γl1) "Hlk1".
  iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
  iDestruct "Hlk" as (γl2) "Hlk2".
  wp_rec.
  wp_pures.
  wp_apply (acquire_spec with "Hlk1").
  iIntros "(Hlocked1&Haccount1)".
  wp_apply (acquire_spec with "Hlk2").
  iIntros "(Hlocked2&Haccount2)".
  iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
  iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)".

  (* If you look at the proof goal now, there are a bunch of things going on.
  The Iris Proof Mode (IPM) embeds a separation logic context within the Coq
  goal. This means we have the Coq context and the IPM context. Furthermore, it

  actually uses two contexts: a persistent context (which comes first and is
  separated by ---------□) of facts that are duplicable and thus don't go away
  when we need to split, and then a spatial context (separated by ---------∗) of
  ordinary spatial premises. The IPM view and tactics let us manipulate these in
  a way similar to how Coq hypotheses work, making proofs in separation logic as
  easy as normal Coq proofs (sort of - separation logic does add some
  difficulties to proofs that are fundamental). Learning these tactics is a lot
  like learning how to do Coq proofs all over again (that is, you need to do it
  but it's not that hard and you do get used to it). *)

  (* this steps through the critical section *)
  wp_pures; wp_load; wp_pures; wp_store; wp_pures.
  wp_pures; wp_load; wp_pures; wp_store; wp_pures.

  (* Now the physical state is updated but not the logical balances in ghost
  state. In order to restore the lock invariant, we have to do that, and this
  requires using the invariant with [iInv]. *)
  rewrite -fupd_wp. (* we need to do this for iInv to work *)
  (* iInv opens the invariant for us and also takes a pattern to destruct the
  resulting [bank_inv γ] right away. You can see that it gives us resources in
  the context but also adds [bank_inv] to the goal, since this invariant needs
  to hold at all points. *)
  iInv "Hinv" as (bal1' bal2') ">(Hγ1&Hγ2&%)".
  (* we use the agreement and update theorems above for these ghost variables *)
  iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
  iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
  iMod (ghost_var_update (bal1-amt) with "Hγ1 Hown1") as "(Hγ1&Hown1)".
  iMod (ghost_var_update (bal2+amt) with "Hγ2 Hown2") as "(Hγ2&Hown2)".
  iModIntro.
  (* we can't just modify ghost state however we want - to continue, [iInv]
  added [bank_inv] to our goal to prove, requiring us to restore the
  invariant *)
  iSplitL "Hγ1 Hγ2".
  { iNext. iExists _, _; iFrame.
    iPureIntro.
    lia. }
  iModIntro.

  (* We've done all the hard work of maintaining the invariant and updating the
  ghost variables to their new values.

  Now we'll be able to release both locks (in any order, actually) by
  re-proving their lock invariants, with the new values of the ghost
  variables. *)
  wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  by iApply "HΦ".
Qed.

(** we're able to prove that [check_consistency] always returns true, using the
protocol established by [is_bank]. *)
Theorem wp_check_consistency b :
  {{{ is_bank b }}}
     check_consistency b
  {{{ RET #true; True }}}.
Proof.
  (* most of this proof is the same: open everything up and acquire the locks,
  then open the lock invariants up *)
  iIntros (Φ) "#Hb HΦ".
  iDestruct "Hb" as (acct1 acct2 γ ->) "(Hacct1&Hacct2&Hinv)".
  iDestruct "Hacct1" as (bal_ref1 lk1 ->) "Hlk".
  iDestruct "Hlk" as (γl1) "Hlk1".
  iDestruct "Hacct2" as (bal_ref2 lk ->) "Hlk".
  iDestruct "Hlk" as (γl2) "Hlk2".
  wp_rec.
  wp_pures.
  wp_apply (acquire_spec with "Hlk1").
  iIntros "(Hlocked1&Haccount1)".
  wp_apply (acquire_spec with "Hlk2").
  iIntros "(Hlocked2&Haccount2)".
  iDestruct "Haccount1" as (bal1) "(Hbal1&Hown1)".
  iDestruct "Haccount2" as (bal2) "(Hbal2&Hown2)".

  (* the critical section is easy *)
  wp_pures; wp_load.
  wp_pures; wp_load.
  wp_pures.

  (* Now we need to prove something about our return value using information
  derived from the invariant. As before we'll open the invariant, but this time
  we don't need to modify anything, just extract a pure fact. *)
  rewrite -fupd_wp.
  iInv N as (bal1' bal2') ">(Hγ1 & Hγ2 & %)". (* the [%] here is the pure fact, actually *)
  iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
  iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
  iModIntro.
  iSplitL "Hγ1 Hγ2".
  { iNext. iExists _, _; iFrame.
    iPureIntro.
    lia. }
  iModIntro.

  wp_apply (release_spec with "[$Hlk2 $Hlocked2 Hbal2 Hown2]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_apply (release_spec with "[$Hlk1 $Hlocked1 Hbal1 Hown1]").
  { iExists _; iFrame. }
  iIntros "_".
  wp_pures.
  (* the calculation always returns true because of a fact we got from the
  invariant *)
  rewrite bool_decide_eq_true_2; last first.
  { congruence. }
  by iApply "HΦ".
Qed.

(* [demo_check_consistency] lets us tie everything together in a theorem that
has no assumptions. It's pretty easy to believe that this theorem implies that
if [demo_check_consistency] terminates, it returns true, which implies the
consistency check works at least with one concurrent transfer. *)
Theorem wp_demo_check_consistency :
  {{{ True }}}
    demo_check_consistency #()
  {{{ RET #true; True }}}.
Proof using All.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply wp_new_bank; first auto.
  (* we use [#Hb] to put the newly created [is_bank] in the "persistent context"
  in the Iris Proof Mode - these are persistent facts and thus are available
  even when we need to split to prove a separating conjunction *)
  iIntros (b) "#Hb".
  (* the proof is easy now - the fork rule requires us to split the context and
  prove any Hoare triple for the forked thread. [transfer] only needs [Hb], but
  that's persistent and will thus be available. We've coincidentally already
  proven a triple for it with a postcondition of [True]. *)
  wp_apply wp_fork.
  - wp_apply (wp_transfer with "Hb").
    auto.
  - (* [check_consistency] always returns true, using [is_bank] *)
    wp_apply (wp_check_consistency with "Hb").
    iIntros "_".
    by iApply "HΦ".
Qed.

End heap.
