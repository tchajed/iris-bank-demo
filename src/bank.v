(*! A simple demo of ghost state and lock reasoning in Iris *)

(* To compile this demo you'll just need Iris, which can be installed from opam
(follow the instructions in the README: https://gitlab.mpi-sws.org/iris/iris) *)

(* meta point: standard coqdoc syntax uses square brackets to surround Coq code,
like [forall x, x = x]. *)

(* we'll write this demo in HeapLang, a simple ML-like language shipped with
Iris *)
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock spin_lock.
(* Ghost state in Iris can be from any resource algebra (for experts: yes, the
story is a little more complicated than that). This proof will use an extremely
simple form of ghost state, from excl_auth. *)
From iris.algebra Require Import lib.excl_auth.

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
- ! dereferences
- many constructs have a colon to disambiguate them from the analogous Coq
  syntax
- this language has no static type system

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

(** transfer is what we want to prove safe, but we won't do anything to prove
that this function does anything interesting since that requires more setup in
the concurrent setting *)
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

Definition ghostR (A: ofeT) := authR (optionUR (exclR A)).
Context {A: ofeT} `{Hequiv: @LeibnizEquiv _ A.(ofe_equiv)} `{Hdiscrete: OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

(* Allocation is an update to ghost state, represented by the [|==>]. Basically
during a program proof (a WP) we have the right to do this. *)
Lemma ghost_var_alloc (a: A) :
  ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
Proof using.
  iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
  { apply excl_auth_valid. }
  iModIntro. iExists γ. iFrame.
Qed.

(* This says the two parts agree, written using _separating implication_ (also
pronounced "magic wand" but that obscures its meaning). Because the conclusion
is persistent (roughly, it consumes no resources / is duplicable, though neither
is these is exactly correcy), applying this theorem will not consume the inputs
even though in general that's what happens in separation logic. *)
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
which is there for technical reasons.

The syntax for separation logic stuff here includes:
- [P ∗ Q] (note that's a unicode symbol) is separating conjunction. This binds
  weakly so that we don't need parentheses around every conjunct.
- [P -∗ Q] is separating implication (think of it as P implies Q and just
  remember that (P -∗ Q) ∗ Q ⊢ Q)
- [⌜φ⌝] embeds a "pure" (Coq) proposition [φ: Prop] into separation logic
- [∃ (x:T), ...] is overloaded to also work within separation logic. This is so
  natural you can easily forget that separation logic and Coq exists aren't the
  same thing.

 *)

(** account_inv is the lock invariant associated with each account. It exposes a
ghost name [γ] used to tie the account balance to a ghost variable. *)
Definition account_inv γ bal_ref : iProp Σ :=
  ∃ (bal: Z), bal_ref ↦ #bal ∗ own γ (◯E bal).

(** an account is a pair of a lock and an account protected by the lock *)
Definition is_account (acct: val) γ : iProp Σ :=
  ∃ (bal_ref: loc) lk,
    ⌜acct = (lk, #bal_ref)%V⌝ ∗
    (* the important part of [is_lock] is the lock invariant, expressed as an
    arbitrary Iris proposition [iProp Σ]. *)
    ∃ (γl: gname), is_lock γl lk (account_inv γ bal_ref).

Record ghost_names :=
  mkNames {
    acct1_name: gname;
    acct2_name: gname;
  }.

(** bank_inv is the invariant (the usual one that holds at all intermediate
points) that holds the authoritative fragments for the account balances and
importantly states that they are always equal. Any thread can open the invariant
to "read" the logical balances, but modifications must respect the constraint
here.

We need to say where the logical account balances are so this has a record with
their two ghost names.

 *)
Definition bank_inv (γ: ghost_names) : iProp Σ :=
  (* the values in the accounts are arbitrary... *)
  ∃ (bal1 bal2: Z),
     own γ.(acct1_name) (●E bal1) ∗
     own γ.(acct2_name) (●E bal2) ∗
     (* ... except that they add up to 0 *)
     ⌜(bal1 + bal2)%Z = 0⌝.

(** finally [is_bank] ties everything together, the accounts and invariant *)
Definition is_bank (b: val): iProp Σ :=
  ∃ (acct1 acct2: val) (γ: ghost_names),
  ⌜b = (acct1, acct2)%V⌝ ∗
  is_account acct1 γ.(acct1_name) ∗
  is_account acct2 γ.(acct2_name) ∗
  inv N (bank_inv γ).

(* Importantly [is_bank b] is _persistent_, which means we can share it among
threads. We'll see this used in [wp_demo_check_consistency]. *)
Instance is_bank_Persistent b : Persistent (is_bank b).
Proof. apply _. (* this proof is actually automatic *) Qed.

(* [new_bank] is actually interesting because we have to create all the ghost
state, lock invariants, and invariant, and of course when you create an
invariant holding [P] you have to prove [P].

These ghost operations correspond to [iMod] in these proofs, which uses theorems
with [|==>] and [==∗]. *)
Theorem wp_new_bank :
  {{{ True }}}
    new_bank #()
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
  set (γ:=mkNames γ1 γ2).
  iMod (inv_alloc N _ (bank_inv γ) with "[Hown1 Hown2]") as "Hinv".
  { iNext. iExists _, _; iFrame.
    iPureIntro; auto. }
  wp_pures.
  iApply "HΦ".
  iExists _, _, γ; iFrame.
  iSplit; first eauto.
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

  (* this steps through the critical section *)
  wp_pures; wp_load; wp_pures; wp_store; wp_pures.
  wp_pures; wp_load; wp_pures; wp_store; wp_pures.

  (* Now the physical state is updated but not the logical balances in ghost
  state. In order to restore the lock invariant, we have to do that, and this
  requires using the invariant with [iInv]. *)
  rewrite -fupd_wp.
  iInv N as (bal1' bal2') ">(Hγ1&Hγ2&%)".
  (* we use the agreement and update theorems above for these ghost variables *)
  iDestruct (ghost_var_agree with "Hγ1 [$]") as %->.
  iDestruct (ghost_var_agree with "Hγ2 [$]") as %->.
  iMod (ghost_var_update (bal1-amt) with "Hγ1 Hown1") as "(Hγ1&Hown1)".
  iMod (ghost_var_update (bal2+amt) with "Hγ2 Hown2") as "(Hγ2&Hown2)".
  iModIntro.
  (* now we have to re-prove the invariant to continue *)
  iSplitL "Hγ1 Hγ2".
  { iNext. iExists _, _; iFrame.
    iPureIntro.
    lia. }
  iModIntro.

  (* Now we'll be able to release both locks (in any order, actually) by
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
