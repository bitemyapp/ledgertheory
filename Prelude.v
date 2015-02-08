(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Prelude: Import parts of Coq's library and add a few extras. **)

Require Export Coq.Lists.List.
Require Export Coq.Arith.Peano_dec.
Require Export omega.Omega.

Lemma nth_error_In {X:Type} (l:list X) (i:nat) (x:X) :
  nth_error l i = value x -> In x l.
revert i. induction l as [|y l IH]; intros [|i].
- intros H1. discriminate H1.
- intros H1. discriminate H1.
- intros H1. inversion H1. now left.
- intros H1. right. apply (IH i). exact H1.
Qed.

Lemma nth_error_app {X:Type} (l r:list X) (i:nat) (x:X) :
  nth_error (l ++ r) i = value x ->
  nth_error l i = value x \/ exists j, i = length l + j /\ nth_error r j = value x.
revert i. induction l as [|y l IH].
- simpl. intros i H1. right. exists i. tauto.
- intros [|i]; simpl.
  + intros H1. now left.
  + intros H1. destruct (IH i H1) as [H2|[j [H2 H3]]].
    * now left.
    * { right. exists j. split.
        - congruence.
        - exact H3.
      }
Qed.

Fixpoint In_dom {X Y:Type} (x : X) (xyl : list (X * Y)) : Prop :=
match xyl with
| nil => False
| cons (x',_) xyl' => x = x' \/ In_dom x xyl'
end.

Lemma In_In_dom_lem {X Y:Type} (x : X) (xyl : list (X * Y)) :
  In_dom x xyl <-> exists y:Y, In (x,y) xyl.
induction xyl as [|[x' y'] l' [IH1 IH2]].
- simpl. split.
  + tauto.
  + intros [y []].
- simpl. split.
  + intros [H1|H1].
    * subst x. exists y'. tauto.
    * destruct (IH1 H1) as [y H2]. exists y. tauto.
  + intros [y [H1|H1]].
    * inversion H1. tauto.
    * right. apply IH2. exists y. assumption.
Qed.

Lemma In_In_dom_lem_2 {X Y:Type} (x : X) (y : Y) (xyl : list (X * Y)) :
  In (x,y) xyl -> In_dom x xyl.
intros H. apply In_In_dom_lem. exists y. exact H.
Qed.

Inductive no_dups {X:Type} : list X -> Prop :=
| no_dups_nil : no_dups nil
| no_dups_cons x l : ~ In x l -> no_dups l -> no_dups (x::l)
.

Inductive fnl {X Y:Type} : list (X * Y) -> Prop :=
| fnl_N : fnl nil
| fnl_C x y l : ~ In_dom x l -> fnl l -> fnl (cons (x,y) l)
.

Lemma fnl_lem {X Y:Type} (l:list (X * Y)) :
  fnl l -> forall x y z, In (x,y) l -> In (x,z) l -> y = z.
intros H. induction H as [|w v l H1 H2 IH].
- intros x y z [].
- intros x y z [H3|H3] [H4|H4].
  + inversion H3. inversion H4. congruence.
  + exfalso. apply In_In_dom_lem_2 in H4. inversion H3. congruence.
  + exfalso. apply In_In_dom_lem_2 in H3. inversion H4. congruence.
  + revert H3 H4. apply IH.
Qed.

Inductive app_perm {X:Type} : list X -> list X -> Prop :=
| app_perm_swap l r : app_perm (l ++ r) (r ++ l)
| app_perm_app l1 r1 l2 r2 : app_perm l1 r1 -> app_perm l2 r2 -> app_perm (l1 ++ l2) (r1 ++ r2)
| app_perm_ref l : app_perm l l
| app_perm_sym l r : app_perm l r -> app_perm r l
| app_perm_tra l r s : app_perm l r -> app_perm r s -> app_perm l s
.

Lemma no_dups_app {X:Type} (l r:list X) :
no_dups l -> no_dups r -> (forall x, In x l -> ~In x r) -> no_dups (l ++ r).
intros H H1. induction H as [|x l H2 H3 IH].
- simpl. tauto.
- intros H4. simpl. apply no_dups_cons.
  + intros H5. apply in_app_iff in H5. destruct H5 as [H5|H5].
    * contradiction.
    * revert H5. apply H4. now left.
  + apply IH. intros y H5. apply H4. now right.
Qed.

Lemma fnl_app {X Y:Type} (l r:list (prod X Y)) :
fnl l -> fnl r -> (forall x, In_dom x l -> ~In_dom x r) -> fnl (l ++ r).
intros H H1. induction H as [|x y l H2 H3 IH].
- simpl. tauto.
- intros H4. simpl. apply fnl_C.
  + intros H5. apply In_In_dom_lem in H5. destruct H5 as [z H5].
    apply in_app_iff in H5. destruct H5 as [H5|H5].
    * apply H2. now apply (In_In_dom_lem_2 x z).
    * apply In_In_dom_lem_2 in H5. revert H5. apply H4. now left.
  + apply IH. intros z H5. apply H4. now right.
Qed.


