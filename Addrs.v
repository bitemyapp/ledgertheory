(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Addrs : Representation of addresses as 160 bit sequences. **)

Require Export Prelude.

Fixpoint bitseq (n:nat) : Type :=
match n with
| 0 => unit
| S n' => (bool * bitseq n')%type
end.

Definition bitseq_eq_dec {n} (bs1 bs2:bitseq n) : { bs1 = bs2 } + { bs1 <> bs2 }.
induction n as [|n IHn].
- destruct bs1, bs2. decide equality.
- destruct bs1 as [b1 bs1], bs2 as [b2 bs2]. repeat decide equality.
Defined.

Definition addr := bitseq 160.

Definition addr_eq_dec (a1 a2: addr) : { a1 = a2 } + { a1 <> a2 }.
apply bitseq_eq_dec.
Defined.

Fixpoint strip_bitseq_false {n:nat} {X:Type} (l:list (bitseq (S n) * X)%type) : list (bitseq n * X)%type :=
match l with
| nil => nil
| cons ((false,bs),x) l' => cons (bs,x) (strip_bitseq_false l')
| cons ((true,bs),x) l' => strip_bitseq_false l'
end.

Fixpoint strip_bitseq_true {n:nat} {X:Type} (l:list (bitseq (S n) * X)%type) : list (bitseq n * X)%type :=
match l with
| nil => nil
| cons ((true,bs),x) l' => cons (bs,x) (strip_bitseq_true l')
| cons ((false,bs),x) l' => strip_bitseq_true l'
end.

Lemma strip_bitseq_false_iff {n} {X} (alpha:bitseq n) (x:X) (l:list (bitseq (S n) * X)%type) :
  In (alpha,x) (strip_bitseq_false l) <-> In ((false,alpha),x) l.
induction l as [|[[[|] beta] y] l IH].
- simpl. tauto.
- simpl. split.
  + intros H1. right. now apply IH.
  + intros [H1|H1].
    * inversion H1.
    * now apply IH.
- simpl. split.
  + intros [H1|H1].
    * left. inversion H1. reflexivity.
    * right. now apply IH.
  + intros [H1|H1].
    * inversion H1. now left.
    * right. now apply IH.
Qed.

Lemma strip_bitseq_true_iff {n} {X} (alpha:bitseq n) (x:X) (l:list (bitseq (S n) * X)%type) :
  In (alpha,x) (strip_bitseq_true l) <-> In ((true,alpha),x) l.
induction l as [|[[[|] beta] y] l IH].
- simpl. tauto.
- simpl. split.
  + intros [H1|H1].
    * left. inversion H1. reflexivity.
    * right. now apply IH.
  + intros [H1|H1].
    * inversion H1. now left.
    * right. now apply IH.
- simpl. split.
  + intros H1. right. now apply IH.
  + intros [H1|H1].
    * inversion H1.
    * now apply IH.
Qed.

