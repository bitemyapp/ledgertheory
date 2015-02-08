(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** CTreeGrafting: A cgraft describes how to extend a ctree to a better approximation.
    The purpose is so that a small ctree can be given in the block header and
    the graft to extend it to a larger ctree can be given in the block delta without
    repeating the ctree information in the header.
 **)

Require Export CTrees.

(***
A "cgraft" can be used to extend a ctree to be a better approximation without repeating the part that is known.
The idea is to use this to put just what's needed in the block header
(enough of an approx to support the coinstake tx)
and then a graft of the extra part that's needed in the block delta.
***)
Definition cgraft : Type := list (prod hashval (sigT ctree)).

Fixpoint cgraft_valid (G:cgraft) : Prop :=
match G with
| nil => True
| (h,existT n T)::G' => ctree_hashroot T = h /\ cgraft_valid G'
end.

(*** Coercion needed due to dependent types ***)
Definition eqnat_coerce_ctree (m n:nat) (E:m = n) (T:ctree m) : ctree n :=
eq_rect m ctree T n E.

(***
The dependent types here are a little tricky.
I could omit m from the input return (existT n T) where T, leaving the caller of the function to check if m = n (which it should).
Instead I decided to do it here. Either way a coercion using the proof of the equation seems to be needed.
***)
Fixpoint cgraft_assoc (G:cgraft) (k:hashval) (m:nat) : ctree m :=
match G with
| nil => ctreeH m k
| (h,existT n T)::G' =>
  if hashval_eq_dec h k then
    match eq_nat_dec n m with
      | left E => eqnat_coerce_ctree n m E T
      | _ => ctreeH m k
    end
  else
    cgraft_assoc G' k m
end.

Lemma cgraft_assoc_hashroot (G:cgraft) (k:hashval) (m:nat) :
  cgraft_valid G ->
  ctree_hashroot (cgraft_assoc G k m) = k.
induction G as [|[h [n T]] G' IH].
- intros _. destruct m; reflexivity.
- simpl. intros [H1 H2]. destruct (hashval_eq_dec h k) as [E1|E1].
  + destruct (eq_nat_dec n m) as [E2|E2].
    * destruct E2. simpl. (*** tricky ***)
      rewrite <- E1. exact H1.
    * destruct m; reflexivity. (*** even though this is impossible (since if ctree m and ctree n have the same hashroot, m should equal n) the proof goes through. ***)
  + exact (IH H2).
Qed.

Lemma cgraft_assoc_subqc (G:cgraft) (k:hashval) (m:nat) :
  cgraft_valid G -> subqc (ctreeH m k) (cgraft_assoc G k m).
intros H1. generalize (cgraft_assoc_hashroot G k m H1). intros H2.
destruct m as [|m].
- simpl. unfold subqc. unfold subqm. apply subqhH.
  change (mtree_hashroot (ctree_mtree (cgraft_assoc G k 0)) = Some k).
  rewrite mtree_hashroot_ctree_hashroot. congruence.
- unfold subqc.
  change (subqm (mtreeH m (Some k)) (ctree_mtree (cgraft_assoc G k (S m)))).
  change (mtree_hashroot (ctree_mtree (cgraft_assoc G k (S m))) = mtree_hashroot (mtreeH m (Some k))).
  change (mtree_hashroot (ctree_mtree (cgraft_assoc G k (S m))) = Some k).
  rewrite mtree_hashroot_ctree_hashroot. congruence.
Qed.

Fixpoint ctree_cgraft (G:cgraft) {n} : ctree n -> ctree n :=
match n with
| O => fun T:ctree 0 =>
         match T with
           | inl h => cgraft_assoc G h 0
           | _ => T
         end
| S n => fun T:ctree (S n) =>
           match T with
             | inr (inl h) => cgraft_assoc G h (S n)
             | inr (inr (inl Tl)) => ctreeBL (ctree_cgraft G Tl)
             | inr (inr (inr (inl Tr))) => ctreeBR (ctree_cgraft G Tr)
             | inr (inr (inr (inr (Tl,Tr)))) => ctreeB (ctree_cgraft G Tl) (ctree_cgraft G Tr)
             | _ => T
           end
end.

Theorem ctree_cgraft_subqc (G:cgraft) {n} (T:ctree n) :
  cgraft_valid G -> subqc T (ctree_cgraft G T).
intros H1. induction n as [|n IH].
- destruct T as [h|[a hl]].
  + simpl.
    change (subqc (ctreeH 0 h) (cgraft_assoc G h 0)).
    now apply cgraft_assoc_subqc.
  + apply subqm_ref.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + apply subqm_ref.
  + change (subqc (ctreeH (S n) h) (cgraft_assoc G h (S n))).
    now apply cgraft_assoc_subqc.
  + split.
    * apply IH.
    * apply subqm_ref.
  + split.
    * apply subqm_ref.
    * apply IH.
  + split.
    * apply IH.
    * apply IH.
Qed.

Transparent ctree_mtree.

Theorem ctree_approx_fun_cgraft_valid (G:cgraft) {n} (T:ctree n) (f:bitseq n -> list asset) :
  cgraft_valid G ->
  octree_approx_fun_p (Some T) f ->
  octree_approx_fun_p (Some (ctree_cgraft G T)) f.
intros HG.
induction n as [|n IH].
- destruct T as [h|[h hl]].
  + unfold octree_approx_fun_p. simpl. intros H1.
    rewrite H1.
    generalize (cgraft_assoc_hashroot G h 0 HG).
    destruct (cgraft_assoc G h 0) as [k|[k kl]].
    * simpl. congruence.
    * simpl. destruct (hlist_hashroot kl); congruence.
  + simpl. tauto.
- destruct T as [[gamma hl]|[h|[Tl|[Tr|[Tl Tr]]]]].
  + simpl. tauto.
  + unfold octree_approx_fun_p.
    intros [Tl [Tr [H1 [H2 H3]]]].
    unfold ctree_cgraft.
    generalize (cgraft_assoc_hashroot G h (S n) HG).
    intros H4.
    destruct (cgraft_assoc G h (S n)) as [[[[|] delta] kl]|[k|[Tl'|[Tr'|[Tl' Tr']]]]].
    * { simpl. simpl in H4.
        destruct (mtree_hashroot Tl) as [hl|] eqn:E1;
          destruct (mtree_hashroot Tr) as [hr|] eqn:E2;
          simpl in H1.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [_ H4].
          split.
          + apply (mtree_hashroot_mtree_approx_fun_p Tl).
            * rewrite mtree_hashroot_empty. exact E1.
            * exact H2.
          + apply (mtree_hashroot_mtree_approx_fun_p Tr).
            * assert (L1: mtree_hashroot Tr = mtree_hashroot (ctree_mtree (ctreeL kl delta))).
              { rewrite mtree_hashroot_ctree_hashroot.
                congruence.
              }
              destruct n; exact L1.
            * exact H3.
        - discriminate H1.
      }
    * { simpl. simpl in H4.
        destruct (mtree_hashroot Tl) as [hl|] eqn:E1;
          destruct (mtree_hashroot Tr) as [hr|] eqn:E2;
          simpl in H1.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [_ H4].
          split.
          + apply (mtree_hashroot_mtree_approx_fun_p Tl).
            * assert (L1: mtree_hashroot Tl = mtree_hashroot (ctree_mtree (ctreeL kl delta))).
              { rewrite mtree_hashroot_ctree_hashroot.
                congruence.
              }
              destruct n; exact L1.
            * exact H2.
          + apply (mtree_hashroot_mtree_approx_fun_p Tr).
            * rewrite mtree_hashroot_empty. exact E2.
            * exact H3.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - discriminate H1.
      }
    * { simpl. exists Tl. exists Tr. simpl in H4. subst k. repeat split.
        - exact H1.
        - exact H2.
        - exact H3.
      }
    * { simpl. simpl in H4.
        destruct (mtree_hashroot Tl) as [hl|] eqn:E1;
          destruct (mtree_hashroot Tr) as [hr|] eqn:E2;
          simpl in H1.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [_ H4].
          split.
          + apply (mtree_hashroot_mtree_approx_fun_p Tl).
            * rewrite mtree_hashroot_ctree_hashroot. congruence.
            * exact H2.
          + apply (mtree_hashroot_mtree_approx_fun_p Tr).
            * rewrite mtree_hashroot_empty. exact E2.
            * exact H3.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - exfalso. discriminate H1.
      }
    * { simpl. simpl in H4.
        destruct (mtree_hashroot Tl) as [hl|] eqn:E1;
          destruct (mtree_hashroot Tr) as [hr|] eqn:E2;
          simpl in H1.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [_ H4].
          split.
          + apply (mtree_hashroot_mtree_approx_fun_p Tl).
            * rewrite mtree_hashroot_empty. exact E1.
            * exact H2.
          + apply (mtree_hashroot_mtree_approx_fun_p Tr).
            * rewrite mtree_hashroot_ctree_hashroot. congruence.
            * exact H3.
        - discriminate H1.
      }
    * { simpl. simpl in H4.
        destruct (mtree_hashroot Tl) as [hl|] eqn:E1;
          destruct (mtree_hashroot Tr) as [hr|] eqn:E2;
          simpl in H1.
        - inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [_ H4].
          apply hashpairinj in H4. destruct H4 as [H4a H4].
          apply hashpairinj in H4. destruct H4 as [H4b _].
          split.
          + apply (mtree_hashroot_mtree_approx_fun_p Tl).
            * rewrite mtree_hashroot_ctree_hashroot. congruence.
            * exact H2.
          + apply (mtree_hashroot_mtree_approx_fun_p Tr).
            * rewrite mtree_hashroot_ctree_hashroot. congruence.
            * exact H3.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - exfalso. inversion H1. rewrite H0 in H4.
          apply hashpairinj in H4. destruct H4 as [H4 _].
          apply hashnatinj in H4. omega.
        - discriminate H1.
      }
  + intros [H1 H2]. split.
    * apply IH. exact H1.
    * exact H2.
  + intros [H1 H2]. split.
    * exact H1.
    * apply IH. exact H2.
  + intros [H1 H2]. split.
    * apply IH. exact H1.
    * apply IH. exact H2.
Qed.

Opaque ctree_cgraft.
Opaque cgraft_valid.
Opaque ctree_mtree.
Opaque mtree_approx_fun_p.

Theorem ctree_valid_cgraft_valid (G:cgraft) (T:ctree 160) :
  ctree_valid T ->
  cgraft_valid G ->
  ctree_valid (ctree_cgraft G T).
intros [f [H1 H2]] HG.
exists f. split.
- exact H1.
- assert (L1: octree_approx_fun_p (Some (ctree_cgraft G T)) f).
  { apply ctree_approx_fun_cgraft_valid.
    - exact HG.
    - unfold octree_approx_fun_p. unfold octree_mtree. exact H2.
  }
  unfold octree_approx_fun_p in L1. unfold octree_mtree in L1.
  exact L1.
Qed.
