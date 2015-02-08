(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** LedgerStates: States are represented here as ledger functions from addresses to lists of assets
    (statefun). A ledger function is valid (sf_valid and sf_valid_) if no address holds duplicate assets,
    assetids are associated with at most one asset, every asset corresponds to a transaction output,
    and every asset id for an asset that has been spent at some time in the past is not
    currently spendable. The function tx_statefun_trans transforms a ledger function to
    a new ledger function. If the current ledger function supports the transaction (statefun_supports_tx)
    and the current ledger function is valid, then the transformed ledger function is also valid (sf_tx_valid_thm).
    The total asset values in the ledger change precisely according to the fees and rewards
    in the transaction (totalunits_bdd).
 **)

Require Export Transactions.

Definition statefun : Type := addr -> list asset.

Definition sf_unsp_txout {n} (f:bitseq n -> list asset) (h:hashval) : Prop :=
exists alpha, In_dom h (f alpha).

(*** sf_spent f h means h is the hash of a txout that has been spent at some point by the state represented by f. ***)
Inductive sf_spent {n} (f:bitseq n -> list asset) (h:hashval) : Prop :=
| sf_spent_1 inpl outpl i alpha : sf_unsp_txout f (hashpair (hashtx(inpl,outpl)) (hashnat i)) -> In (alpha,h) inpl -> sf_spent f h
| sf_spent_R inpl outpl i alpha : sf_spent f (hashpair (hashtx(inpl,outpl)) (hashnat i)) -> In (alpha,h) inpl -> sf_spent f h
.

Definition sf_valid_ {n} (alphapre:bitseq n -> addr) (f:bitseq n -> list asset) :=
(*** No duplicate: List at f alpha has no duplicate entries. ***)
(forall alpha, no_dups (f alpha))
/\
(*** Functionality: An unspent txout is only associated with one asset in one address. ***)
(forall h alpha u alpha' u', In (h,u) (f alpha) -> In (h,u') (f alpha') -> alpha = alpha' /\ u = u')
/\
(*** Existence: For every (h,u) in (f alpha), h comes from a txout with output of asset u to address alpha. ***)
(forall h u alpha, In (h,u) (f alpha)
           -> exists inpl outpl i,
                h = hashpair (hashtx(inpl,outpl)) (hashnat i)
                /\
                nth_error outpl i = value(alphapre alpha,u))
/\
(*** No Double Spending: Every txout that has been spent according to f is not an unspent txout of f. ***)
(forall h, sf_spent f h -> ~ sf_unsp_txout f h)
.

Definition sf_valid (f:statefun) : Prop := sf_valid_ (fun alpha => alpha) f.

Lemma sf_valid_fnl (f:statefun) : sf_valid f -> forall alpha, fnl (f alpha).
intros [Hf1 [Hf2 _]] alpha.
generalize (fun h u => Hf2 h alpha u alpha).
generalize (Hf1 alpha).
generalize (f alpha) as al.
intros al H. induction H as [|[h u] hr H1 H2 IH].
- intros _. apply fnl_N.
- intros H3. apply fnl_C.
  + intros H4. apply In_In_dom_lem in H4. destruct H4 as [v H5].
    assert (L1: In (h,u) ((h,u)::hr)) by now left.
    assert (L2: In (h,v) ((h,u)::hr)) by now right.
    destruct (H3 _ _ _ L1 L2) as [_ H6]. subst v. contradiction (H1 H5).
  + apply IH. intros k v v' H4 H5. apply (H3 k).
    * now right.
    * now right.
Qed.    
        
Inductive statefun_asset_value_in f : list addr_assetid -> nat -> Prop :=
| statefun_asset_value_in_nil : statefun_asset_value_in f nil 0
| statefun_asset_value_in_cons h a u inpl alpha v :
    statefun_asset_value_in f inpl v ->
    In a (f alpha) ->
    asset_value a = Some u ->
    h = assetid a ->
    statefun_asset_value_in f ((alpha,h)::inpl) (u+v)
| statefun_asset_value_in_skip h a inpl alpha v :
    statefun_asset_value_in f inpl v ->
    In a (f alpha) ->
    asset_value a = None ->
    h = assetid a ->
    statefun_asset_value_in f ((alpha,h)::inpl) v
.

Fixpoint totalassets_ {n} : forall (f:bitseq n -> list asset), list asset :=
match n with
| O => fun (f:bitseq 0 -> list asset) => f tt
| S n' => fun (f:bitseq (S n') -> list asset) => totalassets_ (fun bs => f (false,bs)) ++ totalassets_ (fun bs => f (true,bs))
end.

Definition statefun_totalassets (f:statefun) : list asset := totalassets_ f.

Definition statefun_totalunits (f:statefun) : nat := 
asset_value_sum (statefun_totalassets f).

Definition statefun_supports_tx (f:addr -> list asset) (tx:Tx) (fee rew:nat) : Prop :=
(exists utot:nat,
   statefun_asset_value_in f (tx_inputs tx) utot
   /\
   asset_value_out (tx_outputs tx) + fee = utot + rew)
.

Definition tx_statefun_trans (tx:Tx) (f:statefun) : statefun :=
fun alpha:addr =>
  (new_assets alpha (tx_outputs tx) (hashtx tx) 0)
    ++
    (remove_assets (f alpha)
                   (get_spent alpha (tx_inputs tx))).

Lemma tx_statefun_trans_lem_iff f inpl outpl alpha h obl u :
In (h,(obl,u)) (tx_statefun_trans (inpl,outpl) f alpha)
<->
In (h,(obl,u)) (f alpha) /\ ~In (alpha,h) inpl
\/
exists i, nth_error outpl i = value (alpha,(obl,u)) /\ h = hashpair (hashtx(inpl,outpl)) (hashnat i).
unfold tx_statefun_trans. split.
- intros H1. apply in_app_iff in H1. destruct H1 as [H1|H1].
  + apply new_assets_iff in H1. destruct H1 as [j [H2 H3]].
    simpl in H2. right. exists j. split.
    * assumption.
    * exact H3.
  + apply remove_assets_iff in H1. destruct H1 as [H2 H3]. left. split.
    * assumption.
    * intros H4. apply H3. apply get_spent_iff. exact H4.
- intros [[H1 H2]|[i [H1 H2]]].
  + apply in_app_iff. right. apply remove_assets_iff. split.
    * assumption.
    * intros H3. apply H2. now apply get_spent_iff.
  + apply in_app_iff. left. apply new_assets_iff. exists i. simpl. split.
    * assumption.
    * exact H2.
Qed.

Lemma statefun_supports_tx_assets_In (f:statefun) (tx:Tx) fee rew alpha h :
  statefun_supports_tx f tx fee rew ->
  In (alpha,h) (tx_inputs tx) -> exists obl u, In (h,(obl,u)) (f alpha).
intros [utot [H _]]. destruct tx as [inpl outpl].
simpl in *|-*.
induction H as [|k [k' [obl' u']] u inpl beta v H1 IH H2 H3 H4|k [k' [obl' u']] inpl beta v H1 IH H2 H3 H4].
- simpl. tauto.
- intros [H5|H5].
  + inversion H5. simpl in H4. subst k'. subst k. exists obl'. exists u'.
    subst beta. exact H2.
  + tauto.
- intros [H5|H5].
  + inversion H5. simpl in H4. subst k'. subst k. exists obl'. exists u'.
    subst beta. exact H2.
  + tauto.
Qed.

(*** We need to know the tx has at least one input to ensure all its txouts are fresh. ***)
Lemma sf_tx_valid_fresh_lem (f:statefun) (tx:Tx) fee rew :
  sf_valid f ->
  tx_inputs_valid (tx_inputs tx) ->
  statefun_supports_tx f tx fee rew ->
  forall i alpha, ~In_dom (hashpair (hashtx tx) (hashnat i)) (f alpha).
destruct tx as [[|[beta hin] inpl] outpl].
- intros _ [Ht2 _]. exfalso. simpl in Ht2. congruence.
- intros Hf Ht Hs i alpha H1.
  generalize Hf. intros [Hf1 [Hf2 [Hf3 Hf4]]].
  apply (Hf4 hin).
  + apply (sf_spent_1 f hin ((beta,hin)::inpl) outpl i beta).
    * exists alpha. assumption.
    * now left.
  + exists beta. apply In_In_dom_lem.
    assert (L1: exists obl u, In (hin, (obl,u)) (f beta)).
    { apply (statefun_supports_tx_assets_In _ _ _ _ _ _ Hs).
      simpl. now left.
    }
    destruct L1 as [obl [u H2]].
    exists (obl,u). exact H2.
Qed.

(*** We need to know the tx has at least one input to ensure all its txouts did not occur as previous spent txs. ***)
Lemma sf_tx_valid_not_spent_lem (f:statefun) (tx:Tx) fee rew :
  sf_valid f ->
  tx_inputs_valid (tx_inputs tx) ->
  statefun_supports_tx f tx fee rew ->
  forall i, ~ sf_spent f (hashpair (hashtx tx) (hashnat i)).
destruct tx as [[|[beta hin] inpl] outpl].
- intros _ [Ht2 _]. exfalso. simpl in Ht2. congruence.
- intros Hf Ht Hs i H1.
  generalize Hf. intros [Hf1 [Hf2 [Hf3 Hf4]]].
  apply (Hf4 hin).
  + apply (sf_spent_R f hin ((beta,hin)::inpl) outpl i beta).
    * exact H1.
    * now left.
  + exists beta. apply In_In_dom_lem.
    assert (L1: exists obl u, In (hin, (obl,u)) (f beta)).
    { apply (statefun_supports_tx_assets_In _ _ _ _ _ _ Hs).
      simpl. now left.
    }
    destruct L1 as [obl [u H2]].
    exists (obl,u). exact H2.
Qed.

(** If a txout h was spent in the transformed state, then it was either already spent or was one of the inputs of the new tx. ***)
Lemma sf_tx_valid_spent_lem inpl outpl f h fee rew :
  tx_inputs_valid inpl ->
  statefun_supports_tx f (inpl,outpl) fee rew ->
  sf_spent (tx_statefun_trans (inpl, outpl) f) h ->
  sf_spent f h \/ exists alpha, In (alpha,h) inpl.
intros Ht Hs H.
induction H as [h inpl' outpl' i alpha [beta H1] H2|h inpl' outpl' i alpha H1 IH1 H2].
- apply In_In_dom_lem in H1. destruct H1 as [u H1].
  apply in_app_iff in H1. destruct H1 as [H1|H1].
  + apply new_assets_iff in H1. destruct H1 as [j [H3 H4]].
    right. exists alpha.
    assert (L1: In (hash_addr_assetid (alpha,h)) (map hash_addr_assetid inpl)).
    { apply hashpairinj in H4. destruct H4 as [H5 H6]. apply hashnatinj in H6.
      simpl in H5. apply hashpairinj in H5.
      destruct H5 as [H7 H8].
      apply hashlistinj in H7. rewrite <- H7.
      apply in_map_iff. exists (alpha,h). tauto. }
    apply in_map_iff in L1. destruct L1 as [[alpha' h'] [L1a L1b]].
    apply hash_addr_assetidinj in L1a. destruct L1a as [L1aa L1ab].
    subst alpha' h'. assumption.
  + apply remove_assets_iff in H1. destruct H1 as [H3 H4].
    left. apply (sf_spent_1 f h inpl' outpl' i alpha).
    * exists beta. apply In_In_dom_lem_2 in H3. assumption.
    * assumption.
- left. destruct IH1 as [H3|[beta H3]].
  + now apply (sf_spent_R f h inpl' outpl' i alpha).
  + apply (statefun_supports_tx_assets_In _ _ _ _ _ _ Hs) in H3.
    destruct H3 as [obl [u H3]].
    apply (sf_spent_1 f h inpl' outpl' i alpha).
    * exists beta. apply In_In_dom_lem_2 in H3. assumption.
    * assumption.
Qed.

Theorem sf_tx_valid_thm (f:statefun) (tx:Tx) fee rew :
  sf_valid f ->
  tx_valid tx ->
  statefun_supports_tx f tx fee rew ->
  sf_valid (tx_statefun_trans tx f).
intros Hf Ht Hs.
destruct tx as [inpl outpl]. generalize Hf Ht. simpl.
intros [Hf1 [Hf2 [Hf3 Hf4]]] Ht2. split.
- intros alpha. simpl. unfold tx_statefun_trans. apply no_dups_app.
  + apply no_dups_new_assets.
  + apply no_dups_remove_assets. apply Hf1.
  + intros [h [obl u]] H1 H2.
    apply new_assets_iff in H1. apply remove_assets_iff in H2.
    destruct H1 as [j [H3 H4]]. destruct H2 as [H5 H6].
    apply (sf_tx_valid_fresh_lem f (inpl,outpl) fee rew Hf Ht2 Hs j alpha).
    apply In_In_dom_lem. exists (obl,u).
    change (h = hashpair (hashtx (inpl, outpl)) (hashnat j)) in H4.
    rewrite H4 in H5. exact H5.
- split.
  + intros h alpha [obl u] alpha' [obl' u'].
    unfold tx_statefun_trans. intros H1 H2.
    apply in_app_iff in H1. apply in_app_iff in H2.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    * apply new_assets_iff in H1. destruct H1 as [j [H3 H4]].
      apply new_assets_iff in H2. destruct H2 as [k [H5 H6]].
      change (nth_error outpl j = value (alpha, (obl,u))) in H3.
      change (h = hashpair (hashtx (inpl, outpl)) (hashnat j)) in H4.
      change (nth_error outpl k = value (alpha', (obl',u'))) in H5.
      change (h = hashpair (hashtx (inpl, outpl)) (hashnat k)) in H6.
      assert (L1: j = k).
      { subst h. apply hashpairinj in H6. destruct H6 as [H7 H8].
        apply hashnatinj in H8. omega. }
      subst k. rewrite H3 in H5. inversion H5. tauto.
    * exfalso.
      apply new_assets_iff in H1. destruct H1 as [j [H3 H4]].
      change (nth_error outpl j = value (alpha, (obl,u))) in H3.
      change (h = hashpair (hashtx (inpl, outpl)) (hashnat j)) in H4.
      apply remove_assets_iff in H2. destruct H2 as [H5 H6].
      change (~ In h (get_spent alpha' inpl)) in H6.
      apply In_In_dom_lem_2 in H5. revert H5.
      rewrite H4. apply (sf_tx_valid_fresh_lem f (inpl,outpl) fee rew Hf Ht2 Hs).
    * exfalso.
      apply remove_assets_iff in H1. destruct H1 as [H3 H4].
      change (~ In h (get_spent alpha inpl)) in H4.
      apply new_assets_iff in H2. destruct H2 as [j [H5 H6]].
      change (nth_error outpl j = value (alpha', (obl',u'))) in H5.
      change (h = hashpair (hashtx (inpl, outpl)) (hashnat j)) in H6.
      apply In_In_dom_lem_2 in H3. revert H3.
      rewrite H6. apply (sf_tx_valid_fresh_lem f (inpl,outpl) fee rew Hf Ht2 Hs).
    * apply remove_assets_iff in H1. destruct H1 as [H3 H4].
      apply remove_assets_iff in H2. destruct H2 as [H5 H6].
      change (~ In h (get_spent alpha inpl)) in H4.
      change (~ In h (get_spent alpha' inpl)) in H6.
      now apply Hf2 with (h := h).
  + split.
    * { unfold tx_statefun_trans. intros h [obl u] alpha H1.
        apply in_app_iff in H1. destruct H1 as [H1|H1].
        - apply new_assets_iff in H1. destruct H1 as [j [H2 H3]].
          exists inpl. exists outpl. exists j. split.
          + assumption.
          + exact H2.
        - apply remove_assets_iff in H1. destruct H1 as [H2 H3].
          revert H2. apply Hf3.
      }
    * { intros h H1 [alpha H2].
        apply In_In_dom_lem in H2. destruct H2 as [u H2].
        apply in_app_iff in H2. destruct H2 as [H2|H2].
        - apply new_assets_iff in H2. destruct H2 as [j [H3 H4]].
          simpl in H3, H4.
          destruct (sf_tx_valid_spent_lem inpl outpl f h fee rew Ht2 Hs H1) as [H5|[beta H5]].
          + revert H5. rewrite H4.
            apply (sf_tx_valid_not_spent_lem f (inpl,outpl) fee rew Hf Ht2 Hs).
          + apply (hashtx_notin_inpl beta inpl outpl j).
            simpl. rewrite <- H4. exact H5.
        - apply remove_assets_iff in H2. destruct H2 as [H3 H4].
          assert (L1: sf_unsp_txout f h).
          { exists alpha. apply In_In_dom_lem_2 in H3. assumption. }
          revert L1. apply Hf4.
          destruct (sf_tx_valid_spent_lem inpl outpl f h fee rew Ht2 Hs H1) as [H5|[beta H5]].
          + assumption.
          + exfalso. apply H4. apply get_spent_iff. simpl.
            assert (L2: alpha = beta).
            { destruct (statefun_supports_tx_assets_In f (inpl,outpl) fee rew beta h Hs H5) as [obl' [v H6]].
              generalize (Hf2 h alpha u beta (obl',v) H3 H6). tauto.
            }
            congruence.
      }
Qed.              

Lemma totalassets__iff {n} (f:bitseq n -> list asset) h u :
In (h,u) (totalassets_ f)
<->
exists bs, In (h,u) (f bs).
induction n as [|n IH].
- simpl. split.
  + intros H1. exists tt. assumption.
  + intros [[] H1]. assumption.
- simpl. split.
  + intros H1. apply in_app_iff in H1. destruct H1 as [H1|H1].
    * apply IH in H1. destruct H1 as [bs H1]. exists (false,bs). assumption.
    * apply IH in H1. destruct H1 as [bs H1]. exists (true,bs). assumption.
  + intros [[[|] bs] H1].
    * apply in_or_app. right. apply IH. exists bs. assumption.
    * apply in_or_app. left. apply IH. exists bs. assumption.
Qed.

Lemma totalassets_iff (f:addr -> list asset) h u :
In (h,u) (statefun_totalassets f)
<->
exists alpha, In (h,u) (f alpha).
apply totalassets__iff.
Qed.

Lemma totalassets_no_dups_ {n} (f:bitseq n -> list asset) :
  (forall bs, no_dups (f bs)) ->
  (forall h bs u bs' u', In (h,u) (f bs) -> In (h,u') (f bs') -> bs = bs' /\ u = u') ->
  no_dups (totalassets_ f).
induction n as [|n IH].
- simpl. intros H1 _. apply H1.
- intros H1 H2. simpl. apply no_dups_app.
  + apply IH.
    * intros bs. apply (H1 (false,bs)).
    * intros h bs u bs' u' H3 H4.
      destruct (H2 h (false,bs) u (false,bs') u' H3 H4) as [H5 H6].
      split; congruence.
  + apply IH.
    * intros bs. apply (H1 (true,bs)).
    * intros h bs u bs' u' H3 H4.
      destruct (H2 h (true,bs) u (true,bs') u' H3 H4) as [H5 H6].
      split; congruence.
  + intros [h u] H3 H4.
    apply totalassets__iff in H3. apply totalassets__iff in H4.
    destruct H3 as [bs H3]. destruct H4 as [bs' H4].
    destruct (H2 h (false,bs) u (true,bs') u H3 H4) as [H5 H6].
    discriminate H5.
Qed.

Lemma totalassets_no_dups (f:statefun) :
 sf_valid f ->
 no_dups (statefun_totalassets f).
intros [Hf1 [Hf2 _]]. apply totalassets_no_dups_.
- exact Hf1.
- exact Hf2.
Qed.

Lemma totalassets_fnl_ {n} (f:bitseq n -> list asset) :
  (forall bs, no_dups (f bs)) ->
  (forall h bs u bs' u', In (h,u) (f bs) -> In (h,u') (f bs') -> bs = bs' /\ u = u') ->
  fnl (totalassets_ f).
induction n as [|n IH].
- simpl. intros H1 H2.
  generalize (fun h u v => H2 h tt u tt v). generalize (H1 tt).
  generalize (f tt) as l. clear.
  intros l Hl. induction Hl as [|[h u] l H0 H1 IH].
  + intros _. apply fnl_N.
  + intros H2. apply fnl_C.
    * intros H3. apply In_In_dom_lem in H3. destruct H3 as [v H4].
      assert (L1: tt = tt /\ u = v).
      { apply (H2 h); simpl; tauto. }
      destruct L1 as [_ L1b].
      subst v. contradiction.
    * { apply IH. intros k v w H3 H4. apply (H2 k).
        - now right.
        - now right.
      }
- intros H1 H2. simpl. apply fnl_app.
  + apply IH.
    * intros bs. apply (H1 (false,bs)).
    * intros h bs u bs' u' H3 H4.
      destruct (H2 h (false,bs) u (false,bs') u' H3 H4) as [H5 H6].
      split; congruence.
  + apply IH.
    * intros bs. apply (H1 (true,bs)).
    * intros h bs u bs' u' H3 H4.
      destruct (H2 h (true,bs) u (true,bs') u' H3 H4) as [H5 H6].
      split; congruence.
  + intros h H3 H4.
    apply In_In_dom_lem in H3. apply In_In_dom_lem in H4.
    destruct H3 as [u H3]. destruct H4 as [v H4].
    apply totalassets__iff in H3. apply totalassets__iff in H4.
    destruct H3 as [bs H3]. destruct H4 as [bs' H4].
    destruct (H2 h (false,bs) u (true,bs') v H3 H4) as [H5 H6].
    discriminate H5.
Qed.

Lemma totalassets_fnl (f:statefun) :
 sf_valid f ->
 fnl (statefun_totalassets f).
intros [Hf1 [Hf2 _]]. apply totalassets_fnl_.
- exact Hf1.
- exact Hf2.
Qed.

Opaque statefun_totalassets.

Lemma totalassets_trans_iff (f:statefun) (tx:Tx) fee rew :
 sf_valid f ->
 tx_valid tx ->
 statefun_supports_tx f tx fee rew ->
 forall h obl u,
   In (h,(obl,u)) (statefun_totalassets (tx_statefun_trans tx f)) <->
   ((In (h,(obl,u)) (statefun_totalassets f) /\ ~exists alpha, In (alpha,h) (tx_inputs tx))
    \/
    exists alpha i, nth_error (tx_outputs tx) i = value (alpha,(obl,u)) /\ h = hashpair (hashtx tx) (hashnat i)).
intros Hf Ht Hs. destruct tx as [inpl outpl]. intros h obl u. split.
- intros H1. destruct (totalassets_iff (tx_statefun_trans (inpl,outpl) f) h (obl,u)) as [H2 _].
  destruct (H2 H1) as [alpha H3].
  unfold tx_statefun_trans in H3. apply in_app_iff in H3.
  destruct H3 as [H4|H4].
  + apply new_assets_iff in H4.
    right. exists alpha. exact H4.
  + apply remove_assets_iff in H4. destruct H4 as [H5 H6]. left. split.
    * destruct (totalassets_iff f h (obl,u)) as [_ H7]. apply H7.
      exists alpha. assumption.
    * intros [beta H7]. simpl in H7. apply H6.
      apply get_spent_iff. simpl.
      assert (L1: alpha = beta).
      { destruct (statefun_supports_tx_assets_In f (inpl,outpl) fee rew beta h Hs H7) as [obl' [v H8]].
        destruct Hf as [_ [Hf2 _]].
        destruct (Hf2 h alpha (obl,u) beta (obl',v) H5 H8) as [H9 _].
        exact H9.
      }
      rewrite L1. exact H7.
- intros [[H1 H2]|[alpha [i H1]]].
  + destruct (totalassets_iff (tx_statefun_trans (inpl,outpl) f) h (obl,u)) as [_ H3].
    apply H3.
    destruct (totalassets_iff f h (obl,u)) as [H4 _].
    destruct (H4 H1) as [alpha H5].
    exists alpha.
    unfold tx_statefun_trans. apply in_or_app.
    right. apply remove_assets_iff.
    split.
    * assumption.
    * intros H6. apply H2. exists alpha. now apply get_spent_iff.
  + destruct (totalassets_iff (tx_statefun_trans (inpl,outpl) f) h (obl,u)) as [_ H3].
    apply H3.
    exists alpha.
    unfold tx_statefun_trans. apply in_or_app.
    left. apply new_assets_iff. exists i. exact H1.
Qed.

Lemma sf_totalassets_app__iff {n} (f g:bitseq n -> list asset) :
  app_perm (totalassets_ (fun alpha => f alpha ++ g alpha))
           (totalassets_ f ++ totalassets_ g).
induction n as [|n IH].
- simpl. apply app_perm_ref.
- simpl.
  generalize (IH (fun bs => f (false,bs)) (fun bs => g (false,bs))).
  intros IH1.
  generalize (IH (fun bs => f (true,bs)) (fun bs => g (true,bs))).
  intros IH2.
  apply app_perm_tra with (r := ((totalassets_ (fun bs : bitseq n => f (false, bs)) ++
                                               totalassets_ (fun bs : bitseq n => g (false, bs))) ++
                                                                                                  (totalassets_ (fun bs : bitseq n => f (true, bs)) ++
                   totalassets_ (fun bs : bitseq n => g (true, bs))))).
  + apply app_perm_app.
    * exact IH1.
    * exact IH2.
  + rewrite <- app_assoc. rewrite <- app_assoc. apply app_perm_app.
    * apply app_perm_ref.
    * { rewrite app_assoc. rewrite app_assoc. apply app_perm_app.
        - apply app_perm_swap.
        - apply app_perm_ref.
      }
Qed.

Lemma sf_totalassets__ifcons_app_perm (nw:asset) (beta:addr) {n} (alphapre:bitseq n -> addr) (f:bitseq n -> list asset) :
  (forall alpha1 alpha2:bitseq n, alphapre alpha1 = alphapre alpha2 -> alpha1 = alpha2) ->
  ((exists alpha:bitseq n, alphapre alpha = beta) ->
   app_perm
     (totalassets_
        (fun alpha : bitseq n =>
           if addr_eq_dec (alphapre alpha) beta then nw :: f alpha else f alpha))
     (nw :: totalassets_ f))
  /\
  (~(exists alpha:bitseq n, alphapre alpha = beta) ->
   app_perm
     (totalassets_
        (fun alpha : bitseq n =>
           if addr_eq_dec (alphapre alpha) beta then nw :: f alpha else f alpha))
     (totalassets_ f)).
induction n as [|n IH]; split; intros H1.
- simpl. destruct H1 as [[] H1].
  destruct (addr_eq_dec (alphapre tt) beta) as [H2|H2].
  + apply app_perm_ref.
  + exfalso. contradiction.
- simpl.
  destruct (addr_eq_dec (alphapre tt) beta) as [H2|H2].
  + exfalso. apply H1. exists tt. assumption.
  + apply app_perm_ref.
- set (alphapre1 := fun alpha:bitseq n => alphapre (true,alpha)).
  set (alphapre0 := fun alpha:bitseq n => alphapre (false,alpha)).
  assert (alphapre1inj : forall alpha1 alpha2, alphapre1 alpha1 = alphapre1 alpha2 -> alpha1 = alpha2).
  { intros alpha1 alpha2 H2. apply H in H2. congruence. }
  assert (alphapre0inj : forall alpha1 alpha2, alphapre0 alpha1 = alphapre0 alpha2 -> alpha1 = alpha2).
  { intros alpha1 alpha2 H2. apply H in H2. congruence. }
  destruct H1 as [[[|] alpha] H1].
  + destruct (IH alphapre1 (fun alpha => f (true,alpha)) alphapre1inj) as [IH1 _].
    destruct (IH alphapre0 (fun alpha => f (false,alpha)) alphapre0inj) as [_ IH2].
    simpl.
    apply app_perm_tra with (r := (totalassets_ (fun bs : bitseq n => f (false, bs)) ++ nw::totalassets_ (fun bs : bitseq n => f (true, bs)))).
    * { apply app_perm_app.
        - apply IH2. intros [alpha0 H2]. rewrite <- H1 in H2. apply H in H2.
          discriminate H2.
        - apply IH1. exists alpha. exact H1.
      }
    * { change (app_perm
     (totalassets_ (fun bs : bitseq n => f (false, bs)) ++
                   ((cons nw nil) ++ totalassets_ (fun bs : bitseq n => f (true, bs))))
     ((nw
      :: totalassets_ (fun bs : bitseq n => f (false, bs))) ++
         totalassets_ (fun bs : bitseq n => f (true, bs)))).
        rewrite app_assoc. apply app_perm_app.
        - apply (app_perm_swap _ (cons nw nil)).
        - apply app_perm_ref.
      } 
  + destruct (IH alphapre1 (fun alpha => f (true,alpha)) alphapre1inj) as [_ IH1].
    destruct (IH alphapre0 (fun alpha => f (false,alpha)) alphapre0inj) as [IH2 _].
    simpl.
    change (app_perm
     (totalassets_
        (fun bs : bitseq n =>
         if addr_eq_dec (alphapre (false, bs)) beta
         then nw :: f (false, bs)
         else f (false, bs)) ++
      totalassets_
        (fun bs : bitseq n =>
         if addr_eq_dec (alphapre (true, bs)) beta
         then nw :: f (true, bs)
         else f (true, bs)))
     ((nw
      :: totalassets_ (fun bs : bitseq n => f (false, bs))) ++
         totalassets_ (fun bs : bitseq n => f (true, bs)))).
    apply app_perm_app.
    * apply IH2. exists alpha. exact H1.
    * apply IH1. intros [alpha0 H2]. rewrite <- H1 in H2. apply H in H2.
      discriminate H2.
- set (alphapre1 := fun alpha:bitseq n => alphapre (true,alpha)).
  set (alphapre0 := fun alpha:bitseq n => alphapre (false,alpha)).
  assert (alphapre1inj : forall alpha1 alpha2, alphapre1 alpha1 = alphapre1 alpha2 -> alpha1 = alpha2).
  { intros alpha1 alpha2 H2. apply H in H2. congruence. }
  assert (alphapre0inj : forall alpha1 alpha2, alphapre0 alpha1 = alphapre0 alpha2 -> alpha1 = alpha2).
  { intros alpha1 alpha2 H2. apply H in H2. congruence. }
  destruct (IH alphapre1 (fun alpha => f (true,alpha)) alphapre1inj) as [_ IH1].
  destruct (IH alphapre0 (fun alpha => f (false,alpha)) alphapre0inj) as [_ IH2].
  simpl. apply app_perm_app.
  + apply IH2. intros [alpha H2]. apply H1. exists (false,alpha). exact H2.
  + apply IH1. intros [alpha H2]. apply H1. exists (true,alpha). exact H2.
Qed.

Lemma sf_totalassets__remove_assets {n} (alphapre:bitseq n -> addr) (f:bitseq n -> list asset) (inpl:list addr_assetid) :
  (forall h alpha u beta v, In (h,u) (f alpha) -> In (h,v) (f beta) -> alpha = beta /\ u = v) ->
  (forall h alpha, In (alphapre alpha,h) inpl -> exists u, In (h,u) (f alpha)) ->
  (forall h u, In (h,u) (totalassets_ f) -> (In h (map (@snd addr hashval) inpl) <-> exists alpha, In (alphapre alpha,h) inpl)) ->
  app_perm (remove_assets (totalassets_ f) (map (@snd addr hashval) inpl))
           (totalassets_ (fun alpha => remove_assets (f alpha) (get_spent (alphapre alpha) inpl))).
intros Hf2 Ht1. induction n as [|n IH].
- simpl.
  intros H1. rewrite (remove_assets_eq (f tt) (map (snd (B:=hashval)) inpl) (get_spent (alphapre tt) inpl)).
  + apply app_perm_ref.
  + intros h H2. apply In_In_dom_lem in H2. destruct H2 as [u H2]. split.
    * intros H3. apply (H1 _ _ H2) in H3. destruct H3 as [[] H3]. now apply get_spent_iff.
    * intros H3. apply (H1 _ _ H2). exists tt. now apply get_spent_iff.
- simpl. intros H1.
  apply app_perm_tra with (r :=
     (remove_assets
        (totalassets_ (fun bs : bitseq n => f (false, bs)))
        (map (snd (B:=hashval)) inpl))
       ++
     (remove_assets
        (totalassets_ (fun bs : bitseq n => f (true, bs)))
        (map (snd (B:=hashval)) inpl))).
  + rewrite remove_assets_app. apply app_perm_ref.
  + apply app_perm_app.
    * { set (alphapre0 := fun alpha:bitseq n => alphapre (false,alpha)).
        set (f0 := fun alpha:bitseq n => f (false,alpha)).
        apply (IH alphapre0 f0).
        - intros h alpha u beta v H2 H3.
          destruct (Hf2 h (false,alpha) u (false,beta) v H2 H3) as [H4 H5].
          split; congruence.
        - intros h alpha H2. unfold alphapre0 in H2. apply Ht1 in H2. exact H2.
        - intros h u H2. split.
          + intros H3. apply (H1 h u) in H3.
            * { destruct H3 as [[[|] alpha] H4].
                - apply totalassets__iff in H2. unfold f0 in H2. simpl in H2.
                  destruct H2 as [beta H2].
                  apply Ht1 in H4. destruct H4 as [v H5].
                  destruct (Hf2 h (true,alpha) v (false,beta) u H5 H2) as [H6 _].
                  discriminate H6.
                - exists alpha. exact H4.
              }
            * apply in_or_app. left. exact H2.
          + intros [alpha H3]. apply (H1 h u).
            * apply in_or_app. left. exact H2.
            * exists (false,alpha). exact H3.
      }
    * { set (alphapre1 := fun alpha:bitseq n => alphapre (true,alpha)).
        set (f1 := fun alpha:bitseq n => f (true,alpha)).
        apply (IH alphapre1 f1).
        - intros h alpha u beta v H2 H3.
          destruct (Hf2 h (true,alpha) u (true,beta) v H2 H3) as [H4 H5].
          split; congruence.
        - intros h alpha H2. unfold alphapre1 in H2. apply Ht1 in H2. exact H2.
        - intros h u H2. split.
          + intros H3. apply (H1 h u) in H3.
            * { destruct H3 as [[[|] alpha] H4].
                - exists alpha. exact H4.
                - apply totalassets__iff in H2. unfold f1 in H2. simpl in H2.
                  destruct H2 as [beta H2].
                  apply Ht1 in H4. destruct H4 as [v H5].
                  destruct (Hf2 h (false,alpha) v (true,beta) u H5 H2) as [H6 _].
                  discriminate H6.
              }
            * apply in_or_app. right. exact H2.
          + intros [alpha H3]. apply (H1 h u).
            * apply in_or_app. right. exact H2.
            * exists (true,alpha). exact H3.
      }
Qed.            

Transparent statefun_totalassets.

Lemma sf_totalassets_app_iff f g :
  app_perm (statefun_totalassets (fun alpha => f alpha ++ g alpha))
           (statefun_totalassets f ++ statefun_totalassets g).
apply sf_totalassets_app__iff.
Qed.

Lemma sf_totalassets_ifcons_app_perm beta nw f :
  app_perm (statefun_totalassets (fun alpha => if addr_eq_dec alpha beta then nw::f alpha else f alpha)) (nw::statefun_totalassets f).
apply sf_totalassets__ifcons_app_perm.
- tauto.
- exists beta. reflexivity.
Qed.

Lemma sf_totalassets_remove_assets f inpl :
  (forall h alpha u beta v, In (h,u) (f alpha) -> In (h,v) (f beta) -> alpha = beta /\ u = v) ->
  (forall h alpha, In (alpha,h) inpl -> exists u, In (h,u) (f alpha)) ->
  app_perm (remove_assets (statefun_totalassets f) (map (@snd addr hashval) inpl))
           (statefun_totalassets (fun alpha => remove_assets (f alpha) (get_spent alpha inpl))).
intros H1 H2.
apply (sf_totalassets__remove_assets (fun alpha => alpha) f inpl H1 H2).
intros h u H3. split.
- intros H4. apply in_map_iff in H4. destruct H4 as [[alpha h'] [H5 H6]].
  exists alpha. simpl in H5. congruence.
- intros [alpha H4]. apply in_map_iff. exists (alpha,h). split.
  + reflexivity.
  + exact H4.
Qed.

Opaque statefun_totalassets.

Lemma sf_totalassets_nil : statefun_totalassets (fun alpha => nil) = nil.
assert (L1: exists l, statefun_totalassets (fun alpha => nil) = l).
{ now exists (statefun_totalassets (fun alpha => nil)). }
destruct L1 as [[|[h u] l] L1a].
- exact L1a.
- assert (L2: In (h, u) (statefun_totalassets (fun _ => nil))).
  { rewrite L1a. left. reflexivity. }
  destruct (totalassets_iff (fun _ => nil) h u) as [H1 H2].
  destruct (H1 L2) as [alpha []].
Qed.

Opaque asset_value_sum.

Lemma sf_totalunits_new_assets (aul:list addr_preasset) txh i :
  statefun_totalunits (fun alpha => new_assets alpha aul txh i) =
  asset_value_out aul.
revert i. induction aul as [|[beta [obl u]] aul IH]; intros i.
- simpl. unfold statefun_totalunits. rewrite sf_totalassets_nil. simpl.
  reflexivity.
- simpl. rewrite <- (IH (S i)). unfold statefun_totalunits.
  assert (L1: app_perm (statefun_totalassets
           (fun alpha : addr =>
            if addr_eq_dec alpha beta
            then
             (hashpair txh (hashnat i), (obl,u)) :: new_assets alpha aul txh (S i)
            else new_assets alpha aul txh (S i)))
                       ((hashpair txh (hashnat i),(obl,u))::(statefun_totalassets
                                                         (fun alpha : addr => new_assets alpha aul txh (S i))))).
  { apply (sf_totalassets_ifcons_app_perm beta (hashpair txh (hashnat i),(obl,u))). }
  apply app_perm_asset_value_sum in L1.
  simpl in L1. rewrite L1.
  destruct (asset_value (hashpair txh (hashnat i), (obl,u))) as [u'|] eqn:E1.
  + rewrite (asset_value_sum_value_cons _ _ _ E1).
    destruct u as [u|d]; try discriminate E1.
    unfold asset_value in E1. simpl in E1. inversion E1. reflexivity.
  + rewrite (asset_value_sum_novalue_cons _ _ E1).
    destruct u as [n|d]; try reflexivity; discriminate E1.
Qed.

Lemma no_dups_map_inpl f inpl :
  sf_valid f ->
  (forall h alpha, In (alpha,h) inpl -> exists u, In (h,u) (f alpha)) ->
  no_dups inpl ->
  no_dups (map (@snd addr hashval) inpl).
intros [_ [Hf2 _]] H1 H.
induction H as [|[alpha h] inpl H2 H3 IH].
- apply no_dups_nil.
- simpl. apply no_dups_cons.
  + intros H4. apply in_map_iff in H4.
    destruct H4 as [[beta k] [H5 H6]]. simpl in H5. subst k.
    assert (L1: exists oblu : prod obligation preasset, In (h, oblu) (f alpha)).
    { apply H1. now left. }
    assert (L2: exists oblu : prod obligation preasset, In (h, oblu) (f beta)).
    { apply H1. now right. }
    destruct L1 as [[obl u] L1a].
    destruct L2 as [[obl' v] L2a].
    destruct (Hf2 h alpha (obl,u) beta (obl',v) L1a L2a) as [H7 _].
    subst beta. contradiction.
  + apply IH. intros k beta H4. apply H1. now right.
Qed.

Lemma statefun_asset_value_in_lem f inpl utot :
  sf_valid f ->
  (forall h alpha, In (alpha,h) inpl -> exists u, In (h,u) (f alpha)) ->
  no_dups inpl ->
  statefun_asset_value_in f inpl utot ->
   utot + statefun_totalunits 
            (fun alpha : addr =>
               remove_assets (f alpha) (get_spent alpha inpl))
   =
   statefun_totalunits f.
intros Hf Ht1 Ht3 H.
assert (L1:forall (h : hashval) (alpha : addr) (u : prod obligation preasset) 
                  (beta : addr) (v : prod obligation preasset),
             In (h, u) (f alpha) -> In (h, v) (f beta) -> alpha = beta /\ u = v).
{ destruct Hf as [_ [Hf2 _]]. exact Hf2. }
unfold statefun_totalunits at 1.
rewrite <- (app_perm_asset_value_sum _ _ (sf_totalassets_remove_assets f inpl L1 Ht1)).
clear L1.
induction H as [|h a u inpl alpha v H1 IH1 H2|h a inpl alpha v H1 IH1 H2 H3].
- simpl. rewrite remove_assets_nil. unfold statefun_totalunits. omega.
- simpl.
  assert (L3:forall h alpha, In (alpha, h) inpl -> exists u : prod obligation preasset, In (h, u) (f alpha)).
  { intros k beta H3. apply Ht1. now right. }
  specialize (IH1 L3).
  assert (L4: v + (u + asset_value_sum
                         (remove_assets (statefun_totalassets f)
                                        (h :: map (snd (B:=hashval)) inpl)))
              = statefun_totalunits f).
  { rewrite asset_value_sum_asset_shift with (a := (assetobl a,assetpre a)).
    - apply IH1. inversion Ht3. assumption.
    - apply totalassets_fnl. exact Hf.
    - exact (no_dups_map_inpl f _ Hf Ht1 Ht3).
    - apply totalassets_iff. exists alpha. subst h.
      destruct a as [h [obl u']]. exact H2.
    - exact H.
  }
  omega.
- simpl.
  assert (L3:forall h alpha, In (alpha, h) inpl -> exists u : prod obligation preasset, In (h, u) (f alpha)).
  { intros k beta H4. apply Ht1. now right. }
  specialize (IH1 L3).
  assert (L4: v + asset_value_sum
                    (remove_assets (statefun_totalassets f)
                                   (h :: map (snd (B:=hashval)) inpl))
              = statefun_totalunits f).
  { rewrite asset_value_sum_asset_shift_non with (a := (assetobl a,assetpre a)).
    - apply IH1. inversion Ht3. assumption.
    - apply totalassets_fnl. exact Hf.
    - exact (no_dups_map_inpl f _ Hf Ht1 Ht3).
    - apply totalassets_iff. exists alpha. subst h.
      destruct a as [h [obl u']]. exact H2.
    - exact H3.
  }
  omega.
Qed.

Theorem totalunits_bdd (f:statefun) (tx:Tx) (fee rew:nat) :
 sf_valid f ->
 tx_valid tx ->
 statefun_supports_tx f tx fee rew ->
 statefun_totalunits (tx_statefun_trans tx f) + fee = statefun_totalunits f + rew.
intros Hf Ht Hs. generalize Hs. intros [utot [H1 H2]].
unfold statefun_totalunits at 1. unfold tx_statefun_trans.
generalize (sf_totalassets_app_iff (fun alpha => new_assets alpha (tx_outputs tx) (hashtx tx) 0) (fun alpha => remove_assets (f alpha) (get_spent alpha (tx_inputs tx)))).
intros H3. apply app_perm_asset_value_sum in H3.
rewrite H3. clear H3.
rewrite <- (asset_value_sum_app 
              (statefun_totalassets
                 (fun alpha : addr =>
                    new_assets alpha (tx_outputs tx) (hashtx tx) 0))
              (statefun_totalassets
                 (fun alpha : addr =>
                    remove_assets (f alpha) (get_spent alpha (tx_inputs tx))))).
change ((statefun_totalunits
           (fun alpha : addr =>
            new_assets alpha (tx_outputs tx) (hashtx tx) 0)) +
        (statefun_totalunits
           (fun alpha : addr =>
              remove_assets (f alpha) (get_spent alpha (tx_inputs tx)))) + fee =
   statefun_totalunits f + rew).
rewrite sf_totalunits_new_assets.
assert (L1:utot + (statefun_totalunits
                     (fun alpha : addr =>
                        remove_assets (f alpha) (get_spent alpha (tx_inputs tx)))) =
   statefun_totalunits f).
{ apply statefun_asset_value_in_lem.
  - exact Hf.
  - destruct tx as [inpl outpl]. destruct Ht as [Ht1a _].
    simpl. intros h alpha H3.
    destruct (statefun_supports_tx_assets_In f (inpl,outpl) fee rew alpha h Hs H3) as [obl' [v H4]].
    exists (obl',v). exact H4.
  - destruct tx as [inpl outpl]. destruct Ht as [_ Ht2b]. exact Ht2b.
  - exact H1.
}
omega.
Qed.

