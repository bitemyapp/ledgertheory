(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Blocks: Blocks are given by headers and deltas.
    We define types of block chains and block header chains.
    We leave the reward function, how 'hits' are checked and how targets are calculated as parameters.
    The block contains a ctree corresponding to sufficient information about the previous ledger
    to process the block (ctree_of_Block) obtained by grafting the information in the block delta
    to the information in the block header. All the transactions in the block (including the
    coinstake in the header) can be combined to give one large transaction (tx_of_Block).
    If the block is valid (valid_Block), then the combined transaction will be valid and supported.
    If we start from a valid genesis ledger and a block chain is built from valid blocks (valid_BlockChain),
    then we are guaranteed that the ending ledger is also valid (lastledgerroot_valid).
    Furthermore, we know precisely how many currency units are in the ledger as of
    a certain block height (lastledgerroot_sum_correct).
 **)

Require Export CTreeGrafting.

(*** Idea: keep up with how fast the past N blocks and use this to determine the current target. I'll use 6 blocks just as a concrete option here. ***)
Definition targetinfo : Type := prod nat (list nat).
Definition nexttargetinfo (ti : targetinfo) (tm : nat) : targetinfo :=
match ti with
| (prevtm,nil) => (tm,(tm - prevtm)::nil)
| (prevtm,c1::nil) => (tm,c1::(tm - prevtm)::nil)
| (prevtm,c2::c1::nil) => (tm,c2::c1::(tm - prevtm)::nil)
| (prevtm,c3::c2::c1::nil) => (tm,c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c4::c3::c2::c1::nil) => (tm,c4::c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c5::c4::c3::c2::c1::nil) => (tm,c5::c4::c3::c2::c1::(tm - prevtm)::nil)
| (prevtm,c6::c5::c4::c3::c2::c1::_) => (tm,c5::c4::c3::c2::c1::(tm - prevtm)::nil)
end.

Definition hashtargetinfo (ti:targetinfo) : hashval :=
let (n,ml) := ti in
hashpair (hashnat n) (hashlist (map hashnat ml)).

Definition targetinfo_timestamp (ti:targetinfo) : nat := fst ti.

Record BlockHeader : Type :=
  mkBlockHeader
    {
      prevblockhash : option hashval;
      newledgerroot : hashval;
      targetinfohash : hashval;
      timestamp : nat;
      stake : nat;
      stakeaddr : addr;
      stakeassetid : hashval;
      blocksignat : signat;
      prevledger : ctree 160
    }.
  
Record BlockDelta : Type :=
  mkBlockDelta
    {
      totalfees : nat;
      stakeoutput : list addr_preasset;
      prevledgergraft : cgraft;
      blockdelta_stxl : list sTx
    }.

Definition Block : Type :=
  prod BlockHeader BlockDelta.

Definition coinstake (b:Block) : Tx :=
  let (bh,bd) := b in
  ((stakeaddr bh,stakeassetid bh)::nil,stakeoutput bd).

Definition hitfun : Type  := option hashval -> nat -> nat -> nat -> addr -> Prop.

Definition targetfun : Type := targetinfo -> nat.

Definition hash_BlockHeader (bh:BlockHeader) : hashval :=
hashopair2 (prevblockhash bh) (hashlist (newledgerroot bh::targetinfohash bh::hashnat (timestamp bh)::hashnat (stake bh)::hashaddr (stakeaddr bh)::(stakeassetid bh)::nil)).

(*** A currency asset can be used to stake as long as it will not mature in the next 1000 blocks. (1000 is arbitrary, of course.) ***)
Definition not_close_to_mature : nat := 1000.

(*** The output from staking cannot be spent until 1000 blocks later. Again, 1000 is arbitrary here. ***)
Definition maturation_post_staking : nat := 1000.

Definition valid_BlockHeader (blockheight:nat) (check_hit : hitfun) (targetf : targetfun) (plr:hashval) (ti:targetinfo) (bh:BlockHeader) : Prop :=
  (timestamp bh > targetinfo_timestamp ti /\ hashtargetinfo ti = targetinfohash bh)
  /\
  check_signat (hash_BlockHeader bh) (blocksignat bh) (stakeaddr bh)
  /\
  check_hit (prevblockhash bh) (timestamp bh) (targetf ti) (stake bh) (stakeaddr bh)
  /\
  ctree_hashroot (prevledger bh) = plr
  /\
  (exists al m n,
     ctree_supports_asset (stakeassetid bh,((al,(m,n)),currency (stake bh))) (prevledger bh) (stakeaddr bh)
     /\
     n > blockheight + not_close_to_mature)
.

Fixpoint sTxs_allinputs (stxl : list sTx) : list addr_assetid :=
  match stxl with
    | ((inpl,_),s)::stxr => inpl ++ sTxs_allinputs stxr
    | nil => nil
  end.

Fixpoint sTxs_alloutputs (stxl : list sTx) : list addr_preasset :=
  match stxl with
    | ((_,outpl),s)::stxr => outpl ++ sTxs_alloutputs stxr
    | nil => nil
  end.

Lemma sTxs_allinputs_iff stxl alpha h :
  In (alpha,h) (sTxs_allinputs stxl) <-> exists tx, In_dom tx stxl /\ In (alpha,h) (tx_inputs tx).
induction stxl as [|[[inpl outpl] s] stxr IH]; split.
- simpl. tauto.
- intros [tx [H1 _]]. contradiction H1.
- simpl. intros H1. apply in_app_or in H1. destruct H1 as [H1|H1].
  + exists (inpl,outpl). simpl. tauto.
  + apply IH in H1. destruct H1 as [tx H2]. exists tx. tauto.
- intros [tx [[H1|H1] H2]].
  + simpl. apply in_or_app. left. rewrite H1 in H2. exact H2.
  + simpl. apply in_or_app. right. apply IH. exists tx. tauto.
Qed.

Lemma sTxs_alloutputs_iff stxl alpha u :
  In (alpha,u) (sTxs_alloutputs stxl) <-> exists tx, In_dom tx stxl /\ In (alpha,u) (tx_outputs tx).
induction stxl as [|[[inpl outpl] s] stxr IH]; split.
- simpl. tauto.
- intros [tx [H1 _]]. contradiction H1.
- simpl. intros H1. apply in_app_or in H1. destruct H1 as [H1|H1].
  + exists (inpl,outpl). simpl. tauto.
  + apply IH in H1. destruct H1 as [tx H2]. exists tx. tauto.
- intros [tx [[H1|H1] H2]].
  + simpl. apply in_or_app. left. rewrite H1 in H2. exact H2.
  + simpl. apply in_or_app. right. apply IH. exists tx. tauto.
Qed.

Definition ctree_of_Header (b:Block) : ctree 160 :=
  let (bh,bd) := b in
  prevledger bh.

Definition ctree_of_Block (b:Block) : ctree 160 :=
  let (bh,bd) := b in
  ctree_cgraft (prevledgergraft bd) (prevledger bh).

Definition timestamp_of_Block (b:Block) : nat :=
  let (bh,bd) := b in
  timestamp bh.

(*** One Tx combining all the Txs in the block, including the coinstake. ***)
Definition tx_of_Block (b:Block) : Tx :=
  let (bh,bd) := b in
  ((stakeaddr bh,stakeassetid bh)::sTxs_allinputs (blockdelta_stxl bd),stakeoutput bd ++ sTxs_alloutputs (blockdelta_stxl bd)).

Definition valid_Block (blockheight:nat) (rew:nat) (check_hit : hitfun) (targetf : targetfun) plr ti (b:Block) : Prop :=
  let (bh,bd) := b in
  (*** The header is valid. ***)
  valid_BlockHeader blockheight check_hit targetf plr ti bh
  /\
  (*** The asset staked must be one of the outputs. This is especially important if it's been loaned for staking.
        The other stake outputs must explicitly say that they cannot be spent until at least blockheight + maturation_post_staking. ***)
  (exists obl:obligation, exists i:nat,
     ctree_supports_asset (stakeassetid bh,(obl,currency (stake bh))) (prevledger bh) (stakeaddr bh)
     /\
     nth_error (stakeoutput bd) i = value (stakeaddr bh,(obl,currency (stake bh)))
     /\
     (forall alpha al m n u j, j <> i /\ nth_error (stakeoutput bd) j = value (alpha,((al,(m,n)),u)) -> n > blockheight + maturation_post_staking))
  /\
  (*** The addresses of the coinstake output are supported by the grafted ctree. ***)
  ((forall alpha ou, In (alpha,ou) (stakeoutput bd) -> ctree_supports_addr (ctree_of_Block (bh,bd)) alpha)
   /\
   (*** and the total output values match the declared stake and reward and fees ***)
   (asset_value_out (stakeoutput bd) = stake bh + rew + totalfees bd))
  /\
  (*** There are no duplicate transactions. ***)
  no_dups (blockdelta_stxl bd)
  /\
  (*** Each transaction in the delta has supported elaborated assets and has valid signatures. ***)
  (forall tx sl, In (tx,sl) (blockdelta_stxl bd) ->
                 exists einpl:list asset,
                   tx_signatures_valid blockheight einpl (tx,sl)
                   /\
                   (forall beta h, In (beta,h) (tx_inputs tx) -> exists a, In a einpl /\ assetid a = h /\ ctree_supports_asset a (ctree_of_Block (bh,bd)) beta))
  /\
  (*** Each transaction in the delta is valid. ***)
  (forall stx, In stx (blockdelta_stxl bd) -> tx_valid (fst stx))
  /\
  (*** No transaction has the stake asset as an input. ***)
  (forall tx, In_dom tx (blockdelta_stxl bd) -> ~ In (stakeaddr bh,stakeassetid bh) (tx_inputs tx))
  /\
  (*** No distinct transactions try to spend the same asset. ***)
  (forall tx1 sl1 tx2 sl2 alpha h,
     In (tx1,sl1) (blockdelta_stxl bd) ->
     In (tx2,sl2) (blockdelta_stxl bd) ->
     In (alpha,h) (tx_inputs tx1) ->
     In (alpha,h) (tx_inputs tx2) ->
     tx1 = tx2 /\ sl1 = sl2)
  /\
  (*** The cgraft is valid. ***)
  cgraft_valid (prevledgergraft bd)
  /\
  (*** Every transaction is supported by the grafted ctree with 0 reward. ***)
  (forall tx, In_dom tx (blockdelta_stxl bd)
              -> exists fee, ctree_supports_tx tx (ctree_of_Block (bh,bd)) fee 0)
  (*** The total inputs and outputs match up with the declared fee. ***)
  /\
  (exists utot:nat,
     ctree_asset_value_in (ctree_of_Block (bh,bd)) (sTxs_allinputs (blockdelta_stxl bd)) utot
     /\
     asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + (totalfees bd) = utot)
  /\
  exists T:ctree 160,
    ctree_hashroot T = newledgerroot bh
    /\ tx_octree_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) = Some T.

Inductive BlockChain : nat -> Type :=
| BlockChainGen : Block -> BlockChain 0
| BlockChainSucc n : BlockChain n -> Block -> BlockChain (S n).

Inductive BlockHeaderChain : nat -> Type :=
| BlockHeaderChainGen : BlockHeader -> BlockHeaderChain 0
| BlockHeaderChainSucc n : BlockHeaderChain n -> BlockHeader -> BlockHeaderChain (S n).

Fixpoint BlockChain_headers {n} (bc : BlockChain n) : BlockHeaderChain n :=
match bc with
| BlockChainGen (bh,_) => BlockHeaderChainGen bh
| BlockChainSucc n bc (bh,_) => BlockHeaderChainSucc n (BlockChain_headers bc) bh
end.

Definition lastledgerroot_of_BlockChain {n} (bc:BlockChain n) : hashval :=
match bc with
| BlockChainGen (bh,_) => newledgerroot bh
| BlockChainSucc n bc (bh,_) => newledgerroot bh
end.

Definition lastledgerroot_of_BlockHeaderChain {n} (bc:BlockHeaderChain n) : hashval :=
match bc with
| BlockHeaderChainGen bh => newledgerroot bh
| BlockHeaderChainSucc n bc bh => newledgerroot bh
end.

Fixpoint valid_BlockChain (rewfn:nat -> nat) (check_hit:hitfun) (targetf:targetfun) genlr genti ti {n} (bc : BlockChain n) : Prop :=
match bc with
| BlockChainGen b => valid_Block 0 (rewfn 0) check_hit targetf genlr genti b /\ ti = nexttargetinfo genti (timestamp_of_Block b)
| BlockChainSucc n bc b => exists ti', valid_BlockChain rewfn check_hit targetf genlr genti ti' bc /\ valid_Block (S n) (rewfn (S n)) check_hit targetf (lastledgerroot_of_BlockChain bc) ti' b /\ ti = nexttargetinfo ti' (timestamp_of_Block b)
end.

Fixpoint valid_BlockHeaderChain (check_hit:hitfun) (targetf:targetfun) genlr genti ti {n} (bc : BlockHeaderChain n) : Prop :=
match bc with
| BlockHeaderChainGen bh => valid_BlockHeader 0 check_hit targetf genlr genti bh /\ ti = nexttargetinfo genti (timestamp bh)
| BlockHeaderChainSucc n bc bh => exists ti', valid_BlockHeaderChain check_hit targetf genlr genti ti' bc /\ valid_BlockHeader (S n) check_hit targetf (lastledgerroot_of_BlockHeaderChain bc) ti' bh /\ ti = nexttargetinfo ti' (timestamp bh)
end.

Lemma tx_of_Block_valid blockheight rew check_hit targetf plr ti (b:Block) :
  valid_Block blockheight rew check_hit targetf plr ti b ->
  tx_valid (tx_of_Block b).
destruct b as [bh bd].
intros HvB. generalize HvB.
intros [[HvBaa [HvBab [HvBac [HvBad [HvBae HvBaf]]]]] [HvBag [HvBah [HvBb [HvBc [HvBd [HvBe [HvBf [HvBg [HvBh [HvBi HvBj]]]]]]]]]]].
split.
- simpl. discriminate.
- simpl. apply no_dups_cons.
  + intros H1. apply sTxs_allinputs_iff in H1.
    destruct H1 as [[inpl outpl] [H2 H3]].
    revert H2 H3. apply HvBe.
  + revert HvBb HvBd HvBf. unfold sTxs_allinputs. generalize (blockdelta_stxl bd).
    clear.
    (*** This could be made into a reasonable lemma instead of giving a double induction in a subproof. ***)
    induction l as [|[[inpl outpl] sl] txl IH].
    * simpl. intros H0 H1 H2. apply no_dups_nil.
    * { simpl. intros H0 H1 H2. apply no_dups_app.
        - assert (L1: (inpl, outpl, sl) = (inpl, outpl, sl) \/ In (inpl, outpl, sl) txl) by now left.
          destruct (H1 ((inpl,outpl),sl) L1) as [_ H1b].
          exact H1b.
        - apply IH.
          + inversion H0. assumption.
          + intros stx H3. apply H1. now right.
          + intros tx1 sl1 tx2 sl2 alpha h H3 H4. apply H2; now right.
        - revert H0 H2. clear.
          induction txl as [|[[inpl2 outpl2] sl2] txr IH]; intros H0 H2 [alpha h] H3.
          + simpl. tauto.
          + intros H4. apply in_app_or in H4.
            destruct H4 as [H4|H4].
            * inversion H0. apply H5. left.
              assert (L1: (inpl,outpl) = (inpl2,outpl2) /\ sl = sl2).
              { apply (H2 (inpl,outpl) sl (inpl2,outpl2) sl2 alpha h).
                - now left.
                - right. now left.
                - exact H3.
                - exact H4.
              }
              destruct L1 as [L1a L1b].
              rewrite L1a. rewrite L1b.
              reflexivity.
            * { revert H4. apply IH.
                - inversion H0. apply no_dups_cons.
                  + intros H6. apply H4. now right.
                  + inversion H5. assumption.
                - intros tx3 sl3 tx4 sl4 beta k H6 H7. apply H2.
                  + simpl. tauto.
                  + simpl. tauto.
                - exact H3.
              }
      }
Qed.

Lemma tx_of_Block_input_iff alpha h (b : Block) :
  In (alpha,h) (tx_inputs (tx_of_Block b))
  <->
  ((alpha = stakeaddr (fst b) /\ h = stakeassetid (fst b))
   \/
   exists tx sl, In (tx,sl) (blockdelta_stxl (snd b)) /\ In (alpha,h) (tx_inputs tx)).
destruct b as [bh bd]. simpl. split; intros [H1|H1].
- left. inversion H1. tauto.
- right. apply sTxs_allinputs_iff in H1.
  destruct H1 as [tx [H1 H2]]. apply In_In_dom_lem in H1.
  destruct H1 as [sl H1]. exists tx. exists sl. tauto.
- left. destruct H1 as [H2 H3]. congruence.
- right. apply sTxs_allinputs_iff. destruct H1 as [tx [sl [H1 H2]]].
  exists tx. split.
  + revert H1. apply In_In_dom_lem_2.
  + exact H2.
Qed.

Lemma tx_of_Block_output_iff alpha obju (b : Block) :
 In (alpha, obju) (tx_outputs (tx_of_Block b))
 <->
 (In (alpha, obju) (stakeoutput (snd b))
  \/
   exists tx sl, In (tx,sl) (blockdelta_stxl (snd b)) /\ In (alpha,obju) (tx_outputs tx)).
destruct b as [bh bd]. simpl. split; intros H1.
- apply in_app_or in H1. destruct H1 as [H1|H1].
  + now left.
  + right. apply sTxs_alloutputs_iff in H1.
    destruct H1 as [tx [H1 H2]]. apply In_In_dom_lem in H1.
    destruct H1 as [sl H1]. exists tx. exists sl. tauto.
- apply in_or_app. destruct H1 as [H1|H1].
  + now left.
  + right. apply sTxs_alloutputs_iff. destruct H1 as [tx [sl [H1 H2]]].
    exists tx. split.
    * revert H1. apply In_In_dom_lem_2.
    * exact H2.
Qed.

Opaque ctree_supports_addr.

(*** This lemma was pulled out from the main proof to help Coq process the main proof. ***)
Lemma tx_of_Block_supported_lem_1 blockheight rew (bh:BlockHeader) (bd:BlockDelta) utot :
  ctree_valid (ctree_of_Block (bh, bd)) ->
  subqc (prevledger bh) (ctree_of_Block (bh, bd)) ->
  (exists (al : list addr) (m n : nat),
     ctree_supports_asset
       (stakeassetid bh, (al, (m, n), currency (stake bh))) 
       (prevledger bh) (stakeaddr bh) /\
     n > blockheight + not_close_to_mature) ->
  asset_value_out (stakeoutput bd) = stake bh + rew + totalfees bd ->
  asset_value_out (sTxs_alloutputs (blockdelta_stxl bd)) + totalfees bd = utot ->
  asset_value_out (tx_outputs (tx_of_Block (bh, bd))) + 0 =
  stake bh + utot + rew.
  intros HT Lsubqc HvBae H5 H3.
  simpl. rewrite asset_value_out_app.
  omega.
Qed.

Theorem tx_of_Block_supported blockheight rew check_hit targetf plr ti (b:Block) :
  ctree_valid (ctree_of_Block b) ->
  valid_Block blockheight rew check_hit targetf plr ti b ->
  ctree_supports_tx (tx_of_Block b) (ctree_of_Block b) 0 rew.
destruct b as [bh bd]. intros HT HvB. generalize HvB.
intros [[HvBaa [HvBab [HvBac [HvBad HvBae]]]] [HvBaf [HvBag [HvBb [HvBc [HvBd [HvBe [HvBf [HvBg [HvBh [HvBi HvBj]]]]]]]]]]].
generalize HvBag. intros [HvBag1 HvBag2].
assert (Lsubqc: subqc (prevledger bh) (ctree_of_Block (bh,bd))).
{ unfold ctree_of_Block. apply ctree_cgraft_subqc. exact HvBg. }
split.
- intros alpha obju H1.
  apply tx_of_Block_output_iff in H1.
  destruct H1 as [H1|[tx' [sl' [H2 H3]]]].
  + exact (HvBag1 alpha obju H1).
  + apply In_In_dom_lem_2 in H2.
    destruct (HvBh tx' H2) as [fee [H2a _]].
    revert H3. apply H2a.
- destruct HvBi as [utot [H2 H3]].
  exists (stake bh + utot).
  split.
  + change (ctree_asset_value_in (ctree_of_Block (bh, bd))
                                 ((stakeaddr bh, stakeassetid bh)
                                    :: sTxs_allinputs (blockdelta_stxl bd))
                                 (stake bh + utot)).
    destruct HvBae as [al [m [n [H4 H5]]]].
    apply ctree_asset_value_in_cons with (a := (stakeassetid bh,((al,(m,n)),currency (stake bh)))).
    * exact H2.
    * revert H4. apply subqc_supports_asset. exact Lsubqc.
    * reflexivity.
    * reflexivity.
  + revert HT Lsubqc HvBae HvBag2 H3.
    apply tx_of_Block_supported_lem_1.
Qed.

Definition ledgerroot_valid (h:hashval) : Prop :=
  ctree_valid (ctreeH 160 h).

Opaque tx_octree_trans.

Lemma ctree_hashroot_ctree_H {n} (h:hashval) :
  ctree_hashroot (ctreeH n h) = h.
destruct n; simpl; reflexivity.
Qed.

Opaque mtree_approx_fun_p.
Opaque ctree_mtree.
Opaque tx_of_Block.
Opaque mtree_hashroot.
Opaque ctree_hashroot.
Opaque ctree_cgraft.
Opaque cgraft_assoc.
Opaque subqm.

Lemma endledgerroot_plr_valid_lem1 lroot (bh:BlockHeader) bd (f:statefun) :
  mtree_approx_fun_p (ctree_mtree (ctreeH 160 lroot)) f ->
  ctree_hashroot (prevledger bh) = lroot ->
  cgraft_valid (prevledgergraft bd) ->
  mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh, bd))) f.
intros H1 H2 H3.
apply (mtree_hashroot_mtree_approx_fun_p (ctree_mtree (ctreeH 160 lroot))).
- change (mtree_hashroot (ctree_mtree (ctreeH 160 lroot)) =
          mtree_hashroot (ctree_mtree (ctree_of_Block (bh, bd)))).
  rewrite mtree_hashroot_ctree_hashroot.
  rewrite mtree_hashroot_ctree_hashroot.
  rewrite ctree_hashroot_ctree_H.
  unfold ctree_of_Block.
  assert (L1: subqc (prevledger bh) (ctree_cgraft (prevledgergraft bd) (prevledger bh))).
  { exact (ctree_cgraft_subqc (prevledgergraft bd) (prevledger bh) H3). }
  unfold subqc in L1.
  apply subqm_hashroot_eq in L1.
  rewrite mtree_hashroot_ctree_hashroot in L1.
  rewrite mtree_hashroot_ctree_hashroot in L1.
  rewrite H2 in L1.
  exact L1.
- exact H1.
Qed.

Theorem lastledgerroot_valid rewfn check_hit targetf genlr genti ti {n} (bc : BlockChain n) :
  ledgerroot_valid genlr ->
  valid_BlockChain rewfn check_hit targetf genlr genti ti bc ->
  ledgerroot_valid (lastledgerroot_of_BlockChain bc).
intros H1. revert ti. induction bc as [[bh bd]|n bc IH [bh bd]]; intros ti.
- intros H2. generalize H2. intros [[[H2aa [H2ab [H2ac [H2ad H2ae]]]] [H2af [H2ag [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i H2j]]]]]]]]]]] Hti].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - revert H1. unfold ledgerroot_valid. unfold ctree_valid.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal. exact H2ad.
    - exact H2g.
  }
  destruct H2j as [T [H2ja H2jb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite <- H2ja.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  assert (L1: octree_supports_tx (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn 0)).
  { destruct H2 as [H2x H2y].
    exact (tx_of_Block_supported 0 (rewfn 0) check_hit targetf _ _ (bh,bd) LT H2x).
  }
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct H1 as [f [H1a H1b]].
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 genlr bh bd f H1b H2ad H2g). }
    exists (tx_statefun_trans (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (fee := 0) (rew := (rewfn 0)).
        - exact H1a.
        - destruct H2 as [H2x H2y]. revert H2x. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn 0)).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1a as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2jb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans tx' (Some T')) (tx_statefun_trans tx' f)).
          { apply (octree_approx_trans tx' (Some T') f 0 (rewfn 0)).
            - exact H1a.
            - unfold tx'. unfold T'. destruct H2 as [H2x H2y]. revert H2x. apply tx_of_Block_supported.
              exact LT.
            - unfold T'. exact LTf.
          }
          unfold octree_approx_fun_p in L5.
          exact L5.
        }
        unfold octree_mtree in L4.
        exact L4.
      }
- intros [ti' [H3 [H2 Hti]]].
  generalize H2.
  intros [[H2aa [H2ab [H2ac [H2ad H2ae]]]] [H2af [H2ag [H2b [H2c [H2d [H2e [H2f [H2g [H2h [H2i H2j]]]]]]]]]]].
  assert (LT: ctree_valid (ctree_of_Block (bh,bd))).
  { unfold ctree_of_Block. apply ctree_valid_cgraft_valid.
    - generalize (IH ti' H3). unfold ledgerroot_valid. unfold ctree_valid.
      apply mtree_hashroot_eq_valid.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite mtree_hashroot_ctree_hashroot.
      rewrite ctree_hashroot_ctree_H.
      f_equal. exact H2ad.
    - exact H2g.
  }
  destruct H2j as [T [H2ja H2jb]].
  change (ledgerroot_valid (newledgerroot bh)).
  rewrite <- H2ja.
  unfold ledgerroot_valid.
  unfold ctree_valid.
  assert (L1: octree_supports_tx (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) 0 (rewfn (S n))).
  { exact (tx_of_Block_supported (S n) (rewfn (S n)) check_hit targetf _ _ (bh,bd) LT H2). }
  apply (mtree_hashroot_eq_valid (ctree_mtree T)).
  + rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  + destruct (IH ti' H3) as [f [H1a H1b]].
    assert (LTf: octree_approx_fun_p (Some (ctree_of_Block (bh,bd))) f).
    { exact (endledgerroot_plr_valid_lem1 _ bh bd f H1b H2ad H2g). }
    exists (tx_statefun_trans (tx_of_Block (bh,bd)) f). split.
    * { apply sf_tx_valid_thm with (fee := 0) (rew := (rewfn (S n))).
        - exact H1a.
        - revert H2. apply tx_of_Block_valid.
        - assert (L2: mtree_supports_tx (tx_of_Block (bh, bd))
                                        (octree_mtree (Some (ctree_of_Block (bh, bd)))) 0 
                                        (rewfn (S n))).
          { revert L1. apply octree_mtree_supports_tx. }
          apply mtree_supports_tx_statefun with (f := f) in L2.
          + exact L2.
          + destruct H1a as [_ [Hf2 _]]. exact Hf2.
          + unfold octree_approx_fun_p in LTf.
            exact LTf.
      }
    * { assert (L4: mtree_approx_fun_p (octree_mtree (Some T)) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
        { rewrite <- H2jb.
          set (tx' := (tx_of_Block (bh,bd))).
          set (T' := (ctree_of_Block (bh,bd))).
          assert (L5: octree_approx_fun_p (tx_octree_trans tx' (Some T')) (tx_statefun_trans tx' f)).
          { apply (octree_approx_trans tx' (Some T') f 0 (rewfn (S n))).
            - exact H1a.
            - unfold tx'. unfold T'. revert H2. apply tx_of_Block_supported.
              exact LT.
            - unfold T'. exact LTf.
          }
          unfold octree_approx_fun_p in L5.
          exact L5.
        }
        unfold octree_mtree in L4.
        exact L4.
      }
Qed.

Fixpoint units_as_of_block (initdistr:nat) (rewfn:nat -> nat) (blockheight:nat) : nat :=
match blockheight with
| O => initdistr
| S n => units_as_of_block initdistr rewfn n + rewfn n
end.

Opaque sf_valid.
Opaque tx_statefun_trans.
Opaque tx_octree_trans.
Opaque mtree_approx_fun_p.

Theorem lastledgerroot_sum_correct initdistr al bl rewfn check_hit targetf genlr genti ti {n}
      (bc : BlockChain n) :
  ledgerroot_valid genlr ->
  octree_totalassets (Some (ctreeH 160 genlr)) al ->
  asset_value_sum al = initdistr ->
  valid_BlockChain rewfn check_hit targetf genlr genti ti bc ->
  octree_totalassets (Some (ctreeH 160 (lastledgerroot_of_BlockChain bc))) bl ->
  asset_value_sum bl = units_as_of_block initdistr rewfn (S n).
intros H1 H2 H3. revert bl ti.
induction bc as [[bh bd]|n bc IH [bh bd]].
- intros bl ti H4 H5.
  simpl. unfold valid_BlockChain in H4.
  generalize H4.
  intros [[[H4aa [H4ab [H4ac [H4ad H4ae]]]] [H4af [H4ag [H4b [H4c [H4d [H4e [H4f [H4g [H4h [H4i [T [HT1 HT2]]]]]]]]]]]]] Hti].
  assert (L0: ctree_hashroot (ctree_of_Block(bh,bd)) = genlr).
  { transitivity (ctree_hashroot (prevledger bh)).
    - unfold ctree_of_Block. symmetry.
      apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H4g.
    - exact H4ad.
  }
  assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
  { unfold octree_valid. revert H1. unfold ledgerroot_valid. unfold ctree_valid.
    apply mtree_hashroot_eq_valid.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L2: tx_valid (tx_of_Block (bh, bd))).
  { destruct H4 as [H4x H4y]. revert H4x. apply tx_of_Block_valid. }
  assert (L3: octree_supports_tx (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn 0)).
  { unfold octree_supports_tx.
    destruct H4 as [H4x H4y].
    revert L1 H4x. unfold octree_valid. apply tx_of_Block_supported.
  }
  generalize L1. intros [f [Hf HTf]].
  assert (L4: mtree_approx_fun_p (ctree_mtree (ctreeH 160 genlr)) f).
  { revert HTf. apply mtree_hashroot_mtree_approx_fun_p.
    rewrite mtree_hashroot_ctree_hashroot. rewrite L0.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) al).
  { unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ HTf).
    revert H2. unfold octree_totalassets. unfold octree_mtree.
    revert L4. clear. apply mtree_approx_fun_p_totalassets.
  }
  assert (L6: octree_approx_fun_p
                (tx_octree_trans (tx_of_Block (bh, bd))
                                 (Some (ctree_of_Block (bh, bd))))
                (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { apply (octree_approx_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn 0) Hf L3).
    unfold octree_approx_fun_p. unfold octree_mtree.
    exact HTf.
  }
  assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { unfold octree_approx_fun_p. rewrite <- HT2.
    exact L6.
  }
  assert (L8: octree_totalassets (tx_octree_trans (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
  { rewrite HT2.
    unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L7).
    revert H5.
    unfold octree_totalassets. unfold octree_mtree.
    apply mtree_approx_fun_p_totalassets.
    revert L7. unfold octree_approx_fun_p.
    apply mtree_hashroot_mtree_approx_fun_p.
    unfold octree_mtree.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    rewrite HT1. reflexivity.
  }
  generalize (octree_tx_asset_value_sum (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn 0) al bl L1 L2 L3 L5 L8).
  rewrite H3.
  assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
  { clear. omega. }
  rewrite L9. exact (fun H => H).
- intros bl ti [ti' [H4 [H5 Hti]]] H6.
  generalize H5.
  intros [[H5aa [H5ab [H5ac [H5ad H5ae]]]] [H5af [H5ag [H5b [H5c [H5d [H5e [H5f [H5g [H5h [H5i [T [HT1 HT2]]]]]]]]]]]]].
  assert (Lplr: ledgerroot_valid (lastledgerroot_of_BlockChain bc)).
  { revert H1 H4. apply lastledgerroot_valid. }
  generalize Lplr. intros [f [Hf Hplrf]].
  assert (LIH: asset_value_sum (totalassets_ f) = units_as_of_block initdistr rewfn (S n)).
  { apply (IH (totalassets_ f) ti').
    - exact H4.
    - unfold octree_totalassets. unfold octree_mtree.
      apply (mtree_approx_fun_p_totalassets _ _ _ Hplrf).
      reflexivity.
  }
  change (asset_value_sum bl = units_as_of_block initdistr rewfn (S n) + rewfn (S n)).
  rewrite <- LIH.
  assert (L0: ctree_hashroot (ctree_of_Block(bh,bd)) = lastledgerroot_of_BlockChain bc).
  { transitivity (ctree_hashroot (prevledger bh)).
    - unfold ctree_of_Block. symmetry.
      apply subqc_hashroot_eq. apply ctree_cgraft_subqc. exact H5g.
    - exact H5ad.
  }
  assert (L1: octree_valid (Some (ctree_of_Block (bh, bd)))).
  { unfold octree_valid. revert Lplr. unfold ledgerroot_valid. unfold ctree_valid.
    apply mtree_hashroot_eq_valid.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L2: tx_valid (tx_of_Block (bh, bd))).
  { revert H5. apply tx_of_Block_valid. }
  assert (L3: octree_supports_tx (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd))) 0 (rewfn (S n))).
  { unfold octree_supports_tx. revert L1 H5. unfold octree_valid. apply tx_of_Block_supported. }
  assert (L4: mtree_approx_fun_p (ctree_mtree (ctree_of_Block (bh,bd))) f).
  { revert Hplrf. apply mtree_hashroot_mtree_approx_fun_p.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot. rewrite L0.
    rewrite ctree_hashroot_ctree_H.
    reflexivity.
  }
  assert (L5: octree_totalassets (Some (ctree_of_Block (bh, bd))) (totalassets_ f)).
  { unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L4).
    reflexivity.
  }
  assert (L6: octree_approx_fun_p
                (tx_octree_trans (tx_of_Block (bh, bd))
                                 (Some (ctree_of_Block (bh, bd))))
                (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { apply (octree_approx_trans (tx_of_Block (bh,bd)) (Some (ctree_of_Block (bh,bd))) f 0 (rewfn (S n)) Hf L3).
    unfold octree_approx_fun_p. unfold octree_mtree.
    exact L4.
  }
  assert (L7: octree_approx_fun_p (Some T) (tx_statefun_trans (tx_of_Block (bh, bd)) f)).
  { unfold octree_approx_fun_p. rewrite <- HT2.
    exact L6.
  }
  assert (L8: octree_totalassets (tx_octree_trans (tx_of_Block (bh, bd)) (Some (ctree_of_Block (bh, bd)))) bl).
  { rewrite HT2.
    unfold octree_totalassets. unfold octree_mtree.
    apply (mtree_approx_fun_p_totalassets _ _ _ L7).
    revert H6.
    unfold octree_totalassets. unfold octree_mtree.
    apply mtree_approx_fun_p_totalassets.
    revert L7. unfold octree_approx_fun_p.
    apply mtree_hashroot_mtree_approx_fun_p.
    unfold octree_mtree.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite mtree_hashroot_ctree_hashroot.
    rewrite ctree_hashroot_ctree_H.
    rewrite HT1. reflexivity.
  }
  generalize (octree_tx_asset_value_sum (Some (ctree_of_Block (bh,bd))) (tx_of_Block (bh,bd)) 0 (rewfn (S n)) (totalassets_ f) bl L1 L2 L3 L5 L8).
  assert (L9: asset_value_sum bl + 0 = asset_value_sum bl).
  { clear. omega. }
  rewrite L9. exact (fun H => H).
Qed.
