(** Copyright (c) 2015 Bill White **)
(** Distributed under the MIT/X11 software license **)
(** See http://www.opensource.org/licenses/mit-license.php **)

(** Assets: Representation of assets as triples:
    (hashval) id
    (obligation) obligations to be met in order to spend the asset
    (preasset) the kind of asset
    In addition to currency units a 'publication' preasset with no value
    is included to simulate 'proof of existence' applications.
    The obligation is (al,(m,n)) where al is a list of addresses that can sign to spend,
    m is the number of addresses that must sign, and n is the block height
    at which spending is first allowed.
 **)

Require Export CryptoSignatures.

Inductive preasset : Type :=
| currency : nat -> preasset (*** currency u is u units of currency ***)
| publication : nat -> preasset (*** data ***)
.

(*** (al,(m,b)) : obligation
 means at least m of the addresses must sign and the block
 height must be at least b in order to use (e.g., spend) the asset.
 ***)
Definition obligation : Type := prod (list addr) (prod nat nat).

Definition mk_obligation (al:list addr) (m b:nat) := (al,(m,b)).

Definition preasset_value (u:preasset) : option nat :=
  match u with
    | currency v => Some v
    | _ => None
  end.

Definition asset : Type := prod hashval (prod obligation preasset).

Definition assetid (a:asset) : hashval := fst a.
Definition assetobl (a:asset) : obligation := fst (snd a).
Definition assetpre (a:asset) : preasset := snd (snd a).

Definition asset_value (a:asset) : option nat := preasset_value (assetpre a).

Definition hashpreasset (a:preasset) : hashval :=
match a with
| currency u => hashpair (hashnat 0) (hashnat u)
| publication d => hashpair (hashnat 1) (hashnat d)
end.

Definition hashobligation (obl:obligation) : hashval :=
match obl with
| (al,(m,b)) =>
  hashpair (hashlist (map hashaddr al)) (hashpair (hashnat m) (hashnat b))
end.

Definition hashasset (a:asset) : hashval :=
match a with
| (h,(obl,p)) =>
  hashpair h (hashpair (hashobligation obl) (hashpreasset p))
end.

Lemma hashpreassetinj a b :
hashpreasset a = hashpreasset b -> a = b.
destruct a as [u|d]; destruct b as [v|d'];
  try (simpl; intros H1; exfalso; apply hashpairinj in H1; destruct H1 as [H1 _]; apply hashnatinj in H1; omega).
- simpl. intros H1.
  apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashnatinj in H1.
  congruence.
- simpl. intros H1. apply hashpairinj in H1. destruct H1 as [_ H1].
  apply hashnatinj in H1.
  congruence.
Qed.

Lemma hashobligationinj (obl obl':obligation) :
  hashobligation obl = hashobligation obl' -> obl = obl'.
destruct obl as [al [m b]]. destruct obl' as [al' [m' b']].
simpl. intros H1.
apply hashpairinj in H1. destruct H1 as [H2 H3].
apply hashpairinj in H3. destruct H3 as [H4 H5].
apply hashnatinj in H4. apply hashnatinj in H5.
apply hashlistinj in H2. apply hashmapinj in H2.
- congruence.
- exact hashaddrinj.
Qed.

Lemma hashassetinj a b :
hashasset a = hashasset b -> a = b.
destruct a as [h [obl u]]. destruct b as [k [obl' v]].
simpl. intros H1.
apply hashpairinj in H1. destruct H1 as [H2 H3].
apply hashpairinj in H3. destruct H3 as [H4 H5].
apply hashobligationinj in H4.
apply hashpreassetinj in H5.
congruence.
Qed.

Definition addr_assetid : Type := prod addr hashval.
Definition addr_preasset : Type := prod addr (prod obligation preasset).
Definition addr_asset : Type := prod addr asset.

Definition hash_addr_assetid (aa : addr_assetid) : hashval :=
let (alpha,h) := aa in
hashpair (hashaddr alpha) h.

Definition hash_addr_preasset (au : addr_preasset) : hashval :=
match au with
| (alpha,(obl,u)) => hashlist ((hashaddr alpha)::(hashobligation obl)::(hashpreasset u)::nil)
end.

Lemma hash_addr_assetidinj alpha a beta b :
 hash_addr_assetid (alpha,a) = hash_addr_assetid (beta,b)
 -> alpha = beta /\ a = b.
unfold hash_addr_assetid. intros H1.
apply hashpairinj in H1. destruct H1 as [H2 H3].
apply hashaddrinj in H2. tauto.
Qed.

Lemma map_hash_addr_assetidinj inpl inpl' :
 map hash_addr_assetid inpl = map hash_addr_assetid inpl'
 -> inpl = inpl'.
revert inpl'. induction inpl as [|[alpha a] inpr IH].
- intros [|[beta b] inpr'].
  + reflexivity.
  + intros H1. discriminate H1.
- intros [|[beta b] inpr'].
  + intros H1. discriminate H1.
  + intros H1.
    change ((hash_addr_assetid (alpha, a) :: map hash_addr_assetid inpr) =
            (hash_addr_assetid (beta, b) :: map hash_addr_assetid inpr')) in H1.
    f_equal.
    * assert (L1: alpha = beta /\ a = b).
      { apply hash_addr_assetidinj. congruence. }
      destruct L1 as [L1a L1b]. congruence.
    * apply IH. congruence.
Qed.

Lemma hash_addr_preassetinj au bv :
  hash_addr_preasset au = hash_addr_preasset bv
  -> au = bv.
destruct au as [alpha [obl u]], bv as [beta [obl' v]].
intros H1. unfold hash_addr_preasset in H1.
apply hashlistinj in H1.
inversion H1. apply hashaddrinj in H0. subst beta.
apply hashobligationinj in H2.
apply hashpreassetinj in H3.
congruence.
Qed.

Lemma map_hash_addr_preassetinj outpl outpl' :
 map hash_addr_preasset outpl = map hash_addr_preasset outpl'
 -> outpl = outpl'.
revert outpl'. induction outpl as [|[alpha u] outpr IH].
- intros [|[beta v] outpr'].
  + reflexivity.
  + intros H1. discriminate H1.
- intros [|[beta v] outpr'].
  + intros H1. discriminate H1.
  + intros H1.
    change ((hash_addr_preasset (alpha, u) :: map hash_addr_preasset outpr) =
            (hash_addr_preasset (beta, v) :: map hash_addr_preasset outpr')) in H1.
    f_equal.
    * apply hash_addr_preassetinj. congruence.
    * apply IH. congruence.
Qed.

Fixpoint asset_value_out (outpl:list addr_preasset) : nat :=
match outpl with
| (alpha,(obl,currency u))::outpr => u + asset_value_out outpr
| (alpha,_)::outpr => asset_value_out outpr
| nil => 0
end.

Lemma asset_value_out_app (l r:list addr_preasset) :
  asset_value_out (l ++ r) = asset_value_out l + asset_value_out r.
induction l as [|[beta [obl u]] l IH].
- simpl. reflexivity.
- simpl. destruct u as [u|d]; simpl; omega.
Qed.

Definition preasset_eq_dec (a1 a2:preasset) : {a1 = a2} + {a1 <> a2}.
destruct a1 as [u|d]; destruct a2 as [v|d']; try (right; discriminate).
- destruct (eq_nat_dec u v) as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
- destruct (eq_nat_dec d d') as [D1|D1].
  + left. congruence.
  + right. intros H1. inversion H1. tauto.
Defined.

Definition obligation_eq_dec (obl1 obl2 : obligation) : { obl1 = obl2 } + { obl1 <> obl2 }.
destruct obl1 as [al1 [m1 b1]]. destruct obl2 as [al2 [m2 b2]].
destruct (eq_nat_dec m1 m2) as [D1|D1]; try (right; congruence).
destruct (eq_nat_dec b1 b2) as [D2|D2]; try (right; congruence).
subst m2.
assert (L1: {al1 = al2} + {al1 <> al2}).
{ clear. revert al2. induction al1 as [|alpha1 al1 IH]; intros [|alpha2 al2].
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (addr_eq_dec alpha1 alpha2) as [D1|D1].
    + destruct (IH al2) as [D2|D2].
      * left. congruence.
      * right. congruence.
    + right. congruence.
}
destruct L1 as [D3|D3].
- left. congruence.
- right. intros H1. inversion H1. contradiction (D3 H0).
Defined.

Definition asset_eq_dec (a1 a2:asset) : {a1 = a2} + {a1 <> a2}.
destruct a1 as [h1 [obl1 u1]], a2 as [h2 [obl2 u2]].
destruct (hashval_eq_dec h1 h2).
- destruct (obligation_eq_dec obl1 obl2).
  + destruct (preasset_eq_dec u1 u2).
    * left. congruence.
    * right. congruence.
  + right. congruence.
- right. congruence.
Defined.

Fixpoint new_assets (alpha:addr) (aul:list addr_preasset) (txh:hashval) (i:nat) : list asset :=
match aul with
  | nil => nil
  | (beta,(obl,u))::aul' =>
    if addr_eq_dec alpha beta then
      (hashpair txh (hashnat i),(obl,u))::(new_assets alpha aul' txh (S i))
    else
      new_assets alpha aul' txh (S i)
end.

Fixpoint remove_assets (al:list asset) (spent:list hashval) : list asset :=
match al with
| nil => nil
| a::al' =>
  if in_dec hashval_eq_dec (assetid a) spent then
    remove_assets al' spent
  else
    cons a (remove_assets al' spent)
end.

Fixpoint get_spent (alpha:addr) (inpl:list addr_assetid) : list hashval :=
match inpl with
| nil => nil
| cons (beta,a) inpl' =>
  if addr_eq_dec alpha beta then
    cons a (get_spent alpha inpl')
  else
    get_spent alpha inpl'
end.

Fixpoint add_vout (txh:hashval) (outpl:list addr_preasset) (i:nat) : list (addr * asset)%type :=
match outpl with
| nil => nil
| cons (alpha,(obl,u)) outpl' => cons (alpha,(hashpair txh (hashnat i),(obl,u))) (add_vout txh outpl' (S i))
end.

Lemma new_assets_iff a alpha aul txh i :
  In a (new_assets alpha aul txh i)
  <->
  exists j, nth_error aul j = value (alpha,(assetobl a,assetpre a)) /\ assetid a = hashpair txh (hashnat (i+j)).
destruct a as [h [obl u]]. revert i. induction aul as [|[beta [obl' v]] aur IH].
- intros i. split.
  + simpl. tauto.
  + intros [[|j] [H1 _]] ; discriminate H1.
- simpl. intros i. destruct (addr_eq_dec alpha beta) as [H1|H1]; split.
  + intros [H2|H2].
    * { exists 0. simpl. split.
        - inversion H2. subst beta. reflexivity.
        - assert (L1: i + 0 = i) by omega.
          rewrite L1.
          congruence.
      }
    * { apply IH in H2. destruct H2 as [j [H3 H4]]. exists (S j). split.
        - exact H3.
        - assert (L1: i + S j = S i + j) by omega.
          rewrite L1.
          exact H4.
      }
  + intros [[|j] [H2 H3]]; simpl in *|-*.
    * { left. inversion H2. f_equal.
        assert (L1: i + 0 = i) by omega.
        rewrite L1 in H3. now symmetry.
       }
    * { right. apply IH. exists j. split.
        - assumption.
        - assert (L1: S i + j = i + S j) by omega.
          rewrite L1. assumption.
      }
  + intros H2. apply IH in H2. destruct H2 as [j [H3 H4]].
    exists (S j). split.
    * exact H3.
    * assert (L1: i + S j = S i + j) by omega.
      rewrite L1. assumption.
  + intros [[|j] [H2 H3]].
    * exfalso. simpl in H2. inversion H2. congruence.
    * { apply IH. exists j. split.
        - exact H2.
        - assert (L1: S i + j = i + S j) by omega.
          rewrite L1. assumption.
      }
Qed.

Lemma remove_assets_iff a al spent :
  In a (remove_assets al spent)
  <->
  In a al /\ ~In (assetid a) spent.
destruct a as [h [obl u]]. induction al as [|[h' [obl' u']] ar IH].
- simpl. tauto.
- simpl. destruct (in_dec hashval_eq_dec h' spent) as [H1|H1]; split.
  + intros H2. apply IH in H2. tauto.
  + intros [[H2|H2] H3].
    * congruence.
    * apply IH. tauto.
  + intros [H2|H2].
    * { split.
        - tauto.
        - inversion H2. subst h'. assumption.
      }
    * tauto.
  + intros [[H2|H2] H3].
    * now left.
    * right. tauto.
Qed.

Lemma get_spent_iff h alpha inpl :
In h (get_spent alpha inpl)
<->
In (alpha,h) inpl.
induction inpl as [|[beta h'] inpr IH].
- simpl. tauto.
- simpl. destruct (addr_eq_dec alpha beta) as [H1|H1]; split.
  + intros [H2|H2].
    * left. congruence.
    * right. tauto.
  + intros [H2|H2].
    * left. inversion H2. reflexivity.
    * right. tauto.
  + tauto.
  + intros [H2|H2].
    * congruence.
    * tauto.
Qed.

Lemma no_dups_new_assets alpha aul txh i :
  no_dups (new_assets alpha aul txh i).
revert i. induction aul as [|[beta [obl v]] aur IH]; intros i.
- simpl. apply no_dups_nil.
- simpl. destruct (addr_eq_dec alpha beta) as [H1|H1].
  + apply no_dups_cons.
    * intros H2. apply new_assets_iff in H2. destruct H2 as [j [H3 H4]].
      apply hashpairinj in H4. destruct H4 as [_ H4].
      apply hashnatinj in H4. omega.
    * apply IH.
  + apply IH.
Qed.

Lemma no_dups_remove_assets al spent :
no_dups al -> no_dups (remove_assets al spent).
intros H. induction H as [|[h [obl u]] al H1 H2 IH].
- simpl. apply no_dups_nil.
- simpl. destruct (in_dec hashval_eq_dec h spent) as [H3|H3].
  + assumption.
  + apply no_dups_cons.
    * intros H4. apply remove_assets_iff in H4. tauto.
    * assumption.
Qed.

Lemma remove_assets_noint_eq (al:list asset) (rem:list hashval) :
  (forall k, In k rem -> ~In_dom k al) ->
  remove_assets al rem = al.
induction al as [|[h [obl u]] ar IH].
- intros _. reflexivity.
- intros H1. simpl. destruct (in_dec hashval_eq_dec h rem) as [D1|D1].
  + exfalso. apply (H1 h D1). now left.
  + f_equal. apply IH. intros k H2 H3. apply (H1 k H2). now right.
Qed.

Lemma fnl_remove_assets (al:list asset) (rem:list hashval) :
  fnl al -> fnl (remove_assets al rem).
intros H. induction H as [|h u al H1 H2 IH].
- apply fnl_N.
- simpl. destruct (in_dec hashval_eq_dec h rem) as [H3|H3].
  + exact IH.
  + apply fnl_C.
    * intros H4. apply H1. apply In_In_dom_lem in H4.
      destruct H4 as [v H4].
      apply remove_assets_iff in H4. destruct H4 as [H5 H6].
      apply In_In_dom_lem. exists v. assumption.
    * exact IH.
Qed.

Definition hashassetlist (al:list asset) : option hashval := ohashlist (map hashasset al).

Lemma hashassetlistinj al bl : hashassetlist al = hashassetlist bl -> al = bl.
intros H1.
change (ohashlist (map hashasset al) = ohashlist (map hashasset bl)) in H1.
apply ohashlistinj in H1.
revert bl H1. induction al as [|a al IH]; intros [|b bl] H1.
- reflexivity.
- discriminate H1.
- discriminate H1.
- simpl in H1. inversion H1. apply hashassetinj in H0. subst b. f_equal.
  now apply IH.
Qed.

Definition asset_value_sum (al:list asset) : nat :=
fold_right plus 0 (map (fun a => match asset_value a with Some u => u | None => 0 end) al).

Lemma asset_value_sum_value_nil :
  asset_value_sum nil = 0.
reflexivity.
Qed.

Lemma asset_value_sum_value_cons a al u :
  asset_value a = Some u ->
  asset_value_sum (a::al) = u + asset_value_sum al.
intros H1. unfold asset_value_sum. simpl. rewrite H1.
reflexivity.
Qed.

Lemma asset_value_sum_novalue_cons a al :
  asset_value a = None ->
  asset_value_sum (a::al) = asset_value_sum al.
intros H1. unfold asset_value_sum. simpl. rewrite H1.
reflexivity.
Qed.

Lemma asset_value_sum_app (l r:list asset) :
asset_value_sum l
+
asset_value_sum r
= 
asset_value_sum (l ++ r).
unfold asset_value_sum. induction l as [|[h u] l IH].
- simpl. reflexivity.
- simpl. rewrite <- plus_assoc. rewrite IH. reflexivity.
Qed.

Lemma app_perm_asset_value_sum (l r:list asset) :
  app_perm l r ->
  asset_value_sum l = asset_value_sum r.
intros H. induction H as [l r|l1 r1 l2 r2 H1 IH1 H2 IH2|l|l r H1 IH1|l r s H1 IH1 H2 IH2].
- rewrite <- asset_value_sum_app. rewrite <- asset_value_sum_app. omega.
- rewrite <- asset_value_sum_app. rewrite <- asset_value_sum_app. omega.
- omega.
- omega.
- omega.
Qed.

Lemma remove_assets_app (al bl:list asset) (rl:list hashval) :
  remove_assets (al ++ bl) rl = (remove_assets al rl) ++ (remove_assets bl) rl.
induction al as [|[h u] al IH].
- reflexivity.
- simpl. destruct (in_dec hashval_eq_dec h rl) as [H1|H1].
  + exact IH.
  + rewrite IH. reflexivity.
Qed.

Lemma remove_assets_nil (l:list asset) :
  remove_assets l nil = l.
induction l as [|[h u] l IH].
- reflexivity.
- simpl. rewrite IH. reflexivity.
Qed.

Lemma remove_assets_nIn_cons (l:list asset) (h:hashval) (rem:list hashval) :
  (~exists u, In (h,u) l) ->
  remove_assets l (h::rem) = remove_assets l rem.
induction l as [|[k v] l IH]; intros H1.
- reflexivity.
- simpl. destruct (hashval_eq_dec h k) as [D1|D1].
  + exfalso. apply H1. exists v. left. congruence.
  + destruct (in_dec hashval_eq_dec k rem) as [D2|D2].
    * apply IH. intros [u H2]. apply H1. exists u. now right.
    * f_equal. apply IH. intros [u H2]. apply H1. exists u. now right.
Qed.

Lemma remove_assets_app2 (l:list asset) (rem1 rem2:list hashval) :
  remove_assets l (rem1 ++ rem2) = remove_assets (remove_assets l rem1) rem2.
induction l as [ |[k v] l IH].
- reflexivity.
- simpl. destruct (in_dec hashval_eq_dec k (rem1 ++ rem2)) as [D1|D1].
  + destruct (in_dec hashval_eq_dec k rem1) as [D2|D2].
    * exact IH.
    * { simpl. destruct (in_dec hashval_eq_dec k rem2) as [D3|D3].
        - exact IH.
        - exfalso. apply in_app_or in D1. tauto.
      }
  + destruct (in_dec hashval_eq_dec k rem1) as [D2|D2].
    * exfalso. apply D1. apply in_or_app. tauto.
    * { simpl. destruct (in_dec hashval_eq_dec k rem2) as [D3|D3].
        - exfalso. apply D1. apply in_or_app. tauto.
        - f_equal. exact IH.
      } 
Qed.

Lemma remove_assets_eq (l:list asset) (rl1 rl2:list hashval) :
  (forall h, In_dom h l -> (In h rl1 <-> In h rl2)) ->
  remove_assets l rl1 = remove_assets l rl2.
induction l as [|[h u] l IH].
- intros _. reflexivity.
- intros H1. simpl.
  destruct (in_dec hashval_eq_dec h rl1) as [H2|H2];
  destruct (in_dec hashval_eq_dec h rl2) as [H3|H3].
  + apply IH. intros k H4. apply H1. now right.
  + exfalso. apply H3. apply H1.
    * now left.
    * assumption.
  + exfalso. apply H2. apply H1.
    * now left.
    * assumption.
  + f_equal. apply IH. intros k H4. apply H1. now right.
Qed.

Lemma asset_value_sum_asset_shift (al:list asset) h a u rl :
  fnl al ->
  no_dups (h::rl) ->
  In (h,a) al ->
  asset_value (h,a) = Some u ->
  u + asset_value_sum (remove_assets al (h::rl)) = asset_value_sum (remove_assets al rl).
intros H H0. induction H as [|k v al H1 H2 IH].
- simpl. tauto.
- simpl. intros H3 E0. destruct (hashval_eq_dec h k) as [H4|H4].
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * exfalso. inversion H0. subst k. contradiction.
    * { destruct H3 as [H3|H3].
        - inversion H3.
          rewrite (asset_value_sum_value_cons _ _ _ E0).
          f_equal.
          subst k.
          apply app_perm_asset_value_sum.
          rewrite (remove_assets_eq al (h::rl) rl).
          + apply app_perm_ref.
          + intros k H8. split.
            * { intros [H9|H9].
                - exfalso. apply H1. subst k. assumption.
                - assumption.
              }
            * intros H9. now right.
        - exfalso. apply H1. apply In_In_dom_lem. exists a. subst k. assumption.
      }
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - now apply IH.
      } 
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - destruct (asset_value (k,v)) as [w|] eqn: E1.
          + rewrite (asset_value_sum_value_cons _ _ _ E1).
            rewrite (asset_value_sum_value_cons _ _ _ E1).
            apply IH in H3.
            * omega.
            * exact E0.
          + rewrite (asset_value_sum_novalue_cons _ _ E1).
            rewrite (asset_value_sum_novalue_cons _ _ E1).
            exact (IH H3 E0).
      } 
Qed.

Lemma asset_value_sum_asset_shift_non (al:list asset) h a rl :
  fnl al ->
  no_dups (h::rl) ->
  In (h,a) al ->
  asset_value (h,a) = None ->
  asset_value_sum (remove_assets al (h::rl)) = asset_value_sum (remove_assets al rl).
intros H H0. induction H as [|k v al H1 H2 IH].
- simpl. tauto.
- simpl. intros H3 H3'. destruct (hashval_eq_dec h k) as [H4|H4].
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * exfalso. inversion H0. subst k. contradiction.
    * { destruct H3 as [H3|H3].
        - inversion H3.
          rewrite (asset_value_sum_novalue_cons _ _ H3').
          change (asset_value_sum (remove_assets al (h :: rl)) = asset_value_sum (remove_assets al rl)).
          subst k.
          apply app_perm_asset_value_sum.
          rewrite (remove_assets_eq al (h::rl) rl).
          + apply app_perm_ref.
          + intros k H8. split.
            * { intros [H9|H9].
                - exfalso. apply H1. subst k. assumption.
                - assumption.
              }
            * intros H9. now right.
        - exfalso. apply H1. apply In_In_dom_lem. exists a. subst k. assumption.
      }
  + destruct (in_dec hashval_eq_dec k rl) as [H5|H5].
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - now apply IH.
      } 
    * { destruct H3 as [H3|H3].
        - inversion H3. exfalso. congruence.
        - destruct (asset_value (k,v)) as [w|] eqn: E1.
          + rewrite (asset_value_sum_value_cons _ _ _ E1).
            rewrite (asset_value_sum_value_cons _ _ _ E1).
            apply IH in H3.
            * omega.
            * exact H3'.
          + rewrite (asset_value_sum_novalue_cons _ _ E1).
            rewrite (asset_value_sum_novalue_cons _ _ E1).
            exact (IH H3 H3').
      } 
Qed.

Lemma add_vout_lem (txh:hashval) (outpl:list addr_preasset) (i:nat) alpha h u :
In (alpha,(h,u)) (add_vout txh outpl i)
<->
exists j, nth_error outpl j = value (alpha,u)
          /\ h = hashpair txh (hashnat (i + j)).
revert i. induction outpl as [|[k [obl v]] outpr IH]; intros i.
- simpl. split.
  + tauto.
  + intros [[|j] [H1 _]]; discriminate H1.
- simpl. split.
  + intros [H1|H1].
    * { inversion H1. exists 0. split.
        - reflexivity.
        - f_equal. f_equal. omega.
      }
    * { apply IH in H1. destruct H1 as [j [H2 H3]]. exists (S j). split.
        - exact H2.
        - rewrite H3. f_equal. f_equal. omega.
      }
  + intros [[|j] [H1 H2]].
    * left. simpl in H1. inversion H1. rewrite H2.
      f_equal. f_equal. f_equal. f_equal. omega.
    * { right. apply IH. exists j. split.
        - exact H1.
        - rewrite H2. f_equal. f_equal. omega.
      }
Qed.
