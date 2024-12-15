Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Program.Equality.
From Coq Require Import Lists.List. Import ListNotations.
(**
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
**)
Import Nat.
From Coq Require Import Strings.String.
From Coq Require Export Sets.Ensembles.

Arguments In {U}.
Arguments Union {U}.
Arguments Singleton {U}.
Arguments Included {U}.



Definition Var: Type := string.
Definition Name: Type:= string.

Inductive Term: Type :=
| VarTerm (v: Var)
| NameTerm (m: Name)
| PrivKeyTerm (k: Name)
| PubKeyTerm (k: Name)
| PairTerm (t1 t2: Term)
| PrivEncTerm  (t: Term) (k: Name)
| PubEncTerm (t: Term) (k: Name).

Definition TermSet: Type := Ensemble Term.


Inductive dy : TermSet -> Term -> Type:=
| ax {X: TermSet} {t: Term} (inH: In X t) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (PrivKeyTerm k)) : dy X (PubKeyTerm k)
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (PairTerm t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (PrivEncTerm t k)) (kH: dy X (PrivKeyTerm k)): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (PrivKeyTerm k)) : dy X (PrivEncTerm t k)
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (PubEncTerm t k)) (keyH: dy X (PrivKeyTerm k)): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (PubKeyTerm k)) : dy X (PubEncTerm t k).


Theorem TermMonotonicity: forall (X Y: TermSet) (t: Term), (dy X t) -> (Included X Y) -> (dy Y t).
Proof. intros X Y t. intros dyxt subset. induction dyxt.
       - subst. apply (ax (subset t inH)).
       - apply  (pk (IHdyxt subset)).
       - apply (splitL (IHdyxt subset)).
       - apply (splitR (IHdyxt subset)).
       - apply (pair (IHdyxt1 subset) (IHdyxt2 subset)).
       - apply (sdec (IHdyxt1 subset) (IHdyxt2 subset)).
       - apply (senc (IHdyxt1 subset) (IHdyxt2 subset)).
       - apply (adec (IHdyxt1 subset) (IHdyxt2 subset)).
       - apply (aenc (IHdyxt1 subset) (IHdyxt2 subset)).
Qed. 

Fixpoint isNormal {X: TermSet} {t: Term} (proof: dy X t) : bool := 
  match proof with
  | pair p1 p2 => andb (isNormal p1) (isNormal p2)
  | senc pt pK => andb (isNormal pt) (isNormal pK)
  | aenc pt pK => andb (isNormal pt) (isNormal pK)
  | pk pK => isNormal pK
                      
  | ax _ => true
  | splitL p =>
      andb (isNormal p)
        (match p return bool with
         | pair _ _ => false
         | senc _ _ => false
         | aenc _ _ => false
         | pk _ => false
         | splitL _ => true
         | splitR _ => true
         | sdec _ _ => true
         | adec _ _ => true
         | ax _ => true
         end)
  | splitR p =>
      andb (isNormal p)
        (match p with | pair _ _ => false
                 | senc _ _ => false
                 | aenc _ _ => false
                 | pk _ => false
                 | _ => true
         end)
  | sdec pe pK =>
      andb (isNormal pe)
        (andb (isNormal pK)
           (match pe with | pair _ _ => false
                     | senc _ _ => false
                     | aenc _ _ => false
                     | pk _ => false
                     | _ => true
            end))
  | adec pe pK =>
        (andb (isNormal pe)
           (andb (isNormal pK) (match pe with | pair _ _ => false
                                         | senc _ _ => false
                                         | aenc _ _ => false
                                         | pk _ => false
                                         | _ => true end)))
  end.


Theorem TermNormalisation :forall (X: TermSet) (t: Term) (proof: dy X t), exists (normal_proof: dy X t), (isNormal normal_proof) = true.
Proof.
  intros X t proof. induction proof.
  - exists (ax inH). simpl. reflexivity.
    
  - destruct IHproof. exists (pk x). simpl. apply H.
    
  - destruct IHproof. dependent destruction x.
    + exists (splitL (ax inH)). reflexivity.
    + exists (splitL (splitL x)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists (splitL (splitR x)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists x1. simpl in H. apply andb_true_iff in H. destruct H. apply H.
    + exists (splitL (sdec x1 x2)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists (splitL (adec x1 x2)). simpl in H. simpl. rewrite -> H. reflexivity.
      
  - destruct IHproof. dependent destruction x.
    + exists (splitR (ax inH)). reflexivity.
    + exists (splitR (splitL x)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists (splitR (splitR x)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists x2. simpl in H. apply andb_true_iff in H. destruct H. apply H0.
    + exists (splitR (sdec x1 x2)). simpl in H. simpl. rewrite -> H. reflexivity.
    + exists (splitR (adec x1 x2)). simpl in H. simpl. rewrite -> H. reflexivity.
      
  - destruct IHproof1. destruct IHproof2. exists (pair x x0). simpl. rewrite -> H. rewrite -> H0. reflexivity.
    
  - destruct IHproof1. destruct IHproof2. dependent destruction x.
    + exists (sdec (ax inH) x0). simpl. rewrite -> H0. reflexivity.
    + exists (sdec (splitL x) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists (sdec (splitR x) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists (sdec (sdec x1 x2) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists x1. simpl in H. apply andb_true_iff in H. destruct H. apply H.
    + exists (sdec (adec x1 x2) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
      
  - destruct IHproof1. destruct IHproof2. exists (senc x x0). simpl. rewrite -> H. rewrite -> H0. reflexivity.
    
  - destruct IHproof1. destruct IHproof2. dependent destruction x.
    + exists (adec (ax inH) x0). simpl. rewrite -> H0. reflexivity.
    + exists (adec (splitL x) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists (adec (splitR x) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists (adec (sdec x1 x2) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists (adec (adec x1 x2) x0). simpl. simpl in H. rewrite -> H. rewrite -> H0. reflexivity.
    + exists x1. simpl in H. apply andb_true_iff in H. destruct H. apply H.
      
  - destruct IHproof1. destruct IHproof2. exists (aenc x x0). simpl. rewrite -> H. rewrite -> H0. reflexivity.
Qed.


Inductive SubTerm: Term -> Term -> Prop:=
| SubTermRefl (t: Term) : SubTerm t t
| SubTermTrans {t1 t2 t3: Term} (r1: SubTerm t1 t2) (r2: SubTerm t2 t3) : SubTerm t1 t3

| SubTermPrivPub (k: Name): SubTerm (PrivKeyTerm k) (PubKeyTerm k)
                                                                                  
| SubTermPairLeft (t1 t2: Term) : SubTerm t1 (PairTerm t1 t2)
| SubTermPairRight (t1 t2: Term) : SubTerm t2 (PairTerm t1 t2)
                                           
| SubTermPrivEncTerm (t : Term) (k: Name) : SubTerm t (PrivEncTerm t k)
| SubTermPrivEncKey (t: Term) (k: Name) : SubTerm (PrivKeyTerm k) (PrivEncTerm t k)

| SubTermPubEncTerm (t : Term) (k: Name) : SubTerm t (PubEncTerm t k)
| SubTermPubEncKey (t: Term) (k: Name) : SubTerm (PubKeyTerm k) (PubEncTerm t k).

Inductive SubTermSet (S: TermSet) : TermSet :=
| SubTermSetCons {t: Term} (proof: exists (t': Term), (In S t') /\ (SubTerm t t')) : In (SubTermSet S) t.

Fixpoint ProofTerms {X: TermSet} {t: Term} (proof: dy X t) : TermSet :=
  match proof with
  | @ax _ t _  => Singleton t
  | @pk _ k kH => Union (Singleton (PubKeyTerm k)) (ProofTerms kH)

  | @splitL _ t1 _ splitH => Union (Singleton t1) (ProofTerms splitH)
  | @splitR _ _ t2 splitH =>  Union (Singleton t2) (ProofTerms splitH)
  | @pair _ t1 t2 t1H t2H => Union (Singleton (PairTerm t1 t2)) (Union (ProofTerms t1H) (ProofTerms t2H))
                        
  | @sdec _ t' _ encH kH => Union (Singleton t') (Union (ProofTerms encH) (ProofTerms kH))
  | @senc _ t' k tH kH => Union (Singleton (PrivEncTerm t' k)) (Union (ProofTerms tH) (ProofTerms kH))
                        
  | @adec _ t' _ encH kH => Union (Singleton t') (Union (ProofTerms encH) (ProofTerms kH))
  | @aenc _ t' k tH kH =>  Union (Singleton (PubEncTerm t' k)) (Union (ProofTerms tH) (ProofTerms kH))
  end.
Lemma TermInSubTermSet {x: Term} {S: TermSet} : In S x -> In (SubTermSet S) x.
Proof.
  intros inS.
  assert (H : exists (somet: Term), (In S somet) /\ (SubTerm x somet)). {
    exists x. split. apply inS. apply (SubTermRefl x).
  } apply (SubTermSetCons S H).
Qed.
  
Lemma UnionSubTermLeft {x: Term} {S T: TermSet}:  (In (SubTermSet S) x) -> (In (SubTermSet (Union S T)) x).
Proof.
  intros inSubS. inversion inSubS. subst.
  assert (H : exists (somet: Term), (In (Union S T) somet) /\ (SubTerm x somet)). {
    destruct proof. destruct H. exists x0. split.
    - apply (Union_introl Term S T x0 H).
    - apply H0.
  } apply (SubTermSetCons (Union S T) H).
Qed.

Lemma UnionSubTermRight {x: Term} {S T: TermSet}: (In (SubTermSet T) x) -> (In (SubTermSet (Union S T)) x).
Proof.
  intros inSubT. inversion inSubT. subst.
  assert (H : exists (somet: Term), (In (Union S T) somet) /\ (SubTerm x somet)). {
    destruct proof. destruct H. exists x0. split.
    - apply (Union_intror Term S T x0 H).
    - apply H0.
  } apply (SubTermSetCons (Union S T) H).
Qed.

Lemma BiggerFish {X: TermSet} {t t': Term}: SubTerm t t' -> In (SubTermSet X) t' -> In (SubTermSet X) t.
Proof.
  intros sub inbigfish. inversion inbigfish. subst.
  assert (H : exists (somet: Term), (In X somet) /\ (SubTerm t somet)). {
    destruct proof. destruct H. exists x. split.
    - apply H.
    - apply (SubTermTrans sub H0).
  } apply (SubTermSetCons X H).
Qed.

Lemma ResultInProofTerms {X: TermSet} {t: Term} (proof: dy X t) : In (ProofTerms proof) t.
Proof.
  destruct proof; simpl.
  - apply (In_singleton Term t).
  - apply (Union_introl Term (Singleton (PubKeyTerm k)) (ProofTerms proof) (PubKeyTerm (k)) (In_singleton Term (PubKeyTerm k))).
  - apply (Union_introl Term (Singleton t1) (ProofTerms proof) t1 (In_singleton Term t1)).
  - apply (Union_introl Term (Singleton t2) (ProofTerms proof) t2 (In_singleton Term t2)).
  - apply (Union_introl Term (Singleton (PairTerm t1 t2)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm t1 t2) (In_singleton Term (PairTerm t1 t2))).
  - apply (Union_introl Term (Singleton t) (Union (ProofTerms proof1) (ProofTerms proof2)) t (In_singleton Term t)).
  - apply (Union_introl Term (Singleton (PrivEncTerm t k)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PrivEncTerm t k) (In_singleton Term (PrivEncTerm t k))).
  - apply (Union_introl Term (Singleton t) (Union (ProofTerms proof1) (ProofTerms proof2)) t (In_singleton Term t)).
  - apply (Union_introl Term (Singleton (PubEncTerm t k)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PubEncTerm t k) (In_singleton Term (PubEncTerm t k))).
Qed.

Theorem SubTermProperty: forall (X: TermSet) (t: Term) (p: dy X t), ((isNormal p) = true)
                                                                       -> match p return Prop with
                                                                          | pair _ _ => (Included
                                                                                           (ProofTerms p)
                                                                                           (SubTermSet (Union X (Singleton t))))
                                                                          | senc _ _ => (Included
                                                                                           (ProofTerms p)
                                                                                           (SubTermSet (Union X (Singleton t))))
                                                                          | aenc _ _ => (Included
                                                                                           (ProofTerms p)
                                                                                           (SubTermSet (Union X (Singleton t))))
                                                                          | pk _ => (Included
                                                                                       (ProofTerms p)
                                                                                       (SubTermSet (Union X (Singleton t))))
                                                                          | _ => (Included
                                                                                    (ProofTerms p)
                                                                                    (SubTermSet X))

                                                                          end.


Proof.
  intros X t proof. induction proof.
  - intros eq. simpl.  intros x inSingleton. inversion inSingleton. subst. assert (H : exists (somet: Term), (In X somet) /\ (SubTerm x somet)). {
      exists x. split. apply inH. apply (SubTermRefl x).
    } apply (SubTermSetCons X H).
  - intros eq. simpl in eq. pose (IHproof eq) as proofsub. assert (proofsub': Included (ProofTerms proof) (SubTermSet (Union X (Singleton (PrivKeyTerm k))))). {
      dependent destruction proof; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub x inpterms))).
    }
    clear proofsub. clear IHproof. clear eq. simpl. intros x. intros unionterm. destruct unionterm.
    + apply (UnionSubTermRight (TermInSubTermSet H)).
    +  assert (H': Included (SubTermSet (Union X (Singleton (PrivKeyTerm k))))
                    (SubTermSet (Union X (Singleton (PubKeyTerm k))))).
      {
        intros x' sub. destruct sub. destruct proof0. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PubKeyTerm k)) somet /\ SubTerm t somet). {exists (PubKeyTerm k). split. apply (In_singleton Term (PubKeyTerm k)). apply (SubTermTrans H1 (SubTermPrivPub k)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PubKeyTerm k)) req)).
      } apply (H' x (proofsub' x H)).

        
  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq. pose (IHproof H) as proofsub. dependent destruction proof.
    + simpl. simpl in proofsub. intros x. pose (proofsub x) as xsub. intros unionterm. destruct unionterm.
      * inversion H1. subst. assert (H' : exists t, (In X t) /\ SubTerm x t). {
          exists (PairTerm x t2). split. apply inH. apply (SubTermPairLeft x t2).
        } apply (SubTermSetCons X H').
      * inversion H1. subst. apply (TermInSubTermSet inH).
    + simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
      * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm x t2)). {
          pose (proofsub (PairTerm x t2)) as goalsub. apply goalsub.
          apply (Union_introl Term (Singleton (PairTerm x t2) ) (ProofTerms proof) (PairTerm x t2)
                   (In_singleton Term (PairTerm x t2))).
        } apply (BiggerFish (SubTermPairLeft x t2) bigfish).
      * apply (proofsub x H1).
    +  simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
       * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm x t2)). {
          pose (proofsub (PairTerm x t2)) as goalsub. apply goalsub.
          apply (Union_introl Term (Singleton (PairTerm x t2) ) (ProofTerms proof) (PairTerm x t2)
                   (In_singleton Term (PairTerm x t2))).
        } apply (BiggerFish (SubTermPairLeft x t2) bigfish).
      * apply (proofsub x H1).
    +  discriminate H0.
    +  simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
       * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm x t2)). {
          pose (proofsub (PairTerm x t2)) as goalsub. apply goalsub.
          apply (Union_introl Term
                   (Singleton (PairTerm x t2)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm x t2)
                   (In_singleton Term (PairTerm x t2))).
        } apply (BiggerFish (SubTermPairLeft x t2) bigfish).
      * apply (proofsub x H1).
    + simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
       * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm x t2)). {
          pose (proofsub (PairTerm x t2)) as goalsub. apply goalsub.
          apply (Union_introl Term
                   (Singleton (PairTerm x t2)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm x t2)
                   (In_singleton Term (PairTerm x t2))).
        } apply (BiggerFish (SubTermPairLeft x t2) bigfish).
       * apply (proofsub x H1).

  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq. pose (IHproof H) as proofsub. dependent destruction proof.
    + simpl. simpl in proofsub. intros x. pose (proofsub x) as xsub. intros unionterm. destruct unionterm.
      * inversion H1. subst. assert (H' : exists t, (In X t) /\ SubTerm x t). {
          exists (PairTerm t1 x). split. apply inH. apply (SubTermPairRight t1 x).
        } apply (SubTermSetCons X H').
      * inversion H1. subst. apply (TermInSubTermSet inH).

    + simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
      * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm t1 x)). {
          pose (proofsub (PairTerm t1 x)) as goalsub. apply goalsub.
          apply (Union_introl Term (Singleton (PairTerm t1 x) ) (ProofTerms proof) (PairTerm t1 x)
                   (In_singleton Term (PairTerm t1 x))).
        } apply (BiggerFish (SubTermPairRight t1 x) bigfish).
      * apply (proofsub x H1).
    +  simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
       * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm t1 x)). {
           pose (proofsub (PairTerm t1 x)) as goalsub. apply goalsub.
           apply (Union_introl Term (Singleton (PairTerm t1 x) ) (ProofTerms proof) (PairTerm t1 x)
                    (In_singleton Term (PairTerm t1 x))).
         } apply (BiggerFish (SubTermPairRight t1 x) bigfish).
       * apply (proofsub x H1).
    +  discriminate H0.
    +  simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
       * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm t1 x)). {
           pose (proofsub (PairTerm t1 x)) as goalsub. apply goalsub.
           apply (Union_introl Term
                    (Singleton (PairTerm t1 x)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm t1 x)
                    (In_singleton Term (PairTerm t1 x))).
         } apply (BiggerFish (SubTermPairRight t1 x) bigfish).
       * apply (proofsub x H1).
    + simpl. simpl in proofsub. intros x. intros unionterm. destruct unionterm.
      * inversion H1. subst. assert (bigfish: In (SubTermSet X) (PairTerm t1 x)). {
          pose (proofsub (PairTerm t1 x)) as goalsub. apply goalsub.
          apply (Union_introl Term
                   (Singleton (PairTerm t1 x)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm t1 x)
                   (In_singleton Term (PairTerm t1 x))).
        } apply (BiggerFish (SubTermPairRight t1 x) bigfish).
      * apply (proofsub x H1).
  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2.
    assert (proofsub1': Included (ProofTerms proof1) (SubTermSet (Union X (Singleton t1)))). {
      clear proofsub2. clear IHproof2. clear eq2. clear proof2.
      destruct proof1 ; try auto ; try (intros x; intros test1; pose (proofsub1 x test1) as nicesub; apply (UnionSubTermLeft nicesub)).
    }
    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton t2)))). {
      clear proofsub1. clear IHproof1. clear eq1. clear proofsub1'. clear proof1.
      destruct proof2 ; try auto ; try (intros x; intros test2; pose (proofsub2 x test2) as nicesub; apply (UnionSubTermLeft nicesub)).
    }
    clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2.
    simpl. intros x. intros unionterm. destruct unionterm.
    + inversion H. subst. apply (UnionSubTermRight (TermInSubTermSet (In_singleton Term (PairTerm t1 t2)))).
    + assert (H1: Included (SubTermSet (Union X (Singleton t1)))
                    (SubTermSet (Union X (Singleton (PairTerm t1 t2))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PairTerm x0 t2)) somet /\ SubTerm t somet). {exists (PairTerm x0 t2). split. apply (In_singleton Term (PairTerm x0 t2)). apply (SubTermTrans H1 (SubTermPairLeft x0 t2)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PairTerm x0 t2)) req)).
      }

      assert (H2: Included (SubTermSet (Union X (Singleton t2)))
                    (SubTermSet (Union X (Singleton (PairTerm t1 t2))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t somet). {exists x0. split. apply H0. apply H2.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PairTerm t1 x0)) somet /\ SubTerm t somet). {exists (PairTerm t1 x0). split. apply (In_singleton Term (PairTerm t1 x0)). apply (SubTermTrans H2 (SubTermPairRight t1 x0)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PairTerm t1 x0)) req)).
      }
      destruct H.
      * apply (H1 x (proofsub1' x H)).
      * apply (H2 x (proofsub2' x H)).
  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. apply andb_true_iff in eq2. destruct eq2 as [eq2  sanity]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2.

    assert (proofsub1': Included (ProofTerms proof1) (SubTermSet X) ). {
      destruct proof1; auto; try discriminate sanity.
    }

    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (PrivKeyTerm k))))). {
      dependent destruction proof2 ; auto ; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).

    } clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. clear sanity. simpl. intros x unionterm. destruct unionterm.
    + inversion H. subst. pose (proofsub1' (PrivEncTerm x k) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermPrivEncTerm x k) bigfish).
    + destruct H.
      ++ apply (proofsub1' x H).
      ++ pose (proofsub2' x H) as xsub2'. destruct xsub2'. destruct proof. destruct H0. destruct H0.
      * assert (H': exists (somet: Term), In X somet /\ SubTerm t0 somet). { exists x. split. apply H0. apply H1. } apply (SubTermSetCons X H').
      * inversion H0. subst. pose (proofsub1' (PrivEncTerm t k) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermTrans H1 (SubTermPrivEncKey t k)) bigfish).
  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2. simpl.

    assert(proofsub1': Included (ProofTerms proof1) (SubTermSet (Union X (Singleton t)))). {
        dependent destruction proof1; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub1 x inpterms))).
        }

        assert(proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (PrivKeyTerm k))))). {
        dependent destruction proof2; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).
        }
        clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. intros x. intros unionterm. destruct unionterm.
        + inversion H. subst. apply (UnionSubTermRight (TermInSubTermSet (In_singleton Term (PrivEncTerm t k)))).
        + assert (H1: Included (SubTermSet (Union X (Singleton t)))
                    (SubTermSet (Union X (Singleton (PrivEncTerm t k))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PrivEncTerm x0 k)) somet /\ SubTerm t0 somet). {exists (PrivEncTerm x0 k). split. apply (In_singleton Term (PrivEncTerm x0 k)). apply (SubTermTrans H1 (SubTermPrivEncTerm x0 k)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PrivEncTerm x0 k)) req)).
      }

      assert (H2: Included (SubTermSet (Union X (Singleton (PrivKeyTerm k))))
                    (SubTermSet (Union X (Singleton (PrivEncTerm t k))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H2.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PrivEncTerm t k)) somet /\ SubTerm t0 somet). {exists (PrivEncTerm t k). split. apply (In_singleton Term (PrivEncTerm t k)). apply (SubTermTrans H2 (SubTermPrivEncKey t k)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PrivEncTerm t k)) req)).
      }

      destruct H.
          * apply (H1 x (proofsub1' x H)).
          * apply (H2 x (proofsub2' x H)).

  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. apply andb_true_iff in eq2. destruct eq2 as [eq2  sanity]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2.

    assert (proofsub1': Included (ProofTerms proof1) (SubTermSet X) ). {
      destruct proof1; auto; try discriminate sanity.
    }

    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (PrivKeyTerm k))))). {
      dependent destruction proof2 ; auto ; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).

    } clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. clear sanity. simpl. intros x unionterm. destruct unionterm.
    + inversion H. subst. pose (proofsub1' (PubEncTerm x k) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermPubEncTerm x k) bigfish).
    + destruct H.
      ++ apply (proofsub1' x H).
      ++ pose (proofsub2' x H) as xsub2'. destruct xsub2'. destruct proof. destruct H0. destruct H0.
      * assert (H': exists (somet: Term), In X somet /\ SubTerm t0 somet). { exists x. split. apply H0. apply H1. } apply (SubTermSetCons X H').
      * inversion H0. subst. pose (proofsub1' (PubEncTerm t k) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermTrans H1 (SubTermTrans (SubTermPrivPub k)(SubTermPubEncKey t k))) bigfish).

  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2. simpl.

    assert(proofsub1': Included (ProofTerms proof1) (SubTermSet (Union X (Singleton t)))). {
        dependent destruction proof1; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub1 x inpterms))).
        }

        assert(proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (PubKeyTerm k))))). {
        dependent destruction proof2; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).
        }
        clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. intros x. intros unionterm. destruct unionterm.
        + inversion H. subst. apply (UnionSubTermRight (TermInSubTermSet (In_singleton Term (PubEncTerm t k)))).
        + assert (H1: Included (SubTermSet (Union X (Singleton t)))
                    (SubTermSet (Union X (Singleton (PubEncTerm t k))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PubEncTerm x0 k)) somet /\ SubTerm t0 somet). {exists (PubEncTerm x0 k). split. apply (In_singleton Term (PubEncTerm x0 k)). apply (SubTermTrans H1 (SubTermPubEncTerm x0 k)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PubEncTerm x0 k)) req)).
      }

      assert (H2: Included (SubTermSet (Union X (Singleton (PubKeyTerm k))))
                    (SubTermSet (Union X (Singleton (PubEncTerm t k))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H2.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (PubEncTerm t k)) somet /\ SubTerm t0 somet). {exists (PubEncTerm t k). split. apply (In_singleton Term (PubEncTerm t k)). apply (SubTermTrans H2 (SubTermPubEncKey t k)).} apply (UnionSubTermRight (SubTermSetCons (Singleton (PubEncTerm t k)) req)).
      }

      destruct H.
          * apply (H1 x (proofsub1' x H)).
          * apply (H2 x (proofsub2' x H)).
Qed.

Fixpoint nPred (n: nat) : Type :=
  match n with
  | O => Prop
  | S n' => Term -> (nPred n')
  end.

Inductive TermVector: nat -> Type :=
  | noterms : TermVector 0
  | consterm {n: nat} (hd: Term) (tl: TermVector n): TermVector (S n).


Inductive Assertion: Type :=
| EqTerm (t u: Term)
| NAryPredicate {n: nat} (P: nPred n) (t: TermVector n)
| Member {n: nat} {t0: Term} (t: TermVector n)
| Conj (a0 a1 : Assertion)
| Exists (afun: Term -> Assertion)
| Says (k: Name) (a: Assertion).         
