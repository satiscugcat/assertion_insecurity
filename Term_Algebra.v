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
Arguments Empty_set {U}.
Arguments cons {A}.

Definition Var: Type := nat.
Definition Name: Type:= nat.
Fixpoint nAryFun (n: nat) (A: Type) (B: Type) : Type :=
  match n with
  | 0 => B
  | S n' => A -> (nAryFun n' A B)
  end.

Inductive Term: Type :=
| VarTerm (v: Var)
| NameTerm (m: Name)
| PrivKeyTerm (k: Name)
| PubKeyTerm (k: Name)
| PairTerm (t1 t2: Term)
| PrivEncTerm  (t: Term) (k: Name)
| PubEncTerm (t: Term) (k: Name).

Definition TermSet: Type := Ensemble Term.

Fixpoint FVSetTerm (t: Term) : Ensemble Var :=
    match t with
    | VarTerm v => Singleton v
    | NameTerm _ => Empty_set
    | PrivKeyTerm _ => Empty_set
    | PubKeyTerm _ => Empty_set
    | PairTerm t1 t2 => Union (FVSetTerm t1) (FVSetTerm t2)
    | PrivEncTerm t' _ => FVSetTerm t'
    | PubEncTerm t' _ => FVSetTerm t'
    end.

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
  - intros eq. simpl in eq. pose (IHproof eq) as proofsub. assert (proofsub': Included (ProofTerms proof) (SubTermSet X)). {
      dependent destruction proof; auto.
    }
    clear proofsub. clear IHproof. clear eq. simpl. intros x. intros unionterm. destruct unionterm.
    + apply (UnionSubTermRight (TermInSubTermSet H)).
    +  apply (UnionSubTermLeft (proofsub' x H)).

        
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

    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (PrivKeyTerm k))) )). {
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

    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet X) ). {
      dependent destruction proof2 ; auto.

    } clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. clear sanity. simpl. intros x unionterm. destruct unionterm.
    + inversion H. subst. pose (proofsub1' (PubEncTerm x k) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermPubEncTerm x k) bigfish).
    + destruct H.
      ++ apply (proofsub1' x H).
      ++ apply (proofsub2' x H).

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



(*
Inductive TermVector: nat -> Type :=
  | VectorNull : TermVector 0
  | VectorCons {n: nat} (hd: Term) (tl: TermVector n): TermVector (S n).
 *)

Check cons.
Inductive PositionTermInTermList: list Term  -> Term -> nat -> Prop :=
| PositionVectorHead0 {n: nat} (head: Term) (tl: list Term) : PositionTermInTermList (head::tl) head 0
| PositionVectorConsSn {n i: nat} (head elem: Term) {tl: list Term} (proof: PositionTermInTermList tl elem i): PositionTermInTermList (head::tl) elem (S i).

Inductive ListLength {A: Type}: list A -> nat -> Prop :=
| Null0 : ListLength [] 0
| ConsS (head : A) {n: nat} {tail : list A} (proof: ListLength tail n) : ListLength (head::tail) (S n).

Inductive Assertion: Type :=
| EqAssertion (t u: Term)
| NAryAssertion {n: nat} (P: nAryFun n Term Prop) (tlist: list Term) (proof: ListLength tlist n)
| MemberAssertion (t0: Term) (tlist: list Term)
| AndAssertion (a0 a1 : Assertion)
| ExistsAssertion (afun: Term -> Assertion) (x: Var)
| SaysAssertion (k: Name) (a: Assertion).         

Fixpoint foldr {A B: Type} (accumulatingfun: A -> B -> B) (initial: B) (fuel: list A): B :=
  match fuel with
  | [] => initial
  | hd::tl => accumulatingfun hd (foldr accumulatingfun initial tl)
  end.
Fixpoint FVSetAssertion (a: Assertion) : Ensemble Var :=
  match a with
  | EqAssertion t u => Union (FVSetTerm t) (FVSetTerm u)
  | NAryAssertion _ tlist _ => (foldr (fun (t: Term) (ts: Ensemble Var) => Union (FVSetTerm t) ts) Empty_set tlist)
  | MemberAssertion t tlist => Union (FVSetTerm t) (foldr (fun (t: Term) (ts: Ensemble Var) => Union (FVSetTerm t) ts) Empty_set tlist)
  | AndAssertion a0 a1 => Union (FVSetAssertion a0) (FVSetAssertion a1)
  | ExistsAssertion afun x => Subtract Var (FVSetAssertion (afun (VarTerm x))) x
  | SaysAssertion _ a => FVSetAssertion a
  end.

Inductive FVSetTermSet: TermSet -> Ensemble Var :=
| FVSetTermSetCons {S: TermSet}{x: Var} (proof: exists (t: Term), In S t /\ In (FVSetTerm t) x): In (FVSetTermSet S) x.
Definition AssertionSet := Ensemble Assertion.
Inductive FVSetAssertionSet: AssertionSet -> Ensemble Var :=
| FVSetAssertionSetCons {A: AssertionSet}{x: Var} (proof: exists (a: Assertion), In A a /\ In (FVSetAssertion a) x): In (FVSetAssertionSet A) x.


Inductive TermSubTermPosition: Term -> Term -> list nat -> Prop :=
| TermTermEpsilon {t: Term}: TermSubTermPosition t t []
                                                 
| TermPairTermLeft0 {t t1 t2: Term} {pos: list nat} (proof: TermSubTermPosition t (PairTerm t1 t2) pos) : TermSubTermPosition t t1 (0::pos)
| TermPairTermRight1 {t t1 t2: Term} {pos: list nat} (proof: TermSubTermPosition t (PairTerm t1 t2) pos) : TermSubTermPosition t t2 (1::pos)

| TermPrivEncTermTerm0 (t t': Term) (k: Name) {pos: list nat} (proof: TermSubTermPosition t (PrivEncTerm t' k) pos) : TermSubTermPosition t t' (0::pos)
| TermPrivEncTermName1 (t t': Term) (k: Name) {pos: list nat} (proof: TermSubTermPosition t (PrivEncTerm t' k) pos) : TermSubTermPosition t (PrivKeyTerm k) (1::pos)

| TermPubEncTermTerm0 (t t': Term) (k: Name) {pos: list nat} (proof: TermSubTermPosition t (PubEncTerm t' k) pos) : TermSubTermPosition t t' (0::pos)
| TermPubEncTermName1 (t t': Term) (k: Name) {pos: list nat} (proof: TermSubTermPosition t (PubEncTerm t' k) pos) : TermSubTermPosition t (PubKeyTerm k) (1::pos).

Inductive TermPositionSet: Term -> Ensemble (list nat) :=
| TermPositionSetCons {t: Term} {pos: list nat} (proof: exists (t': Term), TermSubTermPosition t t' pos): In (TermPositionSet t) pos.

Inductive AssertionTermPosition: Assertion -> Term -> list nat -> Prop :=
| AssertionEqualityLeft0 {t tsub: Term} {pos: list nat} (proof: TermSubTermPosition t tsub pos) (t': Term) : AssertionTermPosition (EqAssertion t t') tsub (0::pos)
| AssertionEqualityRight1 {t t' t'sub: Term} {pos: list nat} (t: Term)(proof: TermSubTermPosition t t'sub pos) : AssertionTermPosition (EqAssertion t t') t'sub (1::pos)
 |AssertionNAry {n i: nat} (P: nAryFun n Term Prop) {tlist: list Term} (lproof: ListLength tlist n) {t: Term} (proof: PositionTermInTermList tlist t i) : AssertionTermPosition (NAryAssertion P tlist lproof) t [i]
| AssertionMemberMember0  (t: Term) (tlist: list Term) : AssertionTermPosition (MemberAssertion t tlist) t [0]
| AssertionMemberDisjunctionSi {n i: nat} {t: Term} (tlist: list Term) (t': Term) (proof: PositionTermInTermList tlist t i): AssertionTermPosition (MemberAssertion t' tlist) t' [(S i)]
                                                                                                                                                        
| AssertionAndLeft0 {a : Assertion}{tsub: Term} {pos: list nat} (proof: AssertionTermPosition a tsub pos) (a' : Assertion): AssertionTermPosition (AndAssertion a a') tsub (0::pos)
| AssertionAndRight1 {a': Assertion} {tsub: Term} {pos: list nat} (a: Assertion) (proof: AssertionTermPosition a' tsub pos) : AssertionTermPosition (AndAssertion a a') tsub (1::pos)

| AssertionExistsVar0 {f: Term -> Assertion} (ftsub: Term -> Term) {pos: list nat} {tsub: Term} {x: Var}  (proof: AssertionTermPosition (f tsub) (ftsub tsub) pos) : AssertionTermPosition (ExistsAssertion f x) (ftsub (VarTerm x)) (0::pos)
| AssertionSaysName00 (k: Name) (a: Assertion): AssertionTermPosition (SaysAssertion k a) (NameTerm k) [0;0]
| AssertionSaysKey0 (k: Name) (a: Assertion): AssertionTermPosition (SaysAssertion k a) (PubKeyTerm k) [0]
| AssertionSaysAss1 {a: Assertion} (k: Name) {tsub: Term}{pos: list nat} (proof: AssertionTermPosition a tsub pos): AssertionTermPosition (SaysAssertion k a) tsub (1::pos).

Inductive AssertionPositionSet: Assertion -> Ensemble (list nat) :=
| AssertionPositionSetCons {a : Assertion} {pos: list nat} (proof: exists (t': Term), AssertionTermPosition a t' pos): In (AssertionPositionSet a) pos.

Inductive AssertionTermPositionSet: Assertion -> Term -> Ensemble (list nat):=
| AssertionTermPositionSetCons {a: Assertion} {t: Term} {pos: list nat} (proof: AssertionTermPosition a t pos): In (AssertionTermPositionSet a t) pos
.
Inductive ProperPrefix: (list nat) -> (list nat) -> Prop :=
| HeadPrefix (hd: nat) {tl: list nat} (nonempty: (tl = []) -> False) : ProperPrefix [hd] (hd::tl)
| ConsPrefix (hd: nat) (tl1 tl2: list nat) (proof: ProperPrefix tl1 tl2) : ProperPrefix (hd::tl1) (hd::tl2).

Inductive QSet: list nat  -> Ensemble (list nat) :=
| EpsilonInQ (t: Term) (pos: list nat): In (QSet pos) []
| PrefixInQ {t: Term} {pos pos': list nat} (prefixProof: ProperPrefix pos' pos) : In (QSet pos) pos'.

Inductive AbstractablePositionSetTerm: TermSet -> Term -> Ensemble (list nat) :=
| AbsractablePositionSetTermCons {S: TermSet} {t: Term} {p: list nat} (positionTermProof: In (TermPositionSet t) p)(abstractableProof: forall (q: list nat) (t': Term), In (QSet p) q -> TermSubTermPosition t t' q -> dy S t') : In (AbstractablePositionSetTerm S t) p. 

Inductive AbstractablePositionSetAssertion: TermSet -> Assertion -> Ensemble (list nat) :=
| AbsAssertionEqualityLeft0 {S: TermSet} {t0: Term} {pos: list nat} (proof: AbstractablePositionSetTerm S t0 pos) (t1: Term):In (AbstractablePositionSetAssertion S (EqAssertion t0 t1)) (0::pos)
| AbsAssertionEqualityRight1 {S: TermSet} {t1: Term} {pos: list nat} (t0: Term) (proof: AbstractablePositionSetTerm S t1 pos): In (AbstractablePositionSetAssertion S (EqAssertion t0 t1)) (1::pos)
|AbsAssertionNAry {S: TermSet} {t: Term} {i n: nat} {tlist: list Term}(P: nAryFun n Term Prop) (proofLength: ListLength tlist n) (proofIdentity: PositionTermInTermList tlist t i) (proofDerivable: dy S t): In (AbstractablePositionSetAssertion S (NAryAssertion P tlist proofLength)) [i]

| AbsAssertionMember (S: TermSet) {n: nat} (t0: Term) (tlist : list Term) : In (AbstractablePositionSetAssertion S (MemberAssertion t0 tlist)) [0]

| AbsAssertionAndLeft0{S:TermSet} {a : Assertion} {pos: list nat} (proof: In (AbstractablePositionSetAssertion S a) pos) (a' : Assertion): In (AbstractablePositionSetAssertion S (AndAssertion a a')) (0::pos)
| AbsAssertionAndRight1 {S: TermSet} {a': Assertion} {pos: list nat} (a: Assertion) (proof: In (AbstractablePositionSetAssertion S a') pos): In (AbstractablePositionSetAssertion S (AndAssertion a a')) (1::pos)
| AbsAssertionExistsVar0 {S: TermSet}{pos: list nat} (afun: Term -> Assertion) {x: Var} (proof: In (AbstractablePositionSetAssertion (Union S (Singleton (VarTerm x))) (afun (VarTerm x))) pos): In (AbstractablePositionSetAssertion S (ExistsAssertion afun x)) (0::pos)
| AbsAssertionSaysPub0 (S: TermSet)(k: Name) (a: Assertion) : In (AbstractablePositionSetAssertion S (SaysAssertion k a)) [0]
| AbsAssertionSaysAss1 {S: TermSet} (k: Name) {a: Assertion} {pos: list nat} (proof: In (AbstractablePositionSetAssertion S a) pos): In (AbstractablePositionSetAssertion S (SaysAssertion k a)) (1::pos).

Check bool.
Inductive ListIntersection {A: Type}: list A -> list A -> list A -> Prop :=
| ListIntersectionNull (l: list A): ListIntersection [] l []
| ListIntersectionNewWin {hd: A} {tl l intersect: list A} (proofIntersect: ListIntersection tl l intersect) (proof: List.In hd l /\ (List.In hd intersect -> False)): ListIntersection (hd::tl) l (hd::intersect)
| ListIntersectionNewFail {hd: A} {tl l intersect: list A} (proofIntersect: ListIntersection tl l intersect) (proof: (List.In hd l -> False)\/ List.In hd intersect ): ListIntersection (hd::tl) l intersect.
Inductive ady: TermSet -> AssertionSet -> Assertion -> Type :=
| aax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: In A alpha): ady S A alpha
                                                                                 
| aeq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : ady S A (EqAssertion t t)
                                                                     
| acons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: ady S A (EqAssertion t1 u1)) (p2: ady S A (EqAssertion t2 u2)): ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))
| acons_privkey {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Name} (p1: ady S A (EqAssertion t1 t2)) (p2: ady S A (EqAssertion (PrivKeyTerm k1) (PrivKeyTerm k2))): ady S A (EqAssertion (PrivEncTerm t1 k1) (PrivEncTerm t2 k2))
| acons_pubkey {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Name} (p1: ady S A (EqAssertion t1 t2)) (p2: ady S A (EqAssertion (PubKeyTerm k1) (PubKeyTerm k2))): ady S A (EqAssertion (PubEncTerm t1 k1) (PubEncTerm t2 k2))

| asym {S: TermSet} {A: AssertionSet} {t u: Term} (p: ady S A (EqAssertion t u)) : ady S A (EqAssertion u t)

| atrans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: ValidTransEqPremiseList S A t1 tk): ady S A (EqAssertion t1 tk)

| aproj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;0]) : ady S A (EqAssertion t1 u1)
| aproj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))  (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;1]) : ady S A (EqAssertion t2 u2)
                                   
          
| aproj_privenc_term {S: TermSet} {A: AssertionSet} {k1 k2: Name} {t1 t2: Term} (p: ady S A (EqAssertion (PrivEncTerm t1 k2) (PrivEncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PrivEncTerm t1 k2) (PrivEncTerm t2 k2))) [0;0]): ady S A (EqAssertion t1 t2)
| aproj_privenc_key {S: TermSet} {A: AssertionSet} {k1 k2: Name} {t1 t2: Term} (p: ady S A (EqAssertion (PrivEncTerm t1 k2) (PrivEncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PrivEncTerm t1 k2) (PrivEncTerm t2 k2))) [0;1]): ady S A (EqAssertion (PrivKeyTerm k1) (PrivKeyTerm k2))                                                                                 
                                                                                
| aproj_pubenc_term {S: TermSet} {A: AssertionSet} {k1 k2: Name} {t1 t2: Term} (p: ady S A (EqAssertion (PubEncTerm t1 k2) (PubEncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PubEncTerm t1 k2) (PubEncTerm t2 k2)) ) [0;0]): ady S A (EqAssertion t1 t2)
| aproj_pubenc_key {S: TermSet} {A: AssertionSet} {k1 k2: Name} {t1 t2: Term} (p: ady S A (EqAssertion (PubEncTerm t1 k2) (PubEncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PubEncTerm t1 k2) (PubEncTerm t2 k2))) [0;1]): ady S A (EqAssertion (PubKeyTerm k1) (PubKeyTerm k2))                        

| aand_intro {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p1: ady S A a1) (p2: ady S A a2): ady S A (AndAssertion a1 a2)
| aand_elim_left {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p: ady S A (AndAssertion a1 a2)): ady S A a1
| aand_elim_right {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p: ady S A (AndAssertion a1 a2)): ady S A a2

| asubst {S: TermSet} {A: AssertionSet} {t u: Term} {l: list Term} (proofMember: ady S A (MemberAssertion t l)) (proofEq: ady S A (EqAssertion t u)): ady S A (MemberAssertion u l)
| aexists_intro {S: TermSet} {A: AssertionSet} {a: Term -> Assertion} {x: Var} {t: Term} (truth: ady S A (a t)) (witness: dy S t) (derivability: Included (AssertionTermPositionSet (a (VarTerm x)) (VarTerm x)) (AbstractablePositionSetAssertion (Union S (Singleton (VarTerm x))) (a (VarTerm x)))): ady S A (ExistsAssertion a x)

| aexists_elim {S: TermSet} {A: AssertionSet} {x y: Var} {afun: Term -> Assertion} {G: Assertion} (proofExists: ady S A (ExistsAssertion afun x)) (proofDerivable: ady (Union S (Singleton (VarTerm y))) A G) (proofFV: In (Union (FVSetTermSet S) (Union (FVSetAssertionSet A) (FVSetAssertion G))) y -> False) : ady S A G
| asay {S: TermSet} {A: AssertionSet} {a: Assertion} {k: Name} (proof1: ady S A a) (proof2: dy S (PrivKeyTerm k)): ady S A (SaysAssertion k a)
| aprom {S: TermSet} {A: AssertionSet} {t n: Term} (proof: ady S A (MemberAssertion t [n])) : ady S A (EqAssertion t n)
| aint {S: TermSet} {A: AssertionSet} {t: Term} {l: list Term} (premises: ValidIntPremiseList S A t l): ady S A (MemberAssertion t l)
| awk {S: TermSet} {A: AssertionSet} {t n: Term} {nlist: list Term} (proofEq: ady S A (EqAssertion t n)) (proofIn: List.In n nlist) (proofValid: DerivableTermsList S nlist): ady S A (MemberAssertion t nlist)                                                           
with ValidIntPremiseList: TermSet -> AssertionSet -> Term -> list Term -> Type:=
| TwoLists {S: TermSet} {A: AssertionSet} {t: Term} {l1 l2 intersect: list Term} (proofIntersect: ListIntersection l1 l2 intersect) (proof1: ady S A (MemberAssertion t l1)) (proof2: ady S A (MemberAssertion t l2)): ValidIntPremiseList S A t intersect
| NewList {S: TermSet} {A: AssertionSet} {t: Term} {l1 intersect intersectl1: list Term} (proofIntersect: ListIntersection l1 intersect intersectl1) (proof1: ady S A (MemberAssertion t l1)) (proof2: ValidIntPremiseList S A t intersect): ValidIntPremiseList S A t intersectl1
with DerivableTermsList: TermSet -> list Term -> Type:=
| SingleDerivable {S: TermSet} {t: Term} (proof: dy S t): DerivableTermsList S [t]
| NewDerivable {S: TermSet} {t: Term} {tlist: list Term} (proofNew: dy S t) (proofList: DerivableTermsList S tlist): DerivableTermsList S (t::tlist)
with ValidTransEqPremiseList: TermSet -> AssertionSet -> Term -> Term -> Type:=
| TwoTrans {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (p1: ady S A (EqAssertion t1 t2)) (p2: ady S A (EqAssertion t2 t3)): ValidTransEqPremiseList S A t1 t3
| TransTrans {S: TermSet} {A: AssertionSet} {t1 t tk tk': Term} (phead: ady S A (EqAssertion t tk)) (plist: ValidTransEqPremiseList S A tk tk'): ValidTransEqPremiseList S A t1 tk'.



                                                                                                                         
