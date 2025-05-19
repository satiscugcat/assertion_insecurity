Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Program.Wf.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lists.List. Import ListNotations.
(**
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat. Import Nat.
**)
Import Nat.
From Stdlib Require Import Strings.String.
From Stdlib Require Export Sets.Ensembles.

Arguments In {U}.
Arguments Union {U}.
Arguments Singleton {U}.
Arguments Included {U}.
Arguments Empty_set {U}.
Arguments cons {A}.

Inductive TermVar : Type := TermVarConstructor (n: nat).
Inductive KeyVar  : Type  := KeyVarConstructor (n: nat).
Definition Var: Type := TermVar + KeyVar.

Inductive Name: Type:=  NameConstructor (n: nat): Name.

Inductive Key: Type :=
| PrivKey (k: Name)
| PubKey (k: Name)
| VarKey (v: KeyVar).

(*
Fixpoint nAryFun (n: nat) (A: Type) (B: Type) : Type :=
  match n with
  | 0 => B
  | S n' => A -> (nAryFun n' A B)
  end.
*)
Inductive Term: Type :=
| VarTerm (v: TermVar)
| NameTerm (m: Name)
| KeyTerm (k: Key)
| PairTerm (t1 t2: Term)
| EncTerm (t: Term) (k: Key).

Definition TermSet: Type := Ensemble Term.

Fixpoint FVSetTerm (t: Term) : Ensemble Var :=
    match t with
    | VarTerm v => Singleton (inl v)
    | NameTerm _ => Empty_set
    | KeyTerm (VarKey v) => Singleton (inr v)
    | KeyTerm _ => Empty_set
    | PairTerm t1 t2 => Union (FVSetTerm t1) (FVSetTerm t2)
    | EncTerm t' k => Union (FVSetTerm t')
                           match k with | VarKey v => Singleton (inr v) | _ => Empty_set end
    end.

Inductive dy : TermSet -> Term -> Type:=
| ax {X: TermSet} {t: Term} (inH: In X t) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (KeyTerm (PrivKey k)) ) : dy X (KeyTerm (PubKey k))
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (PairTerm t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (EncTerm t (PrivKey k))) (kH: dy X (KeyTerm (PrivKey k))): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (KeyTerm (PrivKey k))) : dy X (EncTerm t (PrivKey k))
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (EncTerm t (PubKey k))) (keyH: dy X (KeyTerm (PrivKey k))): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (KeyTerm (PubKey k))) : dy X (EncTerm t (PubKey k)).


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

Fixpoint dyProofNormaliser {X: TermSet} {t: Term} (proof: dy X t) {struct proof}: dy X t.
Proof.
  destruct proof.
  - apply (ax inH).
  - apply (pk (dyProofNormaliser _ _ proof)).
  - dependent destruction proof.
    + apply (splitL (ax inH)).
    + apply (splitL (splitL (dyProofNormaliser _ _ proof))).
    + apply (splitL (splitR (dyProofNormaliser _ _ proof))).
    + apply (dyProofNormaliser _ _ proof1).
    + apply (splitL (sdec (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2))).
    + apply (splitL (adec (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2))).
  - dependent destruction proof.
    + apply (splitR (ax inH)).
    + apply (splitR (splitL (dyProofNormaliser _ _ proof))).
    + apply (splitR (splitR (dyProofNormaliser _ _ proof))).
    + apply (dyProofNormaliser _ _ proof2).
    + apply (splitR (sdec (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2))).
    
    + apply (splitR (adec (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2))).
  -  apply (pair (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2)).
  - dependent destruction proof1.
    + apply (sdec (ax inH) (dyProofNormaliser _ _ proof2)).
    + apply (sdec (splitL (dyProofNormaliser _ _ proof1)) (dyProofNormaliser _ _ proof2)).
    + apply (sdec (splitR (dyProofNormaliser _ _ proof1)) (dyProofNormaliser _ _ proof2)).
    +  apply (sdec (sdec (dyProofNormaliser _ _ proof1_1) (dyProofNormaliser _ _ proof1_2))
                (dyProofNormaliser _ _ proof2)).
    + apply (dyProofNormaliser _ _ proof1_1).
    +  apply (sdec (adec (dyProofNormaliser _ _ proof1_1) (dyProofNormaliser _ _ proof1_2))
                  (dyProofNormaliser _ _ proof2)).
  - apply (senc (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2)).
  - dependent destruction proof1.
    + apply (adec (ax inH) (dyProofNormaliser _ _ proof2)).
    + apply (adec (splitL (dyProofNormaliser _ _ proof1)) (dyProofNormaliser _ _ proof2)).
    + apply (adec (splitR (dyProofNormaliser _ _ proof1)) (dyProofNormaliser _ _ proof2)).
    +  apply (adec (sdec (dyProofNormaliser _ _ proof1_1) (dyProofNormaliser _ _ proof1_2))
                (dyProofNormaliser _ _ proof2)).
   
    +  apply (adec (adec (dyProofNormaliser _ _ proof1_1) (dyProofNormaliser _ _ proof1_2))
                (dyProofNormaliser _ _ proof2)).
    + apply (dyProofNormaliser _ _ proof1_1).
  -  apply (aenc (dyProofNormaliser _ _ proof1) (dyProofNormaliser _ _ proof2)).
Defined.
    
  
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

Theorem dyProofNormaliserCorrectness :forall (X: TermSet) (t: Term) (proof: dy X t), (isNormal (dyProofNormaliser proof)) = true.
Proof.
  intros X t proof. dependent induction proof.
  - simpl. reflexivity.
  - simpl. assumption.
  - simpl. dependent destruction proof; simpl.
    +  reflexivity.
    + simpl. dependent destruction proof.
      ++ simpl. reflexivity.
      ++  simpl in IHproof. apply andb_true_iff in IHproof. destruct  IHproof as [IHproof []].  apply andb_true_iff in IHproof. destruct IHproof as [IHproof1 IHproof2]. apply andb_true_iff. split; auto. apply andb_true_iff. split.
          {
            admit.
          }
Admitted.
Inductive SubTerm: Term -> Term -> Prop:=
| SubTermRefl (t: Term) : SubTerm t t
| SubTermTrans {t1 t2 t3: Term} (r1: SubTerm t1 t2) (r2: SubTerm t2 t3) : SubTerm t1 t3
                                                                                  
| SubTermPairLeft (t1 t2: Term) : SubTerm t1 (PairTerm t1 t2)
| SubTermPairRight (t1 t2: Term) : SubTerm t2 (PairTerm t1 t2)
                                            
| SubTermEncTerm (t : Term) (k: Key) : SubTerm t (EncTerm t k )
| SubTermEncKey (t: Term) (k: Key) : SubTerm (KeyTerm k) (EncTerm t k ).

Inductive SubTermSet (S: TermSet) : TermSet :=
| SubTermSetCons {t: Term} (proof: exists (t': Term), (In S t') /\ (SubTerm t t')) : In (SubTermSet S) t.

Fixpoint ProofTerms {X: TermSet} {t: Term} (proof: dy X t) : TermSet :=
  match proof with
  | @ax _ t _  => Singleton t
  | @pk _ k kH => Union (Singleton (KeyTerm (PubKey k))) (ProofTerms kH)

  | @splitL _ t1 _ splitH => Union (Singleton t1) (ProofTerms splitH)
  | @splitR _ _ t2 splitH =>  Union (Singleton t2) (ProofTerms splitH)
  | @pair _ t1 t2 t1H t2H => Union (Singleton (PairTerm t1 t2)) (Union (ProofTerms t1H) (ProofTerms t2H))
                        
  | @sdec _ t' _ encH kH => Union (Singleton t') (Union (ProofTerms encH) (ProofTerms kH))
  | @senc _ t' k tH kH => Union (Singleton (EncTerm t' (PrivKey k)) ) (Union (ProofTerms tH) (ProofTerms kH))
                        
  | @adec _ t' _ encH kH => Union (Singleton t') (Union (ProofTerms encH) (ProofTerms kH))
  | @aenc _ t' k tH kH =>  Union (Singleton (EncTerm t' (PubKey k))) (Union (ProofTerms tH) (ProofTerms kH))
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
  - apply (Union_introl Term (Singleton (KeyTerm (PubKey k))) (ProofTerms proof) (KeyTerm (PubKey k)) (In_singleton Term (KeyTerm (PubKey k)))).
  - apply (Union_introl Term (Singleton t1) (ProofTerms proof) t1 (In_singleton Term t1)).
  - apply (Union_introl Term (Singleton t2) (ProofTerms proof) t2 (In_singleton Term t2)).
  - apply (Union_introl Term (Singleton (PairTerm t1 t2)) (Union (ProofTerms proof1) (ProofTerms proof2)) (PairTerm t1 t2) (In_singleton Term (PairTerm t1 t2))).
  - apply (Union_introl Term (Singleton t) (Union (ProofTerms proof1) (ProofTerms proof2)) t (In_singleton Term t)).
  - apply (Union_introl Term (Singleton (EncTerm t (PrivKey k))) (Union (ProofTerms proof1) (ProofTerms proof2)) (EncTerm t (PrivKey k)) (In_singleton Term (EncTerm t (PrivKey k)))).
  - apply (Union_introl Term (Singleton t) (Union (ProofTerms proof1) (ProofTerms proof2)) t (In_singleton Term t)).
  - apply (Union_introl Term (Singleton (EncTerm t (PubKey k))) (Union (ProofTerms proof1) (ProofTerms proof2)) (EncTerm t (PubKey k)) (In_singleton Term (EncTerm t (PubKey k)))).
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

    assert (proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (KeyTerm (PrivKey k)))) )). {
      dependent destruction proof2 ; auto ; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).

    } clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. clear sanity. simpl. intros x unionterm. destruct unionterm.
    + inversion H. subst. pose (proofsub1' (EncTerm x (PrivKey k)) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermEncTerm x (PrivKey k)) bigfish).
    + destruct H.
      ++ apply (proofsub1' x H).
      ++ pose (proofsub2' x H) as xsub2'. destruct xsub2'. destruct proof. destruct H0. destruct H0.
      * assert (H': exists (somet: Term), In X somet /\ SubTerm t0 somet). { exists x. split. apply H0. apply H1. } apply (SubTermSetCons X H').
      * inversion H0. subst. pose (proofsub1' (EncTerm t (PrivKey k)) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermTrans H1 (SubTermEncKey t (PrivKey k))) bigfish).
  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2. simpl.

    assert(proofsub1': Included (ProofTerms proof1) (SubTermSet (Union X (Singleton t)))). {
        dependent destruction proof1; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub1 x inpterms))).
        }

        assert(proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (KeyTerm (PrivKey k)))))). {
        dependent destruction proof2; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).
        }
        clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. intros x. intros unionterm. destruct unionterm.
        + inversion H. subst. apply (UnionSubTermRight (TermInSubTermSet (In_singleton Term (EncTerm t (PrivKey k))))).
        + assert (H1: Included (SubTermSet (Union X (Singleton t)))
                    (SubTermSet (Union X (Singleton (EncTerm t (PrivKey k)))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.
          assert (req: exists(somet: Term), In (Singleton (EncTerm x0 (PrivKey k))) somet /\ SubTerm t0 somet). {exists (EncTerm x0 (PrivKey k)). split. apply (In_singleton Term (EncTerm x0 (PrivKey k))). apply (SubTermTrans H1 (SubTermEncTerm x0 (PrivKey k))).} apply (UnionSubTermRight (SubTermSetCons (Singleton (EncTerm x0 (PrivKey k))) req)).
      }

      assert (H2: Included (SubTermSet (Union X (Singleton (KeyTerm (PrivKey k)))))
                    (SubTermSet (Union X (Singleton (EncTerm t (PrivKey k)))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H2.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (EncTerm t (PrivKey k))) somet /\ SubTerm t0 somet). {exists (EncTerm t (PrivKey k)). split. apply (In_singleton Term (EncTerm t (PrivKey k))). apply (SubTermTrans H2 (SubTermEncKey t (PrivKey k))).} apply (UnionSubTermRight (SubTermSetCons (Singleton (EncTerm t (PrivKey k))) req)).
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
    + inversion H. subst. pose (proofsub1' (EncTerm x (PubKey k)) (ResultInProofTerms proof1)) as bigfish. apply (BiggerFish (SubTermEncTerm x (PubKey k)) bigfish).
    + destruct H.
      ++ apply (proofsub1' x H).
      ++ apply (proofsub2' x H).

  - intros eq. simpl in eq. apply andb_true_iff in eq. destruct eq as [eq1 eq2]. pose (IHproof1 eq1) as proofsub1. pose (IHproof2 eq2) as proofsub2. simpl.

    assert(proofsub1': Included (ProofTerms proof1) (SubTermSet (Union X (Singleton t)))). {
        dependent destruction proof1; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub1 x inpterms))).
        }

        assert(proofsub2': Included (ProofTerms proof2) (SubTermSet (Union X (Singleton (KeyTerm (PubKey k)))))). {
        dependent destruction proof2; auto; try (intros x ; intros inpterms ; apply (UnionSubTermLeft (proofsub2 x inpterms))).
        }
        clear proofsub1. clear proofsub2. clear IHproof1. clear IHproof2. intros x. intros unionterm. destruct unionterm.
        + inversion H. subst. apply (UnionSubTermRight (TermInSubTermSet (In_singleton Term (EncTerm t (PubKey k))))).
        + assert (H1: Included (SubTermSet (Union X (Singleton t)))
                    (SubTermSet (Union X (Singleton (EncTerm t (PubKey k)))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H1.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (EncTerm x0 (PubKey k))) somet /\ SubTerm t0 somet). {exists (EncTerm x0 (PubKey k)). split. apply (In_singleton Term (EncTerm x0 (PubKey k))). apply (SubTermTrans H1 (SubTermEncTerm x0 (PubKey k))).} apply (UnionSubTermRight (SubTermSetCons (Singleton (EncTerm x0 (PubKey k))) req)).
      }

      assert (H2: Included (SubTermSet (Union X (Singleton (KeyTerm (PubKey k)))))
                    (SubTermSet (Union X (Singleton (EncTerm t (PubKey k)))))).
      {
        intros x' sub. destruct sub. destruct proof. destruct H0. destruct H0.
        - assert (req: exists(somet: Term), In X somet /\ SubTerm t0 somet). {exists x0. split. apply H0. apply H2.} apply (UnionSubTermLeft (SubTermSetCons X req)).
        - inversion H0. subst.  assert (req: exists(somet: Term), In (Singleton (EncTerm t (PubKey k))) somet /\ SubTerm t0 somet). {exists (EncTerm t (PubKey k)). split. apply (In_singleton Term (EncTerm t (PubKey k))). apply (SubTermTrans H2 (SubTermEncKey t (PubKey k))).} apply (UnionSubTermRight (SubTermSetCons (Singleton (EncTerm t (PubKey k))) req)).
      }

      destruct H.
          * apply (H1 x (proofsub1' x H)).
          * apply (H2 x (proofsub2' x H)).
Qed.



Check cons.
Inductive PositionTermInTermList: list Term  -> Term -> nat -> Prop :=
| PositionVectorHead0 {n: nat} (head: Term) (tl: list Term) : PositionTermInTermList (head::tl) head 0
| PositionVectorConsSn {n i: nat} (head elem: Term) {tl: list Term} (proof: PositionTermInTermList tl elem i): PositionTermInTermList (head::tl) elem (S i).

Inductive ListLength {A: Type}: list A -> nat -> Prop :=
| Null0 : ListLength [] 0
| ConsS (head : A) {n: nat} {tail : list A} (proof: ListLength tail n) : ListLength (head::tail) (S n).

Inductive Assertion: Type :=
| EqAssertion (t u: Term)
(* | NAryAssertion {n: nat} (P: nAryFun n Term Prop) (tlist: list Term) (proof: ListLength tlist n) *)
| MemberAssertion (t0: Term) (tlist: list Term)
| AndAssertion (a0 a1 : Assertion)
| ExistsAssertion (a: Assertion) (x: Var)
| SaysAssertion (k: Name) (a: Assertion).         

Fixpoint foldr {A B: Type} (accumulatingfun: A -> B -> B) (initial: B) (fuel: list A): B :=
  match fuel with
  | [] => initial
  | hd::tl => accumulatingfun hd (foldr accumulatingfun initial tl)
  end.
Fixpoint FVSetAssertion (a: Assertion) : Ensemble Var :=
  match a with
  | EqAssertion t u => Union (FVSetTerm t) (FVSetTerm u)
  (* | NAryAssertion _ tlist _ => (foldr (fun (t: Term) (ts: Ensemble Var) => Union (FVSetTerm t) ts) Empty_set tlist) *)
  | MemberAssertion t tlist => Union (FVSetTerm t) (foldr (fun (t: Term) (ts: Ensemble Var) => Union (FVSetTerm t) ts) Empty_set tlist)
  | AndAssertion a0 a1 => Union (FVSetAssertion a0) (FVSetAssertion a1)
  | ExistsAssertion a x => Subtract Var (FVSetAssertion a) x
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

| TermEncTermTerm0 (t t': Term) (k: Key) {pos: list nat} (proof: TermSubTermPosition t (EncTerm t' k) pos) : TermSubTermPosition t t' (0::pos)
| TermEncTermName1 (t t': Term) (k: Key) {pos: list nat} (proof: TermSubTermPosition t (EncTerm t' k) pos) : TermSubTermPosition t (KeyTerm k) (1::pos).

Inductive TermPositionSet: Term -> Ensemble (list nat) :=
| TermPositionSetCons {t: Term} {pos: list nat} (proof: exists (t': Term), TermSubTermPosition t t' pos): In (TermPositionSet t) pos.

Inductive AssertionTermPosition: Assertion -> Term -> list nat -> Prop :=
| AssertionEqualityLeft0 {t tsub: Term} {pos: list nat} (proof: TermSubTermPosition t tsub pos) (t': Term) : AssertionTermPosition (EqAssertion t t') tsub (0::pos)
| AssertionEqualityRight1 {t t' t'sub: Term} {pos: list nat} (t: Term)(proof: TermSubTermPosition t t'sub pos) : AssertionTermPosition (EqAssertion t t') t'sub (1::pos)
 (*|AssertionNAry {n i: nat} (P: nAryFun n Term Prop) {tlist: list Term} (lproof: ListLength tlist n) {t: Term} (proof: PositionTermInTermList tlist t i) : AssertionTermPosition (NAryAssertion P tlist lproof) t [i] *)
| AssertionMemberMember0  (t: Term) (tlist: list Term) : AssertionTermPosition (MemberAssertion t tlist) t [0]
| AssertionMemberDisjunctionSi {n i: nat} {t: Term} (tlist: list Term) (t': Term) (proof: PositionTermInTermList tlist t i): AssertionTermPosition (MemberAssertion t' tlist) t' [(S i)]
                                                                                                                                                        
| AssertionAndLeft0 {a : Assertion}{tsub: Term} {pos: list nat} (proof: AssertionTermPosition a tsub pos) (a' : Assertion): AssertionTermPosition (AndAssertion a a') tsub (0::pos)
| AssertionAndRight1 {a': Assertion} {tsub: Term} {pos: list nat} (a: Assertion) (proof: AssertionTermPosition a' tsub pos) : AssertionTermPosition (AndAssertion a a') tsub (1::pos)

| AssertionExistsVar0 {a: Assertion} {pos: list nat} {tsub: Term} {x: Var}  (proof: AssertionTermPosition a (match x with | inl v => VarTerm v | inr v => KeyTerm (VarKey v) end) pos) : AssertionTermPosition (ExistsAssertion a x) (match x with | inl v => VarTerm v | inr v => KeyTerm (VarKey v) end) (0::pos)

| AssertionSaysName00 (k: Name) (a: Assertion): AssertionTermPosition (SaysAssertion k a) (NameTerm k) [0;0]
| AssertionSaysKey0 (k: Name) (a: Assertion): AssertionTermPosition (SaysAssertion k a) (KeyTerm (PubKey k)) [0]
| AssertionSaysAss1 {a: Assertion} (k: Name) {tsub: Term}{pos: list nat} (proof: AssertionTermPosition a tsub pos): AssertionTermPosition (SaysAssertion k a) tsub (1::pos).




Inductive AssertionPositionSet: Assertion -> Ensemble (list nat) :=
| AssertionPositionSetCons {a : Assertion} {pos: list nat} (proof: exists (t': Term), AssertionTermPosition a t' pos): In (AssertionPositionSet a) pos.

Inductive AssertionTermPositionSet: Assertion -> Term -> Ensemble (list nat):=
| AssertionTermPositionSetCons {a: Assertion} {t: Term} {pos: list nat} (proof: AssertionTermPosition a t pos): In (AssertionTermPositionSet a t) pos.
Inductive ProperPrefix: (list nat) -> (list nat) -> Prop :=
| HeadPrefix (hd: nat) {tl: list nat} (nonempty: (tl = []) -> False) : ProperPrefix [hd] (hd::tl)
| ConsPrefix (hd: nat) (tl1 tl2: list nat) (proof: ProperPrefix tl1 tl2) : ProperPrefix (hd::tl1) (hd::tl2).


Definition AssertionSubTerm (a: Assertion) (t: Term) := exists (pos: list nat), AssertionTermPosition a t pos.
Inductive AssertionSubTermSet (a: Assertion) : Ensemble Term :=
| AssertionSubTermSetCons {t: Term} (p: AssertionSubTerm a t) : In (AssertionSubTermSet a) t.
Inductive AssertionSetSubTermSet (A: AssertionSet) : Ensemble Term :=
| AssertionSetSubTermSetCons {t: Term} (p: exists a, In A a /\ AssertionSubTerm a t) : In (AssertionSetSubTermSet A) t.
Definition AssertionMaximalSubTerm (a: Assertion) (t: Term) :=
  exists (pos: list nat), (AssertionTermPosition a t pos /\ (~ (exists (t': Term) (pos': list nat), AssertionTermPosition a t' pos' /\ ProperPrefix pos' pos))).
Inductive QSet: list nat  -> Ensemble (list nat) :=
| EpsilonInQ (t: Term) (pos: list nat): In (QSet pos) []
| PrefixInQ {t: Term} {pos pos': list nat} (prefixProof: ProperPrefix pos' pos) : In (QSet pos) pos'.

Inductive AbstractablePositionSetTerm: TermSet -> Term -> Ensemble (list nat) :=
| AbsractablePositionSetTermCons {S: TermSet} {t: Term} {p: list nat} (positionTermProof: In (TermPositionSet t) p)(abstractableProof: forall (q: list nat) (t': Term), In (QSet p) q -> TermSubTermPosition t t' q -> dy S t') : In (AbstractablePositionSetTerm S t) p. 

Inductive AbstractablePositionSetAssertion: TermSet -> Assertion -> Ensemble (list nat) :=
| AbsAssertionEqualityLeft0 {S: TermSet} {t0: Term} {pos: list nat} (proof: AbstractablePositionSetTerm S t0 pos) (t1: Term):In (AbstractablePositionSetAssertion S (EqAssertion t0 t1)) (0::pos)
| AbsAssertionEqualityRight1 {S: TermSet} {t1: Term} {pos: list nat} (t0: Term) (proof: AbstractablePositionSetTerm S t1 pos): In (AbstractablePositionSetAssertion S (EqAssertion t0 t1)) (1::pos)
(* |AbsAssertionNAry {S: TermSet} {t: Term} {i n: nat} {tlist: list Term}(P: nAryFun n Term Prop) (proofLength: ListLength tlist n) (proofIdentity: PositionTermInTermList tlist t i) (proofDerivable: dy S t): In (AbstractablePositionSetAssertion S (NAryAssertion P tlist proofLength)) [i] *)

| AbsAssertionMember (S: TermSet) {n: nat} (t0: Term) (tlist : list Term) : In (AbstractablePositionSetAssertion S (MemberAssertion t0 tlist)) [0]

| AbsAssertionAndLeft0{S:TermSet} {a : Assertion} {pos: list nat} (proof: In (AbstractablePositionSetAssertion S a) pos) (a' : Assertion): In (AbstractablePositionSetAssertion S (AndAssertion a a')) (0::pos)
| AbsAssertionAndRight1 {S: TermSet} {a': Assertion} {pos: list nat} (a: Assertion) (proof: In (AbstractablePositionSetAssertion S a') pos): In (AbstractablePositionSetAssertion S (AndAssertion a a')) (1::pos)
| AbsAssertionExistsVar0 {S: TermSet}{pos: list nat} (a: Assertion) {x: Var} (proof: In (AbstractablePositionSetAssertion (Union S (Singleton match x with | inl v => VarTerm v | inr v => KeyTerm (VarKey v) end)) a) pos):
  In (AbstractablePositionSetAssertion S (ExistsAssertion a x))
    (0::pos)
| AbsAssertionSaysPub0 (S: TermSet)(k: Name) (a: Assertion) : In (AbstractablePositionSetAssertion S (SaysAssertion k a)) [0]
| AbsAssertionSaysAss1 {S: TermSet} (k: Name) {a: Assertion} {pos: list nat} (proof: In (AbstractablePositionSetAssertion S a) pos): In (AbstractablePositionSetAssertion S (SaysAssertion k a)) (1::pos).

Check bool.
Inductive ListIntersection {A: Type}: list A -> list A -> list A -> Prop :=
| ListIntersectionNull (l: list A): ListIntersection [] l []
| ListIntersectionNewWin {hd: A} {tl l intersect: list A} (proofIntersect: ListIntersection tl l intersect) (proof: List.In hd l /\ (List.In hd intersect -> False)): ListIntersection (hd::tl) l (hd::intersect)
| ListIntersectionNewFail {hd: A} {tl l intersect: list A} (proofIntersect: ListIntersection tl l intersect) (proof: (List.In hd l -> False)\/ List.In hd intersect ): ListIntersection (hd::tl) l intersect.

Inductive SubstitutedAssertion: Assertion -> Ensemble (list nat) -> Term -> Assertion -> Prop :=
| SubstitutedAssertionCons
    {a a': Assertion} {t: Term} {P: Ensemble (list nat)}
    (includedProof: Included P (AssertionPositionSet a))
    (termPositionSubstitutedProof: forall pos,
        In P pos -> AssertionTermPosition a' t pos
    )
    (termPositionSameProof: forall pos t',
        (In P pos -> False) -> AssertionTermPosition a t pos -> AssertionTermPosition a' t' pos
    )
  : SubstitutedAssertion a P t a'.

Definition var_to_term (v: Var) : Term :=
  match v with
  | inl v => VarTerm v
  | inr v => KeyTerm (VarKey v)
  end.
Inductive ady: TermSet -> AssertionSet -> Assertion -> Type :=
| aax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: In A alpha): ady S A alpha
                                                                                 
| aeq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : ady S A (EqAssertion t t)
                                                                     
| acons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: ady S A (EqAssertion t1 u1)) (p2: ady S A (EqAssertion t2 u2)): ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))
                                                                                                                                         
| acons_enc {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Key} (p1: ady S A (EqAssertion t1 t2)) (p2: ady S A (EqAssertion ((KeyTerm k1)) (KeyTerm k2 ))): ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))
                                                                                                     

| asym {S: TermSet} {A: AssertionSet} {t u: Term} (p: ady S A (EqAssertion t u)) : ady S A (EqAssertion u t)

| atrans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: ValidTransEqPremiseList S A t1 tk): ady S A (EqAssertion t1 tk)

| aproj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;0]) : ady S A (EqAssertion t1 u1)
| aproj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))  (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;1]) : ady S A (EqAssertion t2 u2)
                                   
          
| aproj_enc_term {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) [0;0]): ady S A (EqAssertion t1 t2)
| aproj_enc_key {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) [0;1]): ady S A (EqAssertion ((KeyTerm k1)) (KeyTerm k2 ))                                                                                 
                                                                            
| aand_intro {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p1: ady S A a1) (p2: ady S A a2): ady S A (AndAssertion a1 a2)
| aand_elim_left {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p: ady S A (AndAssertion a1 a2)): ady S A a1
| aand_elim_right {S: TermSet} {A: AssertionSet} {a1 a2: Assertion} (p: ady S A (AndAssertion a1 a2)): ady S A a2

| asubst {S: TermSet} {A: AssertionSet} {t u: Term} {l: list Term} (proofMember: ady S A (MemberAssertion t l)) (proofEq: ady S A (EqAssertion t u)): ady S A (MemberAssertion u l)
                                                                                                                                                          
| aexists_intro {S: TermSet} {A: AssertionSet} {a a': Assertion} {x: Var} {t: Term}
    (substitutedProof: SubstitutedAssertion a (AssertionTermPositionSet a (var_to_term x)) t a')
    (truth: ady S A a' ) (witness: dy S t)
    (derivability: Included (AssertionTermPositionSet a (var_to_term x)) (AbstractablePositionSetAssertion (Union S (Singleton (var_to_term x))) a)): ady S A (ExistsAssertion a x)

| aexists_elim {S: TermSet} {A: AssertionSet} {x y: Var} {a a': Assertion} {G: Assertion}
    (proofExists: ady S A (ExistsAssertion a x))
    (substitutedProof: SubstitutedAssertion a (AssertionTermPositionSet a (var_to_term x)) (var_to_term y) a')
    (proofDerivable: ady
                       (Union S (Singleton (var_to_term y)) )
                       (Union A (Singleton a'))
                       G)
    (proofFV: In (Union (FVSetTermSet S) (Union (FVSetAssertionSet A) (FVSetAssertion G))) y -> False)
  : ady S A G
                                                                                                                                                                                                                                                                                                                 
| asay {S: TermSet} {A: AssertionSet} {a: Assertion} {k: Name} (proof1: ady S A a) (proof2: dy S (KeyTerm (PrivKey k))): ady S A (SaysAssertion k a)
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
| TransTrans {S: TermSet} {A: AssertionSet} {t1 tk tk': Term} (phead: ady S A (EqAssertion t1 tk)) (plist: ValidTransEqPremiseList S A tk tk'): ValidTransEqPremiseList S A t1 tk'.


Definition isAtomic (a: Assertion) : bool :=
  match a with
  | EqAssertion _ _ => true
  | MemberAssertion _ _ => true
  | SaysAssertion _ _ => true
  | _ => false
  end.


                                                                                                                         
Inductive eq_ady: TermSet -> AssertionSet -> Assertion -> Type :=
| eq_aax (S: TermSet) {A: AssertionSet} {alpha: Assertion} (proof: In A alpha): eq_ady S A alpha
                                                                                 
| eq_aeq {S: TermSet} (A: AssertionSet) {t: Term} (proof: dy S t) : eq_ady S A (EqAssertion t t)
                                                                     
| eq_acons_pair {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p1: eq_ady S A (EqAssertion t1 u1)) (p2: eq_ady S A (EqAssertion t2 u2)): eq_ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))

| eq_acons_enc {S: TermSet} {A: AssertionSet} {t1 t2: Term} {k1 k2: Key} (p1: eq_ady S A (EqAssertion t1 t2)) (p2: eq_ady S A (EqAssertion ((KeyTerm k1)) (KeyTerm k2 ))): eq_ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))

| eq_asym {S: TermSet} {A: AssertionSet} {t u: Term} (p: eq_ady S A (EqAssertion t u)) : eq_ady S A (EqAssertion u t)

| eq_atrans {S: TermSet} {A: AssertionSet} {t1 tk: Term} (p: Eq_ValidTransEqPremiseList S A t1 tk): eq_ady S A (EqAssertion t1 tk)

| eq_aproj_pair_left {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;0]) : eq_ady S A (EqAssertion t1 u1)
| eq_aproj_pair_right {S: TermSet} {A: AssertionSet} {t1 t2 u1 u2: Term} (p: eq_ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))  (pin: In (AbstractablePositionSetAssertion S (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2))) [0;1]) : eq_ady S A (EqAssertion t2 u2)
                                   
          
| eq_aproj_enc_term {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) [0;0]): eq_ady S A (EqAssertion t1 t2)
| eq_aproj_enc_key {S: TermSet} {A: AssertionSet} {k1 k2: Key} {t1 t2: Term} (p: eq_ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) (pin: In (AbstractablePositionSetAssertion S (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) [0;1]): eq_ady S A (EqAssertion ((KeyTerm k1)) (KeyTerm k2 ))                                             

| eq_asubst {S: TermSet} {A: AssertionSet} {t u: Term} {l: list Term} (proofMember: eq_ady S A (MemberAssertion t l)) (proofEq: eq_ady S A (EqAssertion t u)): eq_ady S A (MemberAssertion u l)

| eq_aprom {S: TermSet} {A: AssertionSet} {t n: Term} (proof: eq_ady S A (MemberAssertion t [n])) : eq_ady S A (EqAssertion t n)
| eq_aint {S: TermSet} {A: AssertionSet} {t: Term} {l: list Term} (premises: Eq_ValidIntPremiseList S A t l): eq_ady S A (MemberAssertion t l)
| eq_awk {S: TermSet} {A: AssertionSet} {t n: Term} {nlist: list Term} (proofEq: eq_ady S A (EqAssertion t n)) (proofIn: List.In n nlist) (proofValid: Eq_DerivableTermsList S nlist): eq_ady S A (MemberAssertion t nlist)                                                           
with Eq_ValidIntPremiseList: TermSet -> AssertionSet -> Term -> list Term -> Type:=
| Eq_TwoLists {S: TermSet} {A: AssertionSet} {t: Term} {l1 l2 intersect: list Term} (proofIntersect: ListIntersection l1 l2 intersect) (proof1: eq_ady S A (MemberAssertion t l1)) (proof2: eq_ady S A (MemberAssertion t l2)): Eq_ValidIntPremiseList S A t intersect
| Eq_NewList {S: TermSet} {A: AssertionSet} {t: Term} {l1 intersect intersectl1: list Term} (proofIntersect: ListIntersection l1 intersect intersectl1) (proof1: eq_ady S A (MemberAssertion t l1)) (proof2: Eq_ValidIntPremiseList S A t intersect): Eq_ValidIntPremiseList S A t intersectl1
                                                                                                                                                                                                                                                                             
with Eq_DerivableTermsList: TermSet -> list Term -> Type:=
| Eq_SingleDerivable {S: TermSet} {t: Term} (proof: dy S t): Eq_DerivableTermsList S [t]
| Eq_NewDerivable {S: TermSet} {t: Term} {tlist: list Term} (proofNew: dy S t) (proofList: Eq_DerivableTermsList S tlist): Eq_DerivableTermsList S (t::tlist)
                                                                                                                                                 
with Eq_ValidTransEqPremiseList: TermSet -> AssertionSet -> Term -> Term -> Type:=
| Eq_TwoTrans {S: TermSet} {A: AssertionSet} {t1 t2 t3: Term} (p1: eq_ady S A (EqAssertion t1 t2)) (p2: eq_ady S A (EqAssertion t2 t3)): Eq_ValidTransEqPremiseList S A t1 t3
| Eq_TransTrans {S: TermSet} {A: AssertionSet} {t1 tk tk': Term} (phead: eq_ady S A (EqAssertion t1 tk)) (plist: Eq_ValidTransEqPremiseList S A tk tk'): Eq_ValidTransEqPremiseList S A t1 tk'.


Definition term_eq_dec : forall (x y : Term), { x = y } + { x <> y }.
Proof.
repeat (decide equality).
Defined.

Fixpoint foldrEqIntList {X: Type} {S: TermSet} {A: AssertionSet} {t: Term} {tl: list Term} (f:forall (S': TermSet) (A': AssertionSet) (t': Term) (tl': list Term), eq_ady S' A' (MemberAssertion t' tl') -> X -> X) (l: Eq_ValidIntPremiseList S A t tl) (initial: X): X:=
  match l with
  | @Eq_TwoLists S' A t l1 l2 intersect pI p1 p2 => (f S' A t l1 p1 (f S' A t l2 p2 initial))
  | @Eq_NewList S' A t l1 i il1 pI p1 pL => (f S' A t l1 p1 (foldrEqIntList f  pL initial))
  end.


Fixpoint foldrEqDerivableTermsList {X: Type} {S: TermSet} {tl: list Term} (f: forall (S': TermSet) (t: Term), dy S' t -> X -> X) (fuel: Eq_DerivableTermsList S tl) (ember: X) : X :=
  match fuel with
  | @Eq_SingleDerivable S' t proof => f S' t proof ember
  | @Eq_NewDerivable S' t tlist proofNew proofList => f S' t proofNew (foldrEqDerivableTermsList f proofList ember)
  end.

Fixpoint foldrEqTransList {X: Type} {S: TermSet} {A: AssertionSet} {t1: Term} {tn: Term} (f: forall (S': TermSet) (A': AssertionSet) (t1: Term) (t2: Term), eq_ady S' A' (EqAssertion t1 t2) -> X -> X) (fuel: Eq_ValidTransEqPremiseList S A t1 tn) (ember: X) : X :=
  match fuel with
  | @Eq_TwoTrans S' A t1 t2 t3 p1 p2 => f S' A t1 t2 p1 (f S' A t2 t3 p2 ember)
  | @Eq_TransTrans S' A t1 tk tk' phead plist => f S' A t1 tk phead (foldrEqTransList f plist ember)
  end
.
Definition containsReflexiveTrans {S: TermSet} {A: AssertionSet} {a1 a2: Term} (l: Eq_ValidTransEqPremiseList S A a1 a2): bool := foldrEqTransList (fun (S': TermSet) (A': AssertionSet) (t1 t2: Term)  (proof: eq_ady S' A' (EqAssertion t1 t2))  (thing: bool) => if term_eq_dec t1 t2 then true else thing) l false.


Definition isCons {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) :bool :=
  match p with
  | eq_acons_pair _ _=> true
  | eq_acons_enc _ _=> true
  | _ => false
  end.


Fixpoint adjacentSafe {S: TermSet} {A: AssertionSet} {a1 a2: Term} (l: Eq_ValidTransEqPremiseList S A a1 a2): bool :=
  match l with
  | Eq_TwoTrans p1 p2 => negb (andb (isCons p1) (isCons p2))
  | Eq_TransTrans phead ptail => andb (negb (andb (isCons phead) match ptail with | Eq_TwoTrans p2 _ => (isCons p2) | Eq_TransTrans p2 _ => (isCons p2) end)) (adjacentSafe ptail)
  end.


Definition intPremiseSafe {S: TermSet} {A: AssertionSet} {t: Term} {l: list Term} (premises: Eq_ValidIntPremiseList S A t l): bool :=
  foldrEqIntList
    (fun (S': TermSet) (A': AssertionSet) (t': Term) (tl': list Term) (proof: eq_ady S' A' (MemberAssertion t' tl')) (fire: bool) => match proof with | eq_aint _ => false | eq_awk _ _ _ => false | _ => fire end)
    premises
    true.

(*MAKES PROOFS VERY MESSY*)
Fixpoint foldEqAdyProof {X: Type} {S: TermSet} {A: AssertionSet} {a: Assertion}  (f : forall (S': TermSet) (A': AssertionSet) (a': Assertion), eq_ady S' A' a' -> X -> X) (assertionProof: eq_ady S A a) (default: X) {struct assertionProof}: X.

Proof.
  assert (nextValue : X). {
  destruct assertionProof; try (apply (foldEqAdyProof _ _ _ _  f assertionProof1  (foldEqAdyProof _ _ _ _ f assertionProof2 default))); try (apply (foldEqAdyProof _ _ _ _ f assertionProof default)).
  - apply default.
  - apply default.
  - induction p.
    + apply (foldEqAdyProof _ _ _ _  f p1  (foldEqAdyProof _ _ _ _ f p2 default)).
    + apply (foldEqAdyProof _ _ _ _ f phead IHp).
  - induction premises.
    + apply (foldEqAdyProof _ _ _ _  f proof1  (foldEqAdyProof _ _ _ _ f proof2 default)).
    + apply (foldEqAdyProof _ _ _ _ f proof1 IHpremises).
  } apply (f S A a assertionProof nextValue).
Defined.

Print foldEqAdyProof.
(* Super Interesting !!*)
Module SanityCheck.
  Inductive even_list : Type :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list

  with odd_list : Type :=
  | OCons : nat -> even_list -> odd_list.

  Fixpoint elength (el : even_list) : nat.
  Proof.
    destruct el.
    - apply 0.
    - induction o.
      + apply (S (S n0)).
  Defined.

  Print elength.

  Example ex1: (elength (ECons 0 (OCons 0 (ENil)))) = 2.
  Proof.
    simpl. reflexivity.
  Qed.
End SanityCheck.
(** The above is super interesting !!!!!*)

(** The following is kept as an artifact.


Program Fixpoint foldEqAdyProof {X: Type} {S: TermSet} {A: AssertionSet} {a: Assertion}  (f : forall (S': TermSet) (A': AssertionSet) (a': Assertion), eq_ady S' A' a' -> X -> X) (assertionProof: eq_ady S A a) (default: X) {struct assertionProof}: X :=
  f S A a assertionProof
  match assertionProof with
  | @eq_aax _ _ _ _ => default
  | @eq_aeq _ _ _ _ => default
  | @eq_acons_pair _ _ _ _ _ _ p1 p2 => foldEqAdyProof f p1 (foldEqAdyProof f p2 default)
  | @eq_acons_privkey _ _ _ _ _ _ p1 p2 => foldEqAdyProof f p1 (foldEqAdyProof f p2 default)
  | @eq_acons_pubkey _ _ _ _ _ _ p1 p2 => foldEqAdyProof f p1 (foldEqAdyProof f p2 default)
  | @eq_asym _ _ _ _ p => foldEqAdyProof f p default
  | @eq_atrans _ _ _ _ prooflist =>
      foldrEqTransList
        (fun (S'': TermSet) (A'': AssertionSet) (t t': Term) (proof: eq_ady S'' A'' (EqAssertion t t')) (thing: X) => foldEqAdyProof f proof thing)
        prooflist
        default
  | @eq_aproj_pair_left _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_aproj_pair_right _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_aproj_privenc_term _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_aproj_privenc_key _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_aproj_pubenc_term _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_aproj_pubenc_key _ _ _ _ _ _ p _ => foldEqAdyProof f p default
  | @eq_asubst _ _ _ _ _ p1 p2 => foldEqAdyProof f p1 (foldEqAdyProof f p2 default)
  | @eq_aprom _ _ _ _ p => foldEqAdyProof f p default
  | @eq_aint _ _ _ _ prooflist =>
      foldrEqIntList
        (fun (S'': TermSet) (A'': AssertionSet) (t': Term) (tl': list Term) (proof: eq_ady S'' A'' (MemberAssertion t' tl')) (thing: X) => foldEqAdyProof f proof thing)
        prooflist
        default
  | @eq_awk _ _ _ _ _ p _ _ => foldEqAdyProof f p default
  end.


 *)
Fixpoint containsCons {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): bool.
Proof.
    remember proof as p. destruct proof.
  - apply false.
  - apply false.
  - apply true.
  - apply true. 
  - apply (containsCons _ _ _ proof).
  - assert (recursiveVal: bool). {
      dependent induction p0.
      - apply (containsCons _ _ _ p1 || containsCons _ _ _ p2).
      -  apply (containsCons _ _ _ phead || (IHp0 (eq_atrans p0) (eq_refl (eq_atrans p0)))).
    }

    apply recursiveVal.
  - 
    apply (containsCons _ _ _ proof).
  - apply (containsCons _ _ _ proof).
  - apply (containsCons _ _ _ proof).
  - apply (containsCons _ _ _ proof).
  - apply (containsCons _ _ _ proof1 || containsCons _ _ _ proof2).
  - apply (containsCons _ _ _ proof).
  - assert (recursiveVal: bool). {
      dependent induction premises.
      - apply (containsCons _ _ _ proof1 || containsCons _ _ _ proof2).
      -  apply (containsCons _ _ _ proof1 || IHpremises (eq_aint premises) (eq_refl _)).
    }

    apply recursiveVal.
  - 
    apply (containsCons _ _ _ proof).

Defined.

Fixpoint isNormalEqAssertionProof {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a): bool.
Proof.
  destruct proof.
  - apply true.
  - apply (andb (isNormal proof)
             match proof with
             | pair _ _ => false
             | senc _ _ => false
             | aenc _ _ => false
             | pk _ => false
             | _ => true
             end ).
  - apply ((isNormalEqAssertionProof _ _ _ proof1) && (isNormalEqAssertionProof _ _ _ proof2)).
  - apply ((isNormalEqAssertionProof _ _ _ proof1) && (isNormalEqAssertionProof _ _ _ proof2)).
  - apply ((match proof with | eq_aax _ _ => true | eq_aprom _ => true | _ => false end) && (isNormalEqAssertionProof _ _ _ proof)).
  - assert (recursiveVal: bool). {
      dependent induction p.
      - apply (isNormalEqAssertionProof _ _ _ p1 && isNormalEqAssertionProof _ _ _ p2).
      -  apply (isNormalEqAssertionProof _ _ _ phead && IHp).
    }

    apply ((negb (containsReflexiveTrans p)) && (adjacentSafe p) && recursiveVal).
  - 
    apply (negb (containsCons proof) && isNormalEqAssertionProof _ _ _ proof).
  - apply (negb (containsCons proof) && isNormalEqAssertionProof _ _ _ proof).
  - apply (negb (containsCons proof) && isNormalEqAssertionProof _ _ _ proof).
  - apply (negb (containsCons proof) && isNormalEqAssertionProof _ _ _ proof).
  - apply (isNormalEqAssertionProof _ _ _ proof1 && isNormalEqAssertionProof _ _ _ proof2).
  - apply (isNormalEqAssertionProof _ _ _ proof).
  - assert (recursiveVal: bool). {
      dependent induction premises.
      - apply (isNormalEqAssertionProof _ _ _ proof1 && isNormalEqAssertionProof _ _ _ proof2).
      -  apply (isNormalEqAssertionProof _ _ _ proof1 && IHpremises).
    }
    apply (foldrEqIntList
             (fun _ _ _ _ proof thing =>
                andb
                  match proof with
                  | eq_aint _ => false
                  | eq_awk _ _ _ => false
                  | _ => true
                          
                  end
                  thing)
             premises
             true

             && recursiveVal
          ).
  - 
    apply (foldrEqDerivableTermsList
             (fun _ _ proof thing => andb (isNormal proof) thing)
             proofValid
             true
           && isNormalEqAssertionProof _ _ _ proof).

Defined.

Print isNormalEqAssertionProof.
Inductive SubProofEqEq {S: TermSet} {A: AssertionSet} : forall {a1 a2: Assertion}, (eq_ady S A a1) -> (eq_ady S A a2) -> Prop:=

| SubProofEqEqRefl {a: Assertion}
    (pa: eq_ady S A a)
  : SubProofEqEq pa pa
| SubProofEqEqTrans {a1 a2 a3: Assertion}
    {pa1: eq_ady S A a1}
    {pa2: eq_ady S A a2}
    {pa3: eq_ady S A a3}
    (sub1: SubProofEqEq pa1 pa2)
    (sub2: SubProofEqEq pa2 pa3)
  : SubProofEqEq pa1 pa3
| SubProofEqEq_eq_acons_pair_left {t1 t2 u1 u2: Term} (p1: eq_ady S A (EqAssertion t1 u1)) (p2: eq_ady S A (EqAssertion t2 u2)): SubProofEqEq p1 (eq_acons_pair p1 p2)
| SubProofEqEq_eq_acons_pair_right {t1 t2 u1 u2: Term} (p1: eq_ady S A (EqAssertion t1 u1)) (p2: eq_ady S A (EqAssertion t2 u2)): SubProofEqEq p2 (eq_acons_pair p1 p2)

| SubProofEqEq_eq_acons_enc_term {t1 t2 : Term} {k1 k2 : Key}
    (p1:eq_ady S A (EqAssertion t1 t2))
    (p2: eq_ady S A (EqAssertion ((KeyTerm k1 )) (KeyTerm k2)))
  : SubProofEqEq p1 (eq_acons_enc p1 p2)
| SubProofEqEq_eq_acons_enc_key {t1 t2 : Term} {k1 k2 : Key}
    (p1:eq_ady S A (EqAssertion t1 t2))
    (p2: eq_ady S A (EqAssertion ((KeyTerm k1)) (KeyTerm k2)))
  : SubProofEqEq p2 (eq_acons_enc p1 p2)

| SubProofEqEq_eq_asym {t u: Term}
    (p: eq_ady S A (EqAssertion t u))
  : SubProofEqEq p (eq_asym p)

| SubProofEqEq_eq_atrans  {a: Assertion} {t1 tk : Term}
    {p: Eq_ValidTransEqPremiseList S A t1 tk}
    {pa: eq_ady S A a}
    (subp: SubProofEqTrans pa p)
  : SubProofEqEq pa (eq_atrans p)

| SubProofEqEq_eq_aproj_pair_left {t1 t2 u1 u2 : Term}
    (p: eq_ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))
    (p': In
           (AbstractablePositionSetAssertion S
              (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))
           [0; 0])
  : SubProofEqEq p (eq_aproj_pair_left p p')

| SubProofEqEq_eq_aproj_pair_right  {t1 t2 u1 u2 : Term}
    (p: eq_ady S A (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))
    (p': In
           (AbstractablePositionSetAssertion S
              (EqAssertion (PairTerm t1 t2) (PairTerm u1 u2)))
           [0; 1]) :
  SubProofEqEq p (eq_aproj_pair_right p p')

| SubProofEqEq_eq_aproj_enc_term   {k1 k2 : Key} {t1 t2 : Term}
    (p: eq_ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2))) 
    (p': In
           (AbstractablePositionSetAssertion S
              (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2)))
           [0; 0]) 
  : SubProofEqEq p (eq_aproj_enc_term p p')

| SubProofEqEq_eq_aproj_enc_key  {k1 k2 : Key} {t1 t2 : Term}
    (p: eq_ady S A (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2)))
    (p': In
           (AbstractablePositionSetAssertion S
              (EqAssertion (EncTerm t1 k1) (EncTerm t2 k2)))
           [0; 1])
  : SubProofEqEq p (eq_aproj_enc_key p p')
                 
| SubProofEqEq_eq_asubst_eq  {t u : Term} {l : list Term}
    (pmem: eq_ady S A (MemberAssertion t l))
    (peq: eq_ady S A (EqAssertion t u))
  : SubProofEqEq peq (eq_asubst pmem peq)

| SubProofEqEq_eq_asubst_mem  {t u : Term} {l : list Term}
    (pmem: eq_ady S A (MemberAssertion t l))
    (peq: eq_ady S A (EqAssertion t u))
  : SubProofEqEq pmem (eq_asubst pmem peq)

| SubProofEqEq_eq_aprom {t n : Term}
    (p: eq_ady S A (MemberAssertion t [n]))
  : SubProofEqEq p (eq_aprom p)

| SubProofEqEq_eq_aint {a: Assertion} {t: Term} {l: list Term}
    {pl: Eq_ValidIntPremiseList S A t l}
    {pa: eq_ady S A a}
    (subp: SubProofEqInt pa pl)
  : SubProofEqEq pa (eq_aint pl)
    

| SubProofEqEq_eq_awk {t n : Term} {nlist : list Term}
    (p: eq_ady S A (EqAssertion t n))
    (p': List.In n nlist)
    (p'l: Eq_DerivableTermsList S nlist)
  : SubProofEqEq p (eq_awk p p' p'l)
with SubProofEqInt {S: TermSet} {A: AssertionSet}: forall {a: Assertion} {t: Term} {tl: list Term}, eq_ady S A a -> Eq_ValidIntPremiseList S A t tl -> Type :=
| SubProofEqInt_Eq_TwoLists_Left {a: Assertion} {t : Term} {l1 l2 intersect : list Term}
    (pint: ListIntersection l1 l2 intersect)
    (p1: eq_ady S A (MemberAssertion t l1))
    (p2: eq_ady S A (MemberAssertion t l2))
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa p1)
  : SubProofEqInt pa (Eq_TwoLists pint p1 p2)
| SubProofEqInt_Eq_TwoLists_Right {a: Assertion} {t : Term} {l1 l2 intersect : list Term}
    (pint: ListIntersection l1 l2 intersect)
    (p1: eq_ady S A (MemberAssertion t l1))
    (p2: eq_ady S A (MemberAssertion t l2))
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa p2)
  : SubProofEqInt pa (Eq_TwoLists pint p1 p2)

| SubProofEqInt_Eq_NewList {a: Assertion} {t : Term} {l1 intersect intersectl1 : list Term}
    (pint: ListIntersection l1 intersect intersectl1)
    (phead: eq_ady S A (MemberAssertion t l1))
    (ptail: Eq_ValidIntPremiseList S A t intersect)
    {pa: eq_ady S A a}
    (subp: SubProofEqEq pa phead)
  : SubProofEqInt pa (Eq_NewList pint phead ptail)
with SubProofEqTrans {S: TermSet} {A: AssertionSet}: forall {a: Assertion} {t1 tn : Term}, eq_ady S A a -> Eq_ValidTransEqPremiseList S A t1 tn -> Type :=
| SubProofEqTrans_Eq_TwoTrans_Left {a: Assertion} {t1 t2 t3 : Term}
    (p1: eq_ady S A (EqAssertion t1 t2))
    (p2: eq_ady S A (EqAssertion t2 t3))
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa p1)
  : SubProofEqTrans pa (Eq_TwoTrans p1 p2)
                    
| SubProofEqTrans_Eq_TwoTrans_Right {a: Assertion} {t1 t2 t3 : Term}
    (p1: eq_ady S A (EqAssertion t1 t2))
    (p2: eq_ady S A (EqAssertion t2 t3))
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa p2)
  : SubProofEqTrans pa (Eq_TwoTrans p1 p2)

| SubProofEqTrans_Eq_TransTrans {a: Assertion} {t1 tk tk' : Term}
    (phead: eq_ady S A (EqAssertion t1 tk))
    (ptail: Eq_ValidTransEqPremiseList S A tk tk')
    {pa: eq_ady S A a}
    (psub: SubProofEqEq pa phead)
  : SubProofEqTrans pa (Eq_TransTrans phead ptail).
Compute True.


Inductive EqAdyProofTermSet {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Ensemble Term :=
| EqAdyProofTermSetCons {a': Assertion} {p': eq_ady S A a'} (pSUB: SubProofEqEq p' p) {t: Term} (pMAX: AssertionMaximalSubTerm a' t): In (EqAdyProofTermSet p) t.

Inductive ListsAssertionSet (A: AssertionSet) : Ensemble (list Term) :=
| ListsAssertionSetCons {l: list Term} (p: exists (t: Term), In A (MemberAssertion t l)) : In (ListsAssertionSet A) l.
Inductive ListsProofSet {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a) : Ensemble (list Term) :=
| ListsProofSetCons
    (l: list Term)
    (proof: exists (t: Term) (p': eq_ady S A (MemberAssertion t l)),
        SubProofEqEq p' p)
  : In (ListsProofSet p) l. 

Inductive ListsTermSet (S: TermSet): Ensemble (list Term) :=
| ListsTermSetCons {t: Term} (p: In S t) : In (ListsTermSet S) [t].
Definition Substitution := forall (v: Var), match v with inl _ => Term | inr _ => Key end.

Definition Empty {X: Type} (S: Ensemble X) : Prop :=
  forall (x: X), In S x -> False.
Definition ConcreteSubstitution (s: Substitution) :=
  forall (v: Var),
    match v with
    | inl v => Empty (FVSetTerm (s (inl v))) 
    | inr v => Empty (FVSetTerm (KeyTerm (s (inr v))))
    end.
Definition substkey (s: Substitution) (k: Key) : Key :=
  match k with
  | VarKey v => s (inr v)
  | _ => k
  end.

Fixpoint apply_substition (s: Substitution) (t: Term) : Term:=
  match t with
  | VarTerm v => s (inl v)
  | NameTerm m => NameTerm m
  | KeyTerm k => KeyTerm (substkey s k)
  | PairTerm t1 t2 => PairTerm (apply_substition s t1) (apply_substition s t2)
  | EncTerm t k => EncTerm (apply_substition s t) (substkey s k)
  end
.
Definition Consistent (S: TermSet) (A: AssertionSet) :=
  exists(s: Substitution),
    ConcreteSubstitution s ->
      ((forall t1 t2, eq_ady S A (EqAssertion t1 t2) -> (apply_substition s t1) = (apply_substition s t2)) /\
      (forall t tlist, eq_ady S A (MemberAssertion t tlist) -> List.In (apply_substition s t) tlist)).

Definition EqAdyNormalisation := forall {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a),
    Consistent S A -> exists (p': eq_ady S A a), isNormalEqAssertionProof p' = true.

Definition EqAdySubTerm := forall {S: TermSet} {A: AssertionSet} {a: Assertion} (p: eq_ady S A a),
    Consistent S A ->
    isNormalEqAssertionProof p = true ->
    let Y := Union (SubTermSet S) (AssertionSetSubTermSet (Union A (Singleton a))) in
    Included (EqAdyProofTermSet p) Y /\ Included (ListsProofSet p)
                                         (Union
                                            (ListsAssertionSet (Union A (Singleton a)))
                                            (ListsTermSet Y)).

Fixpoint proofTransformation {S: TermSet} {A: AssertionSet} {a: Assertion} (proof: eq_ady S A a) : eq_ady S A a.
Proof.
  remember proof as p. dependent destruction proof.
  - apply p.
  - dependent destruction proof.
    +
Admitted.


Theorem EqNormal: EqAdyNormalisation.
Proof.
  unfold EqAdyNormalisation.
  intros. remember p as p'. dependent induction p.
  - exists p'. subst. unfold isNormalEqAssertionProof; unfold foldEqAdyProof. simpl. reflexivity.
  - remember proof as proof'. dependent destruction proof; try (exists p'; subst p'; subst proof'; unfold isNormalEqAssertionProof; simpl; reflexivity).
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
      
  - specialize (IHp1 H p1 (eq_refl p1)); specialize (IHp2 H p2 (eq_refl p2)).
    destruct IHp1 as [p1' H1]. destruct IHp2 as [p2' H2]. exists (eq_acons_pair p1' p2'). simpl. rewrite -> H1. rewrite -> H2. simpl. reflexivity.

  - specialize (IHp1 H p1 (eq_refl p1)); specialize (IHp2 H p2 (eq_refl p2)).
    destruct IHp1 as [p1' H1]. destruct IHp2 as [p2' H2]. exists (eq_acons_enc p1' p2'). simpl. rewrite -> H2. rewrite -> H1. simpl. reflexivity.

  - specialize (IHp H p (eq_refl p)). clear Heqp' p. clear p'. destruct IHp as [p IHp]. remember p as p'. dependent destruction p'.
    + exists (eq_asym p).  subst p. unfold isNormalEqAssertionProof; unfold foldEqAdyProof. simpl. reflexivity.
    + exists p. subst p. assumption.
    + simpl in IHp. apply andb_true_iff in IHp. destruct IHp. exists (eq_asym p). simpl. isNormalEqAssertionProof in IHp.  unfold foldEqAdyProof in IHp. simpl in IHp. 
    
    Admitted.
