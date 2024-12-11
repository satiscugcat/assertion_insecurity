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

Definition Var: Type := string.
Definition Name: Type:= string.

Inductive Term: Type :=
| VarTerm (v: Var)
| PrivKeyTerm (k: Name)
| PubKeyTerm (k: Name)
| PairTerm (t1 t2: Term)
| PrivEncTerm  (t: Term) (k: Name)
| PubEncTerm (t: Term) (k: Name).

Definition TermSet: Type := Ensemble Term.


Inductive dy : TermSet -> Term -> Type:=
| ax {X: TermSet} {t: Term} (inH: In Term X t) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (PrivKeyTerm k)) : dy X (PubKeyTerm k)
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (PairTerm t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (PairTerm t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (PrivEncTerm t k)) (kH: dy X (PrivKeyTerm k)): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (PrivKeyTerm k)) : dy X (PrivEncTerm t k)
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (PubEncTerm t k)) (keyH: dy X (PrivKeyTerm k)): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (PubKeyTerm k)) : dy X (PubEncTerm t k).

Theorem TermMonotonicity: forall (X Y: TermSet) (t: Term), (dy X t) -> (Included Term X Y) -> (dy Y t).
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
  
Fixpoint nPred (n: nat) : Type :=
  match n with
  | O => Prop
  | S n' => Term -> (nPred n')
  end.

Definition TermList: Type := list Term.

Inductive tLength: TermList -> nat -> Prop :=
| EmptyList : tLength [] 0
| AddElement {hd: Term} {tl: TermList} {n: nat} (H: tLength tl n): tLength (hd::tl) (S n).

Inductive Assertion: Type :=
| EqTerm (t u: Term)
| NAryPredicate {n: nat} (P: nPred n) {t: TermList} (lp: tLength t n)
| Member {n: nat} {t0: Term} {t: TermList} (lp: tLength t n)
| Conj (a0 a1 : Assertion)
| Exists (afun: Var -> Assertion)
| Says (k: Name) (a: Assertion).         
