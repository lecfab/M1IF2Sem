
(** * Preuves en Coq *)
(*
  Tactiques permises : intros, apply, destruct, assumption, simpl.
  Compléter éventuellement les parties TOD0, et la tactique 'admit'...
  Rendre le script selon les instructions déjà  formulées dans les DM précédents.
 *)

(** ** Représentation des sigma-types dans les inductifs de Coq *)

Section SigmaType.
  Variable U : Type.
  Variable P : U -> Type.

  Inductive sigma : Type :=
    sigma_intro : forall x : U, P x -> sigma.

  Definition sigma_elim_left (e : sigma) : U.
    destruct e. (*on detruit pour directement obtenir le premier elem*)
    exact x.
  Defined.

Print sigma_elim_left.

(*
sigma_elim_left = 
fun e : sigma => match e with
                 | sigma_intro x _ => x
                 end
     : sigma -> U
*)

  Definition sigma_elim_right (e : sigma) : P (sigma_elim_left e).
    destruct e. (*on detruit*)
    simpl. (*on veut appliquer P au premier elem => on simplifie pour obtenir ce premier elem*)
    exact p. (*reste juste a voir que l'on a ce que l'on veut*)
  Defined.

Print sigma_elim_left.
(*
sigma_elim_left = 
fun e : sigma => match e with
                 | sigma_intro x _ => x
                 end
     : sigma -> U
*)

Print sigma_elim_right.
(*
fun e : sigma =>
match e as s return (P (sigma_elim_left s)) with
| sigma_intro _ p => p
end
     : forall e : sigma, P (sigma_elim_left e)
*)

Print sigma_intro.
End SigmaType.

(** ** Le théorème du choix (deux formulations) *)

Section Choix.
  Context (A B : Type).
  Context (C : A -> B -> Type).

  Theorem choice : (forall x :A, sigma B (C x)) -> sigma (A->B) (fun f:A->B => forall x:A, C x (f x)).
  Proof.
    intros.
    (*on doit introduire sigma_intro appliqué à une fonction A->B correcte*)
    apply (sigma_intro (A->B) (fun f:A->B => forall x:A, C x (f x)) (fun x:A => sigma_elim_left B (C x) (X x))).
    intros.
    apply sigma_elim_right.

    (*methode avec un with*)
    (*apply sigma_intro with (x := fun x:A => sigma_elim_left B (C x) (X x)).
    intros.
    apply sigma_elim_right.*)
  Qed.
End Choix.

(* Consulter Init/Specif.v pour le type sigT et son usage *)

Section Choix2.
  Context (A B : Type).
  Context (C : A -> B -> Type).
  
  Variable C_totale : forall x : A, {y : B & C x y}.

  Theorem choice2 : {f : A -> B & forall x : A, C x (f x)}.
  Proof.
    exists (fun x => projT1 (C_totale x)). (*on regarde la fonction qui récupère un elem qui marche pour x*)
    intro.
    destruct (C_totale x). (*on applique a x*)
    simpl. (*simplification de la fonction que l'on souhaite considérer*)
    assumption.
  Qed.
End Choix2.

(** ** L'égalité de Leibniz *)

Section Leibniz.
  Variable A : Prop.
  Definition eq (a b: A) : Prop := forall P : (A -> Prop), P a -> P b.

  Lemma eq_refl : forall a : A, eq a a.
  Proof.
    unfold eq.
    intros.
    assumption.
  Qed.

  Lemma eq_sym : forall a b : A, (eq a b) -> eq b a.
  Proof.
    unfold eq.
    intros a b H. (*ici doit conclure eq b a*)
    exact (H (fun x => eq x a) (eq_refl a)). (*on sait eq a a et donc grace a H on peut obtenir eq b a grace a la reflexivité*)
  Qed.

  Lemma eq_trans : forall a b c: A, (eq a b) -> (eq b c) -> (eq a c).
  Proof.
    intros.
    intro P.
    intro.
    apply H0. (*on veut P c et avec H0 il suffira d'avoir P b*)
    apply H. (*avec H il suffira d'avoir P a*)
    assumption. (*on l'a*)
  Qed.
End Leibniz.

(** ** Le type Identité dans les inductifs de Coq *)

Inductive Id {A : Type} : A -> A -> Type :=
  Id_reflexive : forall x : A, Id x x.

Print Id_rect.

(** On s'assure pour commencer que cela définit bien
    une relation d'équivalence sur le type {A} donné
    implicitement.
 *)

Lemma Id_refl {A : Type} : forall a : A, Id a a.
Proof.
  intro.
  exact (Id_reflexive a).
Qed.

Lemma Id_sym {A : Type} : forall a b : A, Id a b -> Id b a.
Proof.
  intros.
  destruct X.
  exact (Id_reflexive x).
Qed.

Lemma Id_trans {A : Type} : forall a b c : A, Id a b -> Id b c -> Id a c.
Proof.
  intros.
  destruct X.
  exact X0.
Qed.

Print Id_trans.
(*
Id_trans = 
fun (A : Type) (a b c : A) (X : Id a b) (X0 : Id b c) =>
match X in (Id y y0) return (Id y0 c -> Id y c) with
| Id_reflexive x => fun X1 : Id x c => X1
end X0
     : forall (A : Type) (a b c : A), Id a b -> Id b c -> Id a c
*)

(** ** Structure de groupoïde sur Id_A

    Pour des raisons qui seront expliqués en cours 9,
    on peut voir un témoin p : Id_A(a,b) comme un chemin
    qui relie a à b.

    On montre ici que sur la collection de tous les chemins
    qui peuvent être ainsi considérés entre deux termes
    quelconques du même type A, peut être équipée d'une
    structure de groupoïde *)

(** *** Tout chemin induit un chemin inverse *)

Definition path_inverse_exemple {A : Type} {x y : A} (p : Id x y) : Id y x
  := match p with Id_reflexive _ => Id_reflexive _ end.

(* Completer à votre tour la défintion suivante du même énoncé,
   mais en nous servant uniquement du langage de tactiques. *)
Definition path_inverse {A : Type} {x y : A} (p : Id x y) : Id y x.
  destruct p.
  exact (Id_reflexive x).
Defined.

Print path_inverse.

(*
fun (A : Type) (x y : A) (p : Id x y) =>
match p in (Id y0 y1) return (Id y1 y0) with
| Id_reflexive x0 => Id_reflexive x0
end
     : forall (A : Type) (x y : A), Id x y -> Id y x
*)

Print Id_sym.

(*
Id_sym = 
fun (A : Type) (a b : A) (X : Id a b) =>
match X in (Id y y0) return (Id y0 y) with
| Id_reflexive x => Id_reflexive x
end
     : forall (A : Type) (a b : A), Id a b -> Id b a
*)

(*On reconnait bien l'exemple*)

(** *** les chemins peuvent être concaténés : c'est notre loi 'interne' *)

Definition path_concat {A : Type} {x y z : A} (p : Id x y) (q : Id y z) : Id x z.
  destruct p.
  exact q.
Defined.

Print path_concat.
(*
path_concat = 
fun (A : Type) (x y z : A) (p : Id x y) (q : Id y z) =>
match p in (Id y0 y1) return (Id y1 z -> Id y0 z) with
| Id_reflexive x0 => fun q0 : Id x0 z => q0
end q
     : forall (A : Type) (x y z : A), Id x y -> Id y z -> Id x z
*)

(** *** cette loi est associative *)

Theorem concat_assoc
        {A : Type} {w x y z : A} (p : Id w x) (q : Id x y) (r : Id y z) :
  Id (path_concat p (path_concat q r)) (path_concat (path_concat p q) r).
Proof.
  destruct p.
  destruct q.
  destruct r.
  unfold path_concat.
  exact (Id_reflexive (Id_reflexive x)).
Qed.

(** *** on dispose de neutres à  gauche ET à  droite 
    d'où l'utilsation du type produit X * Y ici. *)
Theorem unity_laws {A : Type} {x y : A} :
  forall p : Id x y, (Id (path_concat (Id_reflexive x) p) p)
                   * (Id (path_concat p (Id_reflexive y)) p).
Proof.
  intros.
  destruct p.
  simpl.
  split. (*Il faut prouver les 2*)
  exact (Id_reflexive (Id_reflexive x)).
  exact (Id_reflexive (Id_reflexive x)).
Qed.

Theorem inverse_laws {A : Type} {x y : A} :
  forall p : Id x y, (Id (Id_reflexive x) (path_concat p (path_inverse p)))
                   * (Id (path_concat (path_inverse p) p) (Id_reflexive y)).
Proof.
  intros.
  destruct p.
  simpl.
  split.
  exact (Id_reflexive (Id_reflexive x)).
  exact (Id_reflexive (Id_reflexive x)).
Qed.

(** ** Un dernier petit exercice préparatoire au cours 9
    Sa signification est évidente, n'est-ce pas ? *)

Definition ap {A B : Type} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y). (*si x=y alors f x = f y*)
Proof.
  destruct p.
  exact (Id_reflexive (f x)).
Qed.
