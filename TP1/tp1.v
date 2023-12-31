(* TP1 Langages formels

   ATTENTION
   Pour le bon affichage des caractères accentués, précisez que l'encodage par défaut de votre NAVIGATEUR doit être Unicode (UTF-8)

   BUT DU TP

   Manipuler Coq / Gallina

   Se familiariser avec 4 mots-clés :
      - Definition
      - Definition avec match ... with
      - Inductive
      - Fixpoint
*)


(* DÉFINIR UN OBJET (entier, fonction, etc.) *)
(* Mot-clef "Definition" 
   suivi du nom de l'objet
   suivi de ":" 
   suivi du type de l'objet
   suivi de ":="
   suivi de la valeur de l'objet. *)
Definition a : nat := 3.
Definition b : nat := 6.

(* En Coq on donne TOUJOURS les types. *)

(* EFFECTUER UN CALCUL... dans l'interpréteur *)
(* Directive "Compute" *)
(* RÉSULTAT ATTENDU : 9 *)
Compute (a+b).

(* AFFICHER LE TYPE... dans l'interpréteur *)
(* Directive "Check" *)
Check (a+b).

Print a.



(* 1) TYPES ÉNUMÉRÉS et INDUCTIFS *)


(* Mots-clefs "Inductive" et "|" par cas. 
   C'est la définition d'un ensemble inductif, on donne des règles...
   Comme on définit un *type* de données, son propre type est Type. *)
Inductive jour : Type :=
  | lundi : jour
  | mardi : jour
  | mercredi : jour
  | jeudi : jour
  | vendredi: jour
  | samedi : jour
  | dimanche : jour.
(* ici uniquement des cas de base *)


(* On peut définir une FONCTION jour_suivant sur ce type.
   (jour_suivant e) s'évalue en le nom du jour suivant le jour e.
   Elle est réalisée suivant *la forme* du paramètre, c'est du
   "filtrage" ou "PATTERN MATCHING". C'est le mécanisme le plus
   confortable pour manipuler des structures inductives. *)
(* Mots-clef "match" "with" "end" *)
Definition jour_suivant (j : jour) : jour :=
  match j with
  | lundi => mardi
  | mardi => mercredi
  | mercredi => jeudi
  | jeudi => vendredi
  | vendredi => samedi
  | samedi => dimanche
  | dimanche => lundi
  end.

(* On teste. RÉSULTAT ATTENDU : jeudi *)
Compute (jour_suivant mercredi).


(* EXERCICE *)
(* Définir la fonction qui retourne le surlendemain d'un jour donné *)
(* C'est une fonction qui APPLIQUÉE À un jour, RETOURNE un jour *)

Definition sur_lendemain (j : jour) : jour :=
  match j with
  | lundi => mercredi
  | mardi => jeudi
  | mercredi => vendredi
  | jeudi => samedi
  | vendredi => dimanche
  | samedi => lundi
  | dimanche => mardi
  end.

(* On re-teste et on devrait obtenir vendredi*)
(* Compute (jour_suivant_le_jour_suivant mercredi). *)


(* On peut aussi définir les booléens... *)
(* Il n'y a que des cas de base et on va les appeler Vrai et Faux *)
Inductive booleens : Type :=
| Vrai : booleens
| Faux : booleens.

(* Ainsi que les fonctions logiques usuelles. *)
(* Le complémentaire : non. *)
Definition non (a : booleens) : booleens :=
  match a with
  | Vrai => Faux
  | Faux => Vrai
  end.


(* Directive d'affichage de type *)
Check non.

(* Directive d'affichage de valeur *)
Print non.


(* EXERCICE *)
(* Définir la fonction "et" sur les booléens. *)
Definition et (a : booleens) (b : booleens) : booleens :=
  match a with
  | Faux => Faux
  | Vrai => match b with
            |Faux => Faux
            |Vrai => Vrai
            end
  end.

(* un petit test, RÉPONSE ATTENDUE : Faux *)
Compute (et Vrai (et Faux Vrai)).


(* EXERCICE *)
(* Définir la fonction "ou" sur les booléens. *)
Definition ou (a : booleens) (b: booleens) : booleens :=
   match a with 
   | Vrai => Vrai 
   | Faux => match b with  
            | Faux => Faux
            | Vrai => Vrai
            end
   end. 

(* RÉPONSE ATTENDUE : Vrai *)
Compute (et Vrai (ou Faux Vrai)). 


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction bcompose : f -> g -> h telle que h est la composition des
deux fonctions booléennes f et g *)

Definition bcompose (f : booleens -> booleens) (g : booleens -> booleens) (a : booleens) : booleens :=
  (f (g a)). 


(* Tester bcompose en définissant une fonction nonnon : booléens -> booléens qui
définit non o non *)
Definition nonnon (a: booleens) : booleens :=
  bcompose non non a.


(* RÉSULTAT ATTENDU : Vrai *)
Compute (nonnon Vrai).


(* Le langage de Coq a bien sûr des booléens (dans le type prédéfini bool),
   ils sont en fait définis de la même façon que nos booleens. Pour l'instant
   nous allons continuer de travailler avec les nôtres. *)

(* On définit maintenant de façon inductive le type des entiers naturels.
   Un entier naturel est :
   - soit un élément particulier noté Z (pour zéro, c'est un cas de base ici),
   - soit le successeur d'un entier naturel.
 
   On a bien DEUX CONSTRUCTEURS pour les entiers : ils sont soit de la
   *forme* "Z" soit de la *forme* "Succ d'un entier".
*)
Inductive entiers : Type :=
| Z : entiers
| Succ : entiers -> entiers.

Definition un  := Succ Z.
Definition deux  := Succ un.
Definition trois  := Succ deux.


(* EXERCICE *)
(* Définir la fonction prédécesseur *)
(* C'est une fonction qui APPLIQUÉE À un entier, RETOURNE un entier *)
(* On considère que le prédécesseur de quelque chose de la forme Z est... Z *)
(* Le prédécesseur de quelque chose de la forme Succ toto est bien sûr toto *)

Definition pred (a : entiers) : entiers :=
  match a with
  | Z => Z
  | Succ a => a
end.

(* RÉSULTAT ATTENDU :  Succ (Succ Z) *)
Compute (pred (Succ (Succ (Succ Z)))).


(* On veut écrire une FONCTION RÉCURSIVE pour ajouter deux entiers.
   Comme la fonction est récursive, on utilise le mot-clé Fixpoint (et
   non plus Definition).
   Elle se calcule selon la forme du premier paramètre *) 
Fixpoint plus (a : entiers) (b : entiers) : entiers :=
  match a with
  | Z => b
  | Succ n => Succ (plus n b)
  end.

Compute(plus deux (plus trois deux)).


(* EXERCICE *)
(* Multiplication
   Elle se calcule selon la forme du premier paramètre *)
Fixpoint mult (a : entiers) (b : entiers) : entiers := 
  match a with
  |Z => Z
  |Succ n => plus b (mult n b)
end.

(* RÉSULTAT ATTENDU : 9 *)
Compute (mult (plus trois trois) trois).


(* EXERCICE *)
(* Définir une fonction est_pair, telle que est_pair APPLIQUÉE À un entier a RETOURNE Vrai si a est pair, Faux sinon. *)


(* RÉSULTAT ATTENDU : Vrai *)
(*Compute (est_pair un). *)

(* RÉSULTAT ATTENDU : Faux *)
(*Compute (est_pair trois).*) 


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction factorielle sur les entiers *)
Fixpoint factorielle (a : entiers) : entiers :=
  match a with
  | Z => un
  | Succ n => mult (Succ n) (factorielle n)
  end.


(* RÉSULTAT ATTENDU : 24 sous forme de Succ( ... (Succ(Z) ...) *)
Compute (factorielle (plus trois un)). 


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction moins, soustraction non négative sur les entiers *)

Fixpoint moins (a :entiers) (b:entiers) : entiers :=
  match b with
  | Z => a
  | Succ n => moins (pred a) n
  end.

(* RÉSULTAT ATTENDU : Succ Z *)
Compute (moins (mult trois trois) deux).

(* RÉSULTAT ATTENDU : Z *)
Compute (moins deux trois).

(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction inf, tel que inf a b vaut/retourne Vrai si a est
   inférieur ou égal à b, Faux sinon. *)
Definition inf (a : entiers) (b : entiers) : booleens := 
  match (moins a b) with
  | Z => match (moins b a) with 
         |Z => Vrai
         |Succ n => Faux
         end
  | Succ n => Vrai
  end. 
(* RÉSULTAT ATTENDU : Vrai *)
Compute (inf un trois).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction egal, tel que egal a b donne Vrai si les entiers
   a et b sont égaux, Faux sinon.*)

Definition egal (a : entiers) (b: entiers) : booleens :=
match (moins a b) with
  | Z => match (moins b a) with
         |Z => Vrai
         | Succ n => Faux
         end
  |Succ n => Faux
  end.

(* RÉSULTAT ATTENDU : Vrai *)
Compute (egal trois trois).

(* RÉSULTAT ATTENDU : Faux *)
Compute (egal un trois).


(* ------------------------------------------------------------ *)


(* Précédemment, on a défini nos booléens et nos entiers naturels,
mais ils sont en fait déjà définis dans la bibliothèque que Coq charge
initialement au démarrage :

NE PAS DECOMMENTER CE QUI SUIT, CE SONT DES TYPES COQ PREDEFINIS

Inductive bool : Set :=
  | true : bool
  | false : bool.

avec les fonctions 

negb (le complémentaire)
andb (le et, (le min))
orb  (le ou, (le max))

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

avec les fonctions usuelles + , - , * , etc.
et les comparaisons :
Nat.eqb pour le test d'égalité
Nat.ltb pour le test plus petit
Nat.leb pour le test plus petit ou égal.


CE SONT EUX QU'ON UTILISERA DORÉNAVANT.

 *)

(* ------------------------------------------------------------ *)


(* 2) LISTES D'OBJETS DE TYPE NAT *)


(* On considère ici des listes d'objets de type nat. *)

(* On peut définir de façon inductive un type nliste pour les listes d'objets de type nat. 
  Le cas de base est bien sûr la liste vide, l'autre règle de construction applique cons
  à un nat et une liste de l'ensemble inductif pour créer un nouvel élément de cet ensemble
*)
Inductive nliste : Type :=
  | vide : nliste
  | cons : nat -> nliste -> nliste.

Definition liste0 := vide.
Definition liste1 := cons 1 vide.
Definition liste2 := cons 2 (cons 1 vide).
Definition liste3 := cons 3 (cons 2 (cons 1 vide)).
Definition liste4 := cons 4 (cons 3 (cons 2 (cons 1 vide))).
Print liste0.
Print liste1.
Print liste2.


(* EXERCICE *)
(* Écrire une fonction ajoute: nat -> nliste -> nliste telle que ajoute n l
   retourne une liste correspondant à l'ajout de l'élément n à la liste l.
   C'est bien sûr juste la fonction qui applique cons
*)

Fixpoint ajoute (e : nat) (l : nliste) : nliste :=
  match l with
  | vide => cons e vide
  | cons x n => cons e (ajoute x n)
  end.

(* RÉSULTAT ATTENDU : cons 3 (cons 2 (cons 1 vide)) *)
Compute (ajoute 3 liste2).


(* EXERCICE *)
(* Écrire une fonction longueur telle que longueur APPLIQUÉE À l
   RETOURNE le nombre (nat) d'éléments de la liste l.  On l'a vue en
   cours.
  C'est bien sûr une fonction qui travaille selon la FORME de l : si
  c'est vide, la longueur vaut zéro, et si l est de la forme cons n l'
  à vous de jouer.  *)
Fixpoint longueur (l : nliste) : nat :=
  match l with
  | vide => 0
  | cons x n => 1 + (longueur n)
end. 


(* RÉSULTAT ATTENDU : 2 *)
Compute (longueur liste2).

(* EXERCICE *)
(* Écrire une fonction concat: nliste -> nliste -> nliste telle que concat l l'
   retourne une liste correspondant à l'ajout des éléments de l en tête de la liste l'. *)

Fixpoint concat (l1 : nliste) (l2 : nliste) : nliste :=
  match l1 with
  | vide => l2
  | cons x n => ajoute x (concat n  l2)
end. 

(* RÉSULTAT ATTENDU : cons 2 (cons 1 (cons 2 (cons 1 vide))) *)
Compute (concat liste2 liste2).

(* EXERCICE *)
(* Écrire une fonction recherche: nat -> nliste -> bool telle que recherche n l
   retourne Vrai si un élément n appartient à la liste l et Faux sinon. *)
(* Pour l'égalité entre éléments du type nat, soit on la redéfinit, soit on utilise Nat.eqb *)
Require Import Nat.
Check (eqb 3 4).
Compute (eqb 3 4).

Fixpoint recherche (e : nat) (l1 : nliste) : bool :=
  match l1 with
  | vide => false
  | cons x n => match (eqb e x) with
                |false => recherche e n
                |true => true
                end
  end.
  
 
(* RÉSULTAT ATTENDU : true *)
Compute (recherche 1 liste2).

(* RÉSULTAT ATTENDU : false *)
Compute (recherche 3 liste2).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction miroir: nliste -> nliste, qui
   retourne une liste correspondant à son argument dans l'ordre
   inverse. Dans un premier temps, on pourra utiliser la fonction de
   concaténation vue précédemment. *)

Fixpoint miroir (l1 : nliste) : nliste :=
  match l1 with
  | vide => vide
  | cons x n => concat (miroir n) (ajoute x vide) 
  end.

(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 3 (cons 4 vide))) *)
Compute (miroir liste3 ).
Compute (miroir liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction supprime: nat -> nliste -> nliste telle que
   supprime n l retourne une liste d'objets de type nat correspondant
   à l sans la première occurrence de n (le cas échéant), à l
   sinon. *)
Fixpoint supprime (e : nat) (l1 : nliste) : nliste :=
  match l1 with
  |vide => vide
  |cons x n => match (eqb x e) with
               |true => n
               |false => ajoute x (supprime e n)
               end
  end.
     


(* RÉSULTAT ATTENDU : cons 4 (cons 2 (cons 1 vide)) *)
Compute (supprime 3 liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction supprime_tout: nat -> nliste -> nliste telle
   que supprime_tout n l retourne une liste correspondant à l sans
   occurrence d'un nat n (le cas échéant), à l sinon. *)

Fixpoint supprime_tout (e : nat) (l1 : nliste) : nliste :=
  match l1 with
  |vide => vide
  |cons x n => match (eqb x e) with
               |true => supprime_tout e n
               |false => ajoute x (supprime_tout e n)
               end
  end.

Compute(supprime_tout 2 (concat liste4 liste4)).

(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction il_existe_pair: nliste -> bool, telle que
   il_existe_pair l retourne Vrai si un élément de l est pair, Faux
   sinon. *)

Fixpoint il_existe_pair (l1 : nliste) : bool :=
  match l1 with
  | vide => false
  | cons x n => match modulo x 2 with
                | 0 => true
                | _ => il_existe_pair n
                end
  end. 


(* RÉSULTAT ATTENDU : true *)
Compute (il_existe_pair liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Insertion triée *)
(* Écrire dans un premier temps une fonction leq : nat -> nat -> bool qui teste si le
premier entier est inférieur ou égal au second *)

Definition leq (a : nat) (b : nat) : bool :=  
 match (a - b) with
 |0 => match (b -a) with
        |0 => true
        |_ => true 
        end
 |_ => false
 end.
 
(* RÉSULTAT ATTENDU : true *)
Compute (leq 2 2).

(* RÉSULTAT ATTENDU : true *)
Compute (leq 2 3).

(* RÉSULTAT ATTENDU : false *)
Compute (leq 3 2).

(* Écrire une fonction insertion_triee : nat -> nliste -> nliste qui effectue
une insertion triée dans une liste *)
Fixpoint insertion_triee (e : nat) (l1 : nliste) : nliste :=
  match l1 with
  | vide => cons e vide
  | cons x n => match (leq x e) with
                | true => ajoute x (insertion_triee e n)
                | false => ajoute e (ajoute x n)
                end
 end.


(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 2 (cons 3 (cons 4 vide)))) *)
Compute (insertion_triee 2 (miroir liste4)).

(* RÉSULTAT ATTENDU : cons 4 (cons 3 (cons 2 (cons 1 (cons 6 vide)))) *)
Compute (insertion_triee 6 liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Tri par insertion d'une liste *)
(* Écrire une fonction tri_insertion : nliste -> nliste qui effectue
le tri par insertion d'une liste *)

Fixpoint tri_insertion (l1 : nliste) : nliste :=
  match l1 with
  | vide => vide
  | cons x n => insertion_triee x (tri_insertion n)
  end.

(* RÉSULTAT ATTENDU : cons 1 (cons 1 (cons 2 (cons 2 (cons 3 (cons 3 (cons 4 (cons 4 vide)))))) *)
Compute (tri_insertion (concat liste4 liste4)).




(* 3) ARBRES BINAIRES *)


(* EXERCICE *)
(* Donner une définition par induction de l'ensemble nBin des arbres
binaires contenant des nat. On souhaite avoir une représentation de
l'arbre vide dans nBin. *)



Inductive nBin : Type :=
  | nEmpty : nBin
  | nNode : nBin -> nat -> nBin -> nBin.



(* Donner un exemple d'arbre, disons à 5 éléments *)


Definition a1 := nNode
                      (nNode nEmpty 2 nEmpty)
                      1
                      (nNode
                            (nNode nEmpty 4 nEmpty)
                            3
                            (nNode nEmpty 5 nEmpty)
                      ).

Check a1.
Print a1.

(* EXERCICE *)
(* Définir la fonction nelements qui renvoie la liste des éléments
   contenus dans un arbre binaire de nat. Le faire naïvement avec un
   concat pour commencer. *)
   
Fixpoint nelements (abr : nBin) : nliste :=
  match abr with
  | nEmpty => vide
  | nNode abrG x abrD => ajoute x (concat 
                              (nelements abrG) 
                              (nelements abrD))
  end.


(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 3 (cons 4 (cons 5 vide)))) *)
Compute (nelements a1).



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nnelts qui renvoie le nombre de noeuds internes
   (portant une étiquette de type nat) dans un nBin. *)

Fixpoint nnelts (abr : nBin) : nat :=
  match abr with
  |nEmpty => 0
  |nNode abrG x abrD => 1 + nnelts abrG + nnelts abrD
  end.

(* RÉSULTAT ATTENDU : 5 *)
Compute (nnelts a1).



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nfeuilles qui renvoie le nombre de feuilles *)

Fixpoint nfeuilles (abr : nBin) : nat :=
  match abr with
  |nEmpty => 1
  |nNode abrG x abrD => nfeuilles abrG + nfeuilles abrD
  end.

(* RÉSULTAT ATTENDU : 6 *)
Compute nfeuilles a1.



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nsum qui renvoie la somme des valeurs portées
   par les noeuds internes d'un nBin. *)
   
Fixpoint nsum (abr : nBin) : nat :=
  match abr with
  |nEmpty => 0
  |nNode abrG x abrD => x + nsum abrG + nsum abrD
  end.
  
  
(* RÉSULTAT ATTENDU : 15 *)
Compute (nsum a1).



(* ------------------------------------------------------------ *)



