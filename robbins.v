From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                 Transcription of :                                         *)
(*           A Complete Proof of the Robbins Conjecture                       *)
(*                     Allen L. Mann                                          *)
(*                                                                            *)
(******************************************************************************)

Section B.

Variable t : Type.
Variable inv : t -> t.
Variable cup : t -> t -> t.
Variable cap : t -> t -> t.
Variable bot : t.
Variable top : t.

Local Notation "1" := top.
Local Notation "0" := bot.
Local Notation "a ^-1" := (inv a).
Local Notation "a ∪ b" := (cup a b) (at level 40).
Local Notation "a ∩ b" := (cap a b) (at level 40).

Record B := {
 B1 : forall x y z : t , x ∪ (y ∪ z) = (x ∪ y) ∪ z;
 B2 : forall x y : t, x ∪ y = y ∪ x;
 B3 : forall x y : t, x ∪ (x ∩ y) = x;
 B4 : forall x y z : t, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z);
 B5 : forall x : t, x ∪ x^-1 = 1;
 B'1 : forall x y z : t, x ∩ (y ∩ z) = (x ∩ y) ∩ z;
 B'2 : forall x y : t, x ∩ y = y ∩ x;
 B'3 : forall x y : t, x ∩ (x ∪ y) = x;
 B'4 : forall x y z : t, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z);
 B'5 : forall x : t, x ∩ x^-1 = 0
}.

Variable PB : B.

Lemma P1 x : (x ∪ x = x) /\ (x ∩ x = x).
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
by rewrite -{2}(B'3 x x) B3 -{4}(B3 x x) B'3.
Qed.

Lemma P1l x : x ∪ x = x.
Proof. by have [] := P1 x. Qed.

Lemma P1r x : x ∩ x = x.
Proof. by have [] := P1 x. Qed.

Lemma P2 x y : (x ∪ y = y <-> x ∩ y = x).
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
split => <-; first by rewrite B'3.
by rewrite B2 B'2 B3.
Qed.

Lemma P3 x : x ∪ 0 = x /\ x ∩ 1 = x.
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
split; first by rewrite -(B'5 x) B3.
by rewrite -(B5 x) B'3.
Qed.

Lemma P3l x : x ∪ 0 = x.
Proof. by have [] := P3 x. Qed.

Lemma P3r x : x ∩ 1 = x.
Proof. by have [] := P3 x. Qed.

Lemma P4 x : x ∪ 1 = 1 /\ x ∩ 0 = 0.
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := (PB).
split; first by rewrite -{1}(B5 x) B1 P1l.
by rewrite -{1}(B'5 x) B'1 P1r.
Qed.

Lemma P4l x : x ∪ 1 = 1.
Proof. by have [] := P4 x. Qed.
Lemma P4r x :  x ∩ 0 = 0.
Proof. by have [] := P4 x. Qed.

Definition is_comp x y := x ∪ y = 1 /\ x ∩ y = 0.

Lemma is_compC x y : is_comp x y -> is_comp y x.
Proof.
move=> [C1 C2].
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
by split; rewrite (B2, B'2).
Qed.

Lemma P5 x : is_comp x x^-1 /\ forall y z, is_comp x y -> is_comp x z -> y = z.
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
split=> [// | y z [yC1 yC2] [zC1 zC2]].
rewrite -[y]P3r -[z]P3r.
by rewrite -{1}zC1 -yC1 !B4 B'2 yC2 [z ∩ _]B'2 zC2 B'2.
Qed.

Lemma P5l x : is_comp x x^-1.
Proof. by have [] := P5 x. Qed.
Lemma P5r x y : is_comp x y -> x^-1 = y.
Proof. by move=> HC; have [xP5] := P5 x; apply. Qed.

Lemma P6 x : x^-1^-1 = x.
Proof. apply/P5r/is_compC/P5l. Qed.

Lemma P7 x y : x^-1 = y^-1 -> x = y.
Proof. by move=> H; rewrite -(P6 x) H P6. Qed.

Lemma P8 : 0^-1 = 1 /\ 1^-1 = 0.
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
suff : is_comp 0 1 by split; apply P5r=> //; apply is_compC.
split; first by rewrite B2 P3l.
by rewrite P3r.
Qed.

Lemma P9 x y : (x ∪ y)^-1 = x^-1 ∩ y^-1 /\ (x ∩ y)^-1 = x^-1 ∪ y^-1.
Proof.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := PB.
split; apply: P5r; split.
- by rewrite B'4 {1}[x ∪ _]B2 -!B1 !B5 !P4l P3r.
- by rewrite B'2 -B'1 B4 [_ ∩ y]B'2 B'5 P3l B'2 -B'1 B'5 P4r.
- by rewrite B2 B'4 B2 B1 B5 B2 P4l -B1 [_ ∪ y]B2 B5 P4l P3r.
by rewrite B4 [_ ∩ y]B'2 -B'1 B'5 P4r [_ ∩ x]B'2 -B'1 B'5 P4r P3l.
Qed.

Lemma P9l x y : (x ∪ y)^-1 = x^-1 ∩ y^-1.
Proof. by have [] := P9 x y. Qed.
Lemma P9r x y : (x ∩ y)^-1 = x^-1 ∪ y^-1.
Proof. by have [] := P9 x y. Qed.

Lemma CP9l x y : (x^-1 ∩ y^-1)^-1 = x ∪ y.
Proof. by rewrite -P9l P6. Qed.

Lemma CP9r x y : (x^-1 ∪ y^-1)^-1 = x ∩ y.
Proof. by rewrite -P9r P6. Qed.

End B.

Section H.

Variable t : Type.
Variable inv : t -> t.
Variable cup : t -> t -> t.

Local Notation "a ^-1" := (inv a).
Local Notation "a ∪ b" := (cup a b) (at level 40).

Record H := {
 H1 : forall x y z, x ∪ (y ∪ z) = (x ∪ y) ∪ z;
 H2 : forall x y, x ∪ y = y ∪ x;
 H3 : forall x y, (x^-1 ∪ y^-1)^-1 ∪ (x^-1 ∪ y)^-1 = x
}.

Variable cap : t -> t -> t.
Variable bot : t.
Variable top : t.

Local Notation "1" := top.
Local Notation "0" := bot.
Local Notation "a ∩ b" := (cap a b) (at level 40).

Lemma P10 : B inv cup cap bot top -> H.
Proof.
move => B.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := B.
split=> // x y.
by rewrite (CP9r B) // (P9l B) // (P6 B) // -B4 B5 (P3r B).
Qed.

Fixpoint ncup n t := if n is n1.+1 then t ∪ ncup n1 t else 0.

Notation "∪_( n ) t " := (ncup n t) (at level 10).

Lemma ncupS n v : ∪_(n.+1) v = v ∪ ∪_(n) v.
Proof. by []. Qed.

Record R := {
 R1 : forall x y z, x ∪ (y ∪ z) = (x ∪ y) ∪ z;
 R2 : forall x y, x ∪ y = y ∪ x;
 R3 : forall x y, ((x ∪ y)^-1 ∪ (x ∪ y^-1)^-1)^-1 = x
}.

Lemma P11 : B inv cup cap bot top -> R.
Proof.
move => B.
have [B1 B2 B3 B4 B5 B'1 B'2 B'3 B'4 B'5] := B.
split=> // x y.
by rewrite (P9l B) // !(P6 B) // -B'4 B'5 (P3l B).
Qed.

Ltac AC f H1 H2 :=
  repeat (rewrite // ?H1 //; ((congr (f _ _); [idtac]) || rewrite H2)).

Section HB.

Variable PH : H.

Lemma P12 x : x ∪ x^-1 = x^-1 ∪ x^-1^-1.
Proof.
have [H1 H2 H3] := PH.
rewrite -{1}[X in X ∪ _ = _](H3 _ x^-1^-1).
rewrite -{1}[X in _ ∪ X = _](H3 _ x^-1^-1).
rewrite -{1}[X in _ = X ∪ _](H3 _ x^-1).
rewrite -{1}[X in _ = _ ∪ X](H3 _ x^-1).
set X1 := (_ ∪ _)^-1; set X2 := (_ ∪ _)^-1.
set X3 := (_ ∪ _)^-1; set X4 := (_ ∪ _)^-1.
rewrite [x^-1^-1 ∪ _]H2 -/X2 [x^-1^-1^-1 ∪ _]H2 -/X3 [x^-1^-1^-1 ∪ _]H2 -/X1.
by AC cup H1 H2.
Qed.

Lemma P13 x : x^-1^-1 = x.
Proof.
have [H1 H2 H3] := PH.
rewrite -{1}[X in X = _](H3 _ x^-1).
rewrite [X in X^-1 ∪ _ = _]H2 -P12 -[X in _ = X](H3 x x^-1^-1).
by rewrite H2 [X in X^-1 ∪ _ = _]H2.
Qed.

Lemma P14 x y : x^-1 = y^-1 -> x = y.
Proof. by move=> H; rewrite -(P13 x) H P13. Qed.

Definition hcap x y := (x^-1 ∪ y^-1)^-1.
Local Notation "a ∩ b" := (hcap a b) (at level 40).

Variable a : t.
Definition htop := a ∪ a^-1.
Local Notation "1" := htop.
Definition hbot := 1^-1.
Local Notation "0" := hbot.

Let BH := B inv cup hcap hbot htop.

Lemma P15 x y : (x ∪ y)^-1 = x^-1 ∩ y^-1 /\ (x ∩ y)^-1 = x^-1 ∪ y^-1.
Proof. by have [H1 H2 H3] := PH; split; rewrite /hcap ?P13. Qed.

Lemma P15l x y : (x ∪ y)^-1 = x^-1 ∩ y^-1.
Proof. by have [] := P15 x y. Qed.
Lemma P15r x y : (x ∩ y)^-1 = x^-1 ∪ y^-1.
Proof. by have [] := P15 x y. Qed.

Lemma P16 x y : x ∪ y = (x^-1 ∩ y^-1)^-1.
Proof. by apply: P14; rewrite P15l P13. Qed.

Lemma P17 x y : (x ∩ y) ∪ (x ∩ y^-1) = x.
Proof. by have [H1 H2 H3] := PH; rewrite /hcap H2 H3. Qed.

Lemma P18 x y z : x ∩ (y ∩ z) = (x ∩ y) ∩ z.
Proof. by rewrite /hcap !P13 H1. Qed.

Lemma P19 x y : x ∩ y = y ∩ x.
Proof. by rewrite /hcap H2. Qed.

Lemma P20 x y : x ∪ x^-1 = y ∪ y^-1.
Proof.
rewrite -{1}[X in X ∪ _ = _](H3 PH _ y^-1).
rewrite -{1}[X in _ ∪ X = _](H3 PH _ y^-1).
rewrite -{1}[X in _ = X ∪ _](H3 PH _ x^-1).
rewrite -{1}[X in _ = _ ∪ X](H3 PH _ x^-1).
rewrite ![_ ∪ x^-1]H2 // ![_ ∪ (x^-1^-1)]H2 //.
by AC cup H1 H2.
Qed.

Lemma P21l x : x ∪ x^-1 = 1.
Proof. by exact: P20. Qed.

Lemma P21r x : x ∩ x^-1 = 0.
Proof. by rewrite /hcap P21l. Qed.

Lemma P22 x : x ∪ 0 = x /\ x ∩ 1 = x.
Proof.
have F1 : 1^-1 = (1 ∪ 1)^-1 ∪ 1^-1.
  by rewrite -/hbot -[X in X = _](H3 PH _ 0) !P13 P21l.
have F2 : 1 = 1 ∪ (1 ∪ 1)^-1.
  by rewrite -[X in X = _](P21l 1) F1 H1 // H2 // H1 // [1^-1 ∪ _]H2 // P21l.
have F3 : 1 = 1 ∪ 1.
  by rewrite -{1}(P21l (1 ∪ 1)) -H1 // -F2.
have F4 : 0 = 0 ∪ 0 by rewrite /hbot {1}F1 -F3.
have F5 z : z ∪ 0 = z.
 rewrite -{1}[X in X ∪ _ = _](H3 PH _ z).
 rewrite [X in (_ ∪ X^-1) ∪ _]H2 // P21l -H1 // -F4.
 rewrite -[X in _ ∪ X^-1 = _](P21l z).
 by rewrite -{1}[X in _ = X](H3 PH _ z) [X in _ ∪ X^-1 = _]H2.
by split; rewrite // /hcap F5 P13.
Qed.

Lemma P22l x : x ∪ 0 = x.
Proof. by have [] := P22 x. Qed.
Lemma P22r x : x ∩ 1 = x.
Proof. by have [] := P22 x. Qed.

Lemma P23 x : x ∪ x = x /\ x ∩ x = x.
Proof.
have F z : z ∩ z = z.
  rewrite -{1}[X in _ = X](H3 PH _ z) [X in _ = _ ∪ X^-1]H2 //.
  by rewrite P21l P22l P15l P13.
by split; rewrite // P16 F P13.
Qed.

Lemma P23l x : x ∪ x = x.
Proof. by have [] := P23 x. Qed.
Lemma P23r x : x ∩ x = x.
Proof. by have [] := P23 x. Qed.

Lemma P24 x : x ∪ 1 = 1 /\ x ∩ 0 = 0.
Proof.
have F z : z ∪ 1 = 1.
  by rewrite -{1}(P21l z) H1 // P23l P21l.
by split; rewrite // /hcap P13 F.
Qed.

Lemma P24l x : x ∪ 1 = 1.
Proof. by have [] := P24 x. Qed.
Lemma P24r x : x ∩ 0 = 0.
Proof. by have [] := P24 x. Qed.

Lemma P25 x y : x ∪ (x ∩ y) = x.
Proof.
by rewrite -{1}(H3 PH x y) /hcap H2 // H1 // P23l H3.
Qed.

Lemma P26 x y : x ∩ (x ∪ y) = x.
Proof.
by rewrite -{1}(P13 x) -{1}(P13 (x ∪ y)) -P15l (P15l x) P25 P13.
Qed.

Lemma P27 x y z : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
rewrite -[X in X = _](P17 _ y) -P18 (P19 _ y) P26.
rewrite -[X in X ∪ _ = _](P17 _ z) -[X in _ ∪ X = _](P17 _ z).
have -> : ((x ∩ (y ∪ z)) ∩ y^-1) ∩ z = (x ∩ y^-1) ∩ z.
  rewrite -{3}[z](P26 z y) H2 //.
  by AC hcap P18 P19.
rewrite -!P18 -P15l P21r P24r P22l.
rewrite -[X in X ∪ _ ∪ _]P23l -!H1 // H2 // !H1 //.
rewrite -[X in _ = X ∪ _ ](P17 _ z) -P18 -!H1 // !P18; congr (_ ∪ (_ ∪ _)).
by rewrite ![_ ∩ z]P19 !P18 H2 // P17.
Qed.

Lemma P28 x y z : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof. by rewrite !P16 (P15r y) P27 P15l. Qed.

Lemma P29 : B inv cup hcap hbot htop.
Proof.
have [H1 H2 H3] := PH.
split=> //.
- exact: P25.
- exact: P27.
- exact: P21l.
- exact: P18.
- exact: P19.
- exact: P26.
- exact: P28.
exact: P21r.
Qed.

End HB.

Let Wm2 := forall x, x^-1^-1 = x.

Lemma P30 : R -> Wm2 -> H.
Proof.
move=> [R1 R2 R3] HWm2.
split=> // x y.
by rewrite -[X in X = _]HWm2 R2 R3 HWm2.
Qed.

Let Wm1 := exists z, forall x, x ∪ z = x.

Lemma P31 : R -> Wm1 -> Wm2.
Proof.
move=> [R1 R2 R3] [zero HWm1] x.
have F1 z : zero = (z^-1 ∪ z^-1^-1)^-1.
  by rewrite -[zero](R3 _ z) ![zero ∪ _]R2 !HWm1.
have F2 z : z^-1 = (z^-1 ∪ z^-1^-1^-1)^-1^-1.
  by rewrite -{1}(R3 z^-1 z^-1^-1) -F1 R2 HWm1.
have F3 z : z^-1^-1^-1 = (z^-1^-1^-1 ∪ z^-1)^-1^-1.
  rewrite -{1}(R3 z^-1^-1^-1 z^-1) -[X in (_ ∪ X^-1)^-1 = _]R2.
  by rewrite -F1 HWm1.
have F4 z : z^-1^-1^-1 = z^-1 by rewrite F3 R2 -F2.
by rewrite -(R3 x x) F4.
Qed.

Let W0 := exists a, a ∪ a = a.

Lemma P32 : R -> W0 -> Wm1.
Proof.
move=> [R1 R2 R3] [a HW0].
pose zero := (a ∪ a^-1)^-1.
exists zero.
have F1 : a = (a^-1 ∪ zero)^-1.
  by rewrite -{1}(R3 a a) HW0.
have F2 x : a ∪ x = ((a ∪ x)^-1 ∪ ((a ∪ x)∪ a^-1)^-1)^-1.
  by rewrite -[X in X = _](R3 _ a) [_ ∪ a]R2 R1 HW0.
have F3 x : x = (((x ∪ a^-1) ∪ zero)^-1 ∪ (x ∪ a)^-1)^-1.
  by rewrite -{1}[X in X = _](R3 _ (a^-1 ∪ zero)) -F1 !R1.
have F4 : a^-1 = (((a ∪ a^-1) ∪ a^-1)^-1 ∪ a)^-1.
  by rewrite -{1}[X in X = _](R3 _ (a ∪ a^-1)) -F1 [a^-1 ∪ _]R2.
have F5 : a = (((a ∪ a^-1) ∪ zero)^-1 ∪ a^-1)^-1.
  by rewrite {1}(F3 a) HW0.
have F6 : a = (((a ∪ a^-1) ∪ a^-1)^-1 ∪ a^-1)^-1.
  rewrite -{1}[X in X = _](R3 _ ((a ∪ a^-1)∪ a^-1)).
  rewrite !R1 !HW0; congr (_ ∪ _)^-1.
  by rewrite {3}F4 R2.
have F7 : ((a ∪ a^-1) ∪ a^-1)^-1 = zero.
  by rewrite -{1}[X in X = _](R3 _ a) -F4 -F6 R2.
have F8 : a^-1 = (a ∪ zero)^-1.
  by rewrite F4 F7 R2.
have F9 : a ∪ zero = a.
  by rewrite F2 -F8 R2 -!R1 [zero ∪ _]R2 !R1 -F5.
move=> x.
rewrite /Wm1 -[X in X = _](R3 _ a).
by rewrite -!R1 ![zero ∪ _]R2 F9 !R1 R2 -F3.
Qed.

Lemma P33 a b c : R -> (a ∪ (b ∪ c)^-1)^-1 = ((a ∪ b) ∪ c^-1)^-1 -> a ∪ b = a.
Proof.
move=> [R1 R2 R3] H.
by rewrite -[X in X = _](R3 _ c) -H -[_ ∪ c]R1 R3.
Qed.

Lemma P34 a b c : R -> (a ∪ (b ∪ c)^-1)^-1 = (b ∪ (a ∪ c)^-1)^-1 -> a = b.
Proof.
move=> [R1 R2 R3] H.
rewrite -[X in X = _](R3 _ (b ∪ c)) H.
suff -> : a ∪ (b ∪ c) = b ∪ (a ∪ c) by rewrite R3.
by AC cup R1 R2.
Qed.

Lemma P35 a b c : R -> (a ∪ b^-1)^-1 = c -> ((a ∪ b)^-1 ∪ c)^-1 = a.
Proof.
move=> [R1 R2 R3] H.
by rewrite -[X in _ = X](R3 _ b) H.
Qed.

Lemma P36 k a b c :
  R -> (a ∪ b^-1)^-1 = c -> (a ∪ (iter k (cup (a ∪ c)) b)^-1)^-1 = c.
Proof.
move=> R H; have [R1 R2 R3] := R.
elim: k => //= k /(P35 R) {1}<-.
set bk := iter _ _ _.
apply: etrans (R3 c (a ∪ bk)).
rewrite R2; congr (_^-1 ∪ _^-1)^-1; AC cup R1 R2.
Qed.

Lemma P37 k a b :
  R -> (((a ∪ b^-1)^-1) ∪ b^-1)^-1 = a ->
  (iter k (cup (a ∪ (a ∪ b^-1)^-1)) b)^-1 = b^-1.
Proof.
move=> R H; have [R1 R2 R3] := R.
set c := (a ∪ _)^-1 in H.
have := P36 k R (refl_equal c).
set bk := iter _ _ _ => H1.
have := P36 k R H.
rewrite [c ∪ a]R2 -/bk => H2.
apply: (@P34 _ _ c R).
by rewrite [_ ∪ c]R2 H R2 H1 {1}/c R2 -H2 [_ ∪ c]R2.
Qed.

Lemma P38 k a b :
  R -> (a ∪ b)^-1 = b^-1 -> (iter k (cup (a ∪ (a ∪ b^-1)^-1)) b)^-1 = b^-1.
Proof.  by move=> R H; apply: P37; rewrite // -{2}H R2 // R3. Qed.

Lemma P39 a b (v1 := iter 2 (cup a) b) (v2 := iter 3 (cup a) b) :
 R -> v1^-1 = b^-1 -> v2^-1 = b^-1 -> v1 = v2.
Proof.
move=> R H1 H2.
have F1 : (v1 ∪ (iter 2 (cup a) b^-1)^-1)^-1 = b^-1.
  have /(P38 1 R){2}<- : ((a ∪ a) ∪ b)^-1 = b^-1.
    by rewrite -H1; congr (_^-1); AC cup R1 R2.
  by rewrite /v1 /=; congr (_^-1); AC cup R1 R2.
have F2 : ((((a ∪ a) ∪ b) ∪ a) ∪ (a ∪ b^-1)^-1)^-1 = b^-1.
  apply: etrans (_ : ((a ∪ a) ∪ b)^-1 = _); last first.
    by rewrite -H1 /v1 /=; congr (_^-1); AC cup R1 R2.
  have F : b^-1 = ((a ∪ a) ∪ b)^-1.
    by rewrite -H1 /v1 /=; congr (_^-1); AC cup R1 R2.
  rewrite -[X in _ = X](@P38 1 a ((a ∪ a) ∪ b) R) //=; last first.
    apply: etrans F.
    by rewrite -H2 /v2 /=; congr (_^-1); AC cup R1 R2.
  by rewrite -F; congr (_^-1); AC cup R1 R2.
apply: etrans (_ : ((a ∪ a) ∪ b) ∪ a = _); last first.
  rewrite /v2 /=; AC cup R1 R2.
apply: etrans (_ : (a ∪ a) ∪ b = _).
  rewrite /v1 /=; AC cup R1 R2.
apply/sym_eq/(@P33 _ _ (a ∪ b^-1) R).
rewrite F2; apply: etrans F1.
by rewrite /v1 /=; congr (_^-1); AC cup R1 R2.
Qed.

Lemma P40 a b :
  R -> (a ∪ b)^-1 = b^-1 \/ ((a ∪ b^-1)^-1 ∪ b^-1)^-1 = a ->
    iter 2 (cup (a ∪ (a ∪ b^-1)^-1)) b =
      iter 3 (cup (a ∪ (a ∪ b^-1)^-1)) b.
Proof.
by move=> R [H|H]; apply: P39=> //; (try by apply: P38); apply: P37.
Qed.

Definition W1 := exists a b, a ∪ b = b.

Lemma P41 : R -> W1 -> W0.
Proof.
move=> R [a [b W1]].
pose c := iter 2 (cup (a ∪ b^-1)^-1) b.
pose d := c ∪ (c ∪ c^-1)^-1.
exists ((d ∪ d) ∪ d).
have F1 : a ∪ c = c by rewrite /c /= -{6}W1; AC cup R1 R2.
have F2 : b^-1 = c^-1.
  have /(P38 2 R)<- : (a ∪ b)^-1 = b^-1 by rewrite W1.
  rewrite /c /=; congr _^-1.
  by rewrite -2!{6}W1; AC cup R1 R2.
have F3 : c ∪ (a ∪ c^-1)^-1 = c.
  rewrite {1}/c -F2.
  apply: etrans (_ : iter 3 (cup (a ∪ b^-1)^-1) b = _).
    by rewrite /=; AC cup R1 R2.
  apply: etrans (_ : iter 3 (cup (a ∪ (a ∪ b^-1)^-1)) b = _).
    by rewrite /= -3!{4}W1; AC cup R1 R2.
  rewrite -P40 //; last by left; rewrite W1.
  by rewrite /c /= -2!{6}W1; AC cup R1 R2.
have F4 : iter 2 (cup d) c = iter 3 (cup d) c.
  apply: P40 => //; right.
  rewrite -{1}F1 [a ∪ _]R2 // -[(_ ∪ _) ∪ c^-1]R1 //.
  by rewrite -{3}F3 R3.
pose V := (d ∪ (d ∪ (d ∪ (d ∪ (d ∪ c))))) ∪ (c ∪ c^-1)^-1.
rewrite /= in F4.
apply: etrans (_ : V = _).
  by rewrite /V {6}/d; AC cup R1 R2.
by rewrite /V -!F4 {3}/d; AC cup R1 R2.
Qed.

Lemma P42 : R -> W1 -> H.
Proof.
by move=> R W1; apply: (P30 R (P31 R (P32 R (P41 R W1)))).
Qed.

Lemma P43 x y : R -> ((x^-1 ∪ y)^-1 ∪ (x ∪ y)^-1)^-1 = y.
Proof. by move=> R; rewrite ![_ ∪ y]R2 // R2 // R3. Qed.

Lemma P44 x y : R ->
  ((((x ∪ y)^-1 ∪ x^-1) ∪ y)^-1 ∪ y)^-1 = (x ∪ y)^-1.
Proof.
move=> R.
apply: etrans (P43 (x^-1 ∪ y) (x ∪ y)^-1 R).
rewrite (P43 x y R) R2 //.
by congr ((_ ∪ _^-1)^-1); AC cup R1 R2.
Qed.

Lemma P45 x y : R ->
  ((((x^-1 ∪ y)^-1 ∪ x) ∪ y)^-1 ∪ y)^-1 = (x^-1 ∪ y)^-1.
Proof.
move=> R.
apply: etrans (P43 (x ∪ y) (x^-1 ∪ y)^-1 R).
rewrite [X in _ = (X^-1 ∪ _)^-1]R2 // (P43 x y R) R2 //.
by congr ((_ ∪ _^-1)^-1); AC cup R1 R2.
Qed.

Lemma P46 x y : R ->
  (((((x^-1 ∪ y)^-1 ∪ x) ∪ y)∪ y)^-1 ∪ (x^-1 ∪ y)^-1)^-1 = y.
Proof.
move=> R.
apply: etrans (P43 (((x^-1 ∪ y)^-1 ∪ x) ∪ y) y R).
by rewrite (P45 x y) // [X in _ = X^-1]R2.
Qed.

Lemma P47 x y z : R ->
  ((((((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪
              (x^-1 ∪ y)^-1) ∪ z)^-1) ∪ (y ∪ z)^-1)^-1 = z.
Proof.
move=> R.
pose w := ((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪ (x^-1 ∪ y)^-1.
apply: etrans (P43 w z R).
by rewrite (P46 x y) // [X in _ = X^-1]R2.
Qed.

Lemma P48 x y z : R ->
  ((((((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪
         (x^-1 ∪ y)^-1) ∪ (y ∪ z)^-1) ∪  z)^-1 ∪ z)^-1
    = (y ∪ z)^-1.
Proof.
move=> R.
pose w := (((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪ (x^-1 ∪ y)^-1) ∪ z.
apply: etrans (P43 w (y ∪ z)^-1 R).
rewrite (P47 x y z) // [X in _ = X^-1]R2 /w //.
by congr (_^-1 ∪ _)^-1; AC cup R1 R2.
Qed.

Lemma P49 x y z u : R ->
  ((((((((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪
          (x^-1 ∪ y)^-1) ∪ (y ∪ z)^-1) ∪  z)^-1 ∪ z) ∪ u)^-1 ∪
            ((y ∪ z)^-1 ∪ u)^-1)^-1 = u.
Proof.
move=> R.
pose w := (((((((x^-1 ∪ y)^-1 ∪ x) ∪ y) ∪ y)^-1 ∪ (x^-1 ∪ y)^-1)
                         ∪ (y ∪ z)^-1) ∪ z)^-1 ∪ z.
apply: etrans (P43 w u R).
by rewrite P48 // [X in _ = X^-1]R2 /w.
Qed.

Notation "n [.]  v " := (iter n.-1 (cup v) v) (at level 10).

Lemma P50 x : R ->
 ((((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1)^-1 ∪
     (((3 [.] x)^-1 ∪ x)^-1 ∪ (5 [.] x))^-1)^-1 = ((3 [.] x)^-1 ∪ x)^-1.
Proof.
move=> R.
have F1 : ((((((((3 [.] x)^-1 ∪ x)^-1 ∪ (5 [.] x))^-1 ∪ (3 [.] x)^-1) ∪
             ((3 [.] x)^-1 ∪ x)^-1) ∪ (2 [.] x))^-1 ∪
             ((3 [.] x)^-1 ∪ x)^-1) ∪ (2 [.] x))^-1 =
                 (((3 [.] x)^-1 ∪ x)^-1  ∪ (5 [.] x))^-1.
  apply: etrans (_ : (((3[.] x) ∪ ((3 [.] x)^-1 ∪ x)^-1) ∪ (2[.] x))^-1 = _); last first.
     by rewrite /=; congr _^-1;  AC cup R1 R2.
  rewrite -[X in _ = X^-1]R1 //.
  apply: etrans (P44 (3 [.] x) ((((3[.] x)^-1 ∪ x)^-1) ∪ 2[.] x) R).
  congr (_)^-1; rewrite -!R1 //.
  congr ((_^-1 ∪ _)^-1 ∪ _).
  rewrite  /=; AC cup R1 R2.
suff {3}<- : ((((3 [.] x)^-1 ∪ x)^-1 ∪ (5 [.] x))^-1 ∪
            (((3 [.] x)^-1) ∪ ((3 [.] x)^-1 ∪ x)^-1)^-1)^-1 = ((3[.] x)^-1 ∪ x)^-1.
  by rewrite  [X in _ = X^-1]R2 //; congr (_^-1 ∪ _)^-1; AC cup R1 R2.
rewrite -F1.
apply: etrans (P49 (3 [.] x) x (2 [.] x) _ R).
congr (_^-1 ∪ _)^-1.
rewrite -!R1 //; congr ((_ ∪ _) ^-1 ∪ _); last by rewrite /=; AC cup R1 R2.
rewrite !R1 //; congr ((_ ∪ _) ∪ _).
rewrite R2 //; congr (_ ∪ _^-1).
by rewrite /=; AC cup R1 R2.
Qed.

Lemma P51 x : R -> (((3 [.] x)^-1 ∪ x)^-1 ∪ (5 [.] x))^-1 = (3 [.] x)^-1.
Proof.
move=> R.
apply: etrans (sym_equal (P43 (((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1) _ R)) _.
rewrite P50 //.
apply: etrans (P47 (3 [.] x) x _ R).
rewrite R2 //; congr (_^-1 ∪ _^-1)^-1; last by rewrite R2.
set X := _^-1; set Y := _^-1; set Z := _^-1; set T := _^-1.
suff ->: Z = T by AC cup R1 R2.
by congr _^-1; rewrite /=; AC cup R1 R2.
Qed.

Lemma P52 x : R -> (((((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1) ∪
                      (2 [.] x))^-1 ∪ (3 [.] x)^-1)^-1 =
                     ((3 [.] x)^-1 ∪ x)^-1 ∪ (2 [.] x).
Proof.
move=> R.
rewrite -{3}(P51 x R).
apply: etrans (P43 (3 [.] x) _ R).
congr (_^-1 ∪ _^-1)^-1; last by rewrite /=; AC cup R1 R2.
by AC cup R1 R2.
Qed.

Lemma P53 x : R -> (((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1)^-1 = x.
Proof.
move=> R.
apply: etrans (P43 (((3 [.] x)^-1 ∪ x)^-1 ∪ (4 [.] x)) _ R).
set X := (_ ∪ 4 [.] _) ∪ x.
have ->: X = ((3[.] x)^-1 ∪ x)^-1 ∪ 5 [.] x.
  by rewrite /X /=; AC cup R1 R2.
rewrite P51 //.
have := P45 (3 [.] x) x R.
set Y := (_ ∪ 3 [.] _) ∪ x.
suff ->: Y = ((3[.] x)^-1 ∪ x)^-1 ∪ 4 [.] x by move=>->.
by rewrite /Y /=; AC cup R1 R2.
Qed.

Lemma P54 x y : R ->
  (((((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1) ∪ y)^-1 ∪ (x ∪ y)^-1)^-1 = y.
Proof.
move=> R.
apply: etrans (P43 (((3 [.] x)^-1 ∪ x)^-1 ∪ (3 [.] x)^-1) _ R).
by rewrite P53 // R2.
Qed.

Lemma P55 (a : t) : R -> W1.
Proof.
move=> R.
exists ((3 [.] a)^-1 ∪ a)^-1; exists (2 [.] a).
rewrite -P52 //.
have {3}->: 3[.] a = a ∪ 2 [.] a by rewrite /=; AC cup R1 R2.
by apply: P54.
Qed.

Lemma P56 a : R -> B inv cup hcap (hbot a) (htop a).
move=> R.
by apply/P29/P42/(P55 a).
Qed.

End H.

Goal True.
idtac "Boolean algebras".
Print B.
idtac "Robbins algebras".
Print R.
idtac "Boolean algebras are Robbins algebras".
Check P11.
idtac "Robbins algebras are Boolean algebras".
Check P56.
by [].
Qed.
