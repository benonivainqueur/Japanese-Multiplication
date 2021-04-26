;; DATA STRUCTURES ;;
(defdata lon (listof nat))
(defdata lolon (listof lon))

 

(check= (lonp '()) t)
(check= (lonp 'a) nil)
(check= (lonp '(1 2)) t)
(check= (lonp '(1 a)) nil)

 

;; turns a number (in reverse-digitized form) into standard written form
;; in the given base
(definec list-to-num (lst :lon base :nat) :nat
 (if (endp lst)
     0
    (+ (car lst) (* base (list-to-num (cdr lst) base)))))
(check= (list-to-num '(1 2 3) 10) 321)
(check= (list-to-num '(1 2 4 123) 0) 1)
(check= (list-to-num '() 3) 0)

 

;; LIST-TO-NUM AXIOMS
;; several associated axioms of this function

 

(defthm ltm-axiom-1
  (implies (and (lonp x) (zerop z) (not (endp x)))
           (equal (car x) (list-to-num x z))))

 

(defthm ltm-axiom-2
  (implies (and (lonp x) (zerop z) (endp x))
           (zerop (list-to-num x z))))

 

(defthm ltm-axiom-3
  (implies (and (lonp x) (natp z) (endp x))
           (zerop (list-to-num x z))))

 

;; a wrapper for standard multiplication given two numbers in reverse-digitized form
(definec normal-mult (list1 :lon list2 :lon base :nat) :nat
 (* (list-to-num list1 base) (list-to-num list2 base)))

 

;; scales a vector by a constant according to standard scalar
;; multiplication on vectors
(definec scale (vector :lon const :nat) :lon
  (cond
   ((endp vector) '())
   (t (cons (* (car vector) const) (scale (cdr vector) const)))))

 

(check= (scale '(1 2 3 4) 2) '(2 4 6 8))
(check= (scale '() 2) '())
(check= (scale '(1 2 3 4) 0) '(0 0 0 0))

 

;; SCALE AXIOMS
;; several associated axioms of this function

 

(defthm scale-axiom-1
  (implies (and (lonp x) (natp y) (natp z))
           (equal (list-to-num (scale x y) z)
                  (* y (list-to-num x z)))))

 

(defthm scale-axiom-2
  (implies (and (lonp x)
                (lonp y)
                (natp z)
                (not (endp y)))
           (equal (* (list-to-num x z) (car y))
                  (list-to-num (scale x (car y)) z))))

 


;; appends each value from the lon onto the lolon in
;; the same index
(definec append-lon (mat :lolon vec :lon) :lolon
;(defun append-lon (mat vec)
  (cond
   ((endp vec) mat)
   ((endp mat) (cons (list (car vec)) (append-lon mat (cdr vec))))
   (t (cons (cons (car vec) (car mat))
            (append-lon (cdr mat) (cdr vec))))))

 

(check= (append-lon '((1) (1 2)) '(1 2)) '((1 1) (2 1 2)))
(check= (append-lon '() '()) '())
(check= (append-lon '((8) (10)) '(1)) '((1 8) (10)))
(check= (append-lon '() '(8)) '((8)))

 

;; APPEND-LON AXIOMS
;; several associated axioms of this function

 

(defthm append-axiom-1
  (implies (and (lonp x) (lolonp y) (endp x))
           (equal (append-lon y x) y)))
(defthm append-axiom-2
  (implies (and (lonp x) (lolonp y) (endp x) (endp y))
           (endp (append-lon y x))))

 

;; handles diagonalizing multiplying (component wise)
;; of the two vectors/lists of digits
(definec diagonalize (list1 :lon list2 :lon) :lolon
  (if (endp list2)
     '()
     (append-lon
       (cons '() (diagonalize list1 (cdr list2)))
       (scale list1 (car list2)))))

 

(check= (diagonalize '() '()) '())
(check= (diagonalize '(2) '(8)) '((16)))
(check= (diagonalize '(2 3) '(8 7)) '((16) (24 14) (21)))

 

;; DIAGONALIZE AXIOMS
;; several associated axioms of this function

 

(defthm diag-endp-y
  (implies (and (lonp x) (lonp y) (endp y))
           (endp (diagonalize x y))))

 

(defthm diag-endp-x
  (implies (and (lonp x) (lonp y) (endp x))
           (and (endp (car (diagonalize x y)))
                (equal (len y) (len (diagonalize x y))))))

 

;; returns the sum of a lon
(definec flattenlon (l :lon) :nat
  (if (endp l)
      0
     (+ (car l) (flattenlon (cdr l)))))

 

(check= (flattenlon '()) 0)
(check= (flattenlon '(0 0)) 0)
(check= (flattenlon '(1 2 3 4 5)) 15)
(check= (flattenlon '(9 9 9)) 27)

 


;; FLATTENLON AXIOMS
;; several associated axioms of this function

 

(defthm flattenlon-axiom-1
  (implies (and (lonp x) (endp x))
           (zerop (flattenlon x))))

 

;; returns the sum of a lolon;;
(definec flattenlolon (l :lolon) :lon
  (if (endp l)
     '()
     (cons (flattenlon (car l)) (flattenlolon (cdr l)))))
(check= (flattenlolon (list '() '())) '(0 0))
(check= (flattenlolon (list '() '(1))) '(0 1))
(check= (flattenlolon (list '(1 2) '(1 2))) '(3 3))
(check= (flattenlolon (list '(0) '(10 10))) '(0 20))

 

;; FLATTENLOLON AXIOMS
;; several associated axioms of this function

 

(defthm flattenlolon-axiom-1
  (implies (and (lonp x) (endp x))
           (endp (flattenlolon x))))

 

(defthm ftll-axiom-2
  (implies (and (lonp x) (lonp y))
           (equal (list (flattenlon y) (flattenlon x)) (flattenlolon (list y x)))))
(defthm ftll-axiom-3
  (implies (and (endp x) (lolonp y) (lolonp z) (equal y z))
           (equal (flattenlolon (append-lon y x)) (flattenlolon (append-lon z x)))))

 

(defthm ftll-axiom-4
  (implies (and (endp x) (lolonp x) (lolonp z))
           (equal (flattenlolon (append-lon z (flattenlolon x))) (flattenlolon z))))

 

(defthm ftll-axiom-5
  (implies (and (lolonp y) (lolonp z) (lolonp x) (equal (flattenlolon z) (flattenlolon y)))
           (equal (list (flattenlon (car x)) (flattenlon (car y))) (list (flattenlon (car x)) (flattenlon (car z))))))

 


(defthm ftll-axiom-6
  (implies (and (lonp x) (not (endp x)) (endp (car y)) (endp (cdr y)) (consp y) (lolonp y))
         (equal (flattenlolon (append-lon y x)) x)))

 

(defthm flatten-append-axiom
  (implies (and (lonp x) (consp x))
           (equal (flattenlolon (append-lon '(NIL) x)) x)))

 

(defthm flatten-append-axiom-2
  (implies (and (lonp x) (consp x))
           (equal (flattenlolon (append-lon nil x)) x)))

(defthm flatten-append-axiom-3
  (implies (and (lolonp x) (lonp y) (natp z))
           (equal (list-to-num (flattenlolon (append-lon x y)) z)
                  (+ (list-to-num (flattenlolon (append-lon x nil)) z)
                     (list-to-num y z)))))
 


;; Distributive multiplication function
(definec distribute-mult (x :lon y :lon z :nat) :nat
  (if (endp y)
    0
    (+ (list-to-num (scale x (car y)) z)
       (* z (distribute-mult x (cdr y) z)))))

 

(defthm distr-mult-equiv
  (implies (and (lonp x) (lonp y) (natp z))
           (equal (distribute-mult x y z)
                  (normal-mult x y z))))

 


;; Japanese multiplication:
(definec jmult (n1 :lon n2 :lon base :nat) :nat
  (list-to-num (flattenlolon (diagonalize n1 n2))
               base))

 

(defthm jmult-equiv-endp
  (implies (and (lonp x) (lonp y) (natp z) (endp x))
           (equal (jmult x y z) (distribute-mult x y z))))

 

(defthm jmult-equiv-endp-y
  (implies (and (lonp x) (lonp y) (natp z) (endp y))
           (equal (jmult x y z) (distribute-mult x y z))))
          
(defthm subgoal-1.2.1 (IMPLIES
   (AND (NOT (EQUAL Z 0))
        (INTEGERP (CAR X))
        (<= 0 (CAR X))
        (NAT-LISTP (CDR X))
        (INTEGERP (CAR Y))
        (<= 0 (CAR Y))
        (CONSP X)
        (NOT (EQUAL (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE (CDR X) (CDR Y)))
                                 Z)
                    (* (LIST-TO-NUM (CDR X) Z)
                       (LIST-TO-NUM (CDR Y) Z))))
        (NAT-LISTP (CDR Y))
        (INTEGERP Z)
        (<= 0 Z)
        (CONSP Y)
        (EQUAL (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                            Z)
               (+ (* (CAR X) (LIST-TO-NUM (CDR Y) Z))
                  (* Z (LIST-TO-NUM (CDR X) Z)
                     (LIST-TO-NUM (CDR Y) Z))))
        Y)
   (EQUAL (LIST-TO-NUM (FLATTENLOLON (APPEND-LON (DIAGONALIZE X (CDR Y))
                                                 (SCALE (CDR X) (CAR Y))))
                       Z)
          (+ (* (CAR Y) (LIST-TO-NUM (CDR X) Z))
             (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                          Z)))))#|ACL2s-ToDo-Line|#


(defthm subgoal-1.2.2 (IMPLIES
 (AND
  (NOT (EQUAL Z 0))
  (INTEGERP (CAR X))
  (<= 0 (CAR X))
  (NAT-LISTP (CDR X))
  (INTEGERP (CAR Y))
  (<= 0 (CAR Y))
  (CONSP X)
  (EQUAL
      (LIST-TO-NUM
           (FLATTENLOLON (APPEND-LON (CONS NIL (DIAGONALIZE (CDR X) (CDR Y)))
                                     (SCALE (CDR X) (CAR Y))))
           Z)
      (+ (* (CAR Y) (LIST-TO-NUM (CDR X) Z))
         (* Z
            (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE (CDR X) (CDR Y)))
                         Z))))
  (NAT-LISTP (CDR Y))
  (INTEGERP Z)
  (<= 0 Z)
  (CONSP Y)
  (EQUAL (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                      Z)
         (+ (* (CAR X) (LIST-TO-NUM (CDR Y) Z))
            (* Z (LIST-TO-NUM (CDR X) Z)
               (LIST-TO-NUM (CDR Y) Z))))
  Y)
 (EQUAL (LIST-TO-NUM (FLATTENLOLON (APPEND-LON (DIAGONALIZE X (CDR Y))
                                               (SCALE (CDR X) (CAR Y))))
                     Z)
        (+ (* (CAR Y) (LIST-TO-NUM (CDR X) Z))
           (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                        Z)))))

(defthm subgoal-1.2
  (IMPLIES
 (AND (INTEGERP (CAR Y))
      (<= 0 (CAR Y))
      (NAT-LISTP (CDR Y))
      (INTEGERP Z)
      (<= 0 Z)
      (CONSP Y)
      (EQUAL (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                          Z)
             (* (LIST-TO-NUM X Z)
                (LIST-TO-NUM (CDR Y) Z)))
      (NAT-LISTP X)
      Y)
 (EQUAL
    (LIST-TO-NUM (FLATTENLOLON (APPEND-LON (CONS NIL (DIAGONALIZE X (CDR Y)))
                                           (SCALE X (CAR Y))))
                 Z)
    (+ (* (CAR Y) (LIST-TO-NUM X Z))
       (* Z
          (LIST-TO-NUM (FLATTENLOLON (DIAGONALIZE X (CDR Y)))
                       Z))))))

 


(defthm jmult-equiv-not-endp
  (implies (and (lonp x) (lonp y) (natp z) (not (endp x)))
           (equal (jmult x y z) (distribute-mult x y z))))

 

(defthm distr-jmult-equiv
  (implies (and (lonp x) (lonp y) (natp z))
           (equal (jmult x y z)
                  (distribute-mult x y z))))

 

(defthm jmult-equiv
  (implies (and (lonp x) (lonp y) (natp z))
           (equal (normal-mult x y z) 
                  (jmult x y z))))