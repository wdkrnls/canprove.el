;;; canprove-simplify-tests.el --- Tests for direct-pass simplification  -*- lexical-binding: t; -*-

;;; Commentary:

;; Tests for the Calc-free Boolean simplifier in `canprove'.
;;
;; Run with:
;;   emacs -batch -L . -l canprove-simplify-tests.el \
;;         -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'seq)
(require 'canprove)

;;; Helpers

(defun canprove-test--simp (f)
  "Simplify F with the direct pass."
  (can-prove-simplify-formula f))

(defun canprove-test--equiv (a b)
  "Non-nil if A and B are logically equivalent, per our own engine."
  (can-prove-tautology (list 'iff a b)))

(defun canprove-test--equivalent-p (a b)
  "Non-nil if the simplification of A is equivalent to B."
  (canprove-test--equiv (canprove-test--simp a) b))

;;; Constants

(ert-deftest canprove-simplify-constant-identity ()
  (should (equal (canprove-test--simp '(and p t)) 'p))
  (should (equal (canprove-test--simp '(and t p)) 'p))
  (should (equal (canprove-test--simp '(or p nil)) 'p))
  (should (equal (canprove-test--simp '(or nil p)) 'p)))

(ert-deftest canprove-simplify-constant-absorbing ()
  (should (eq (canprove-test--simp '(and p nil)) nil))
  (should (eq (canprove-test--simp '(and nil p)) nil))
  (should (eq (canprove-test--simp '(or p t)) t))
  (should (eq (canprove-test--simp '(or t p)) t)))

(ert-deftest canprove-simplify-bare-constants ()
  (should (eq (canprove-test--simp t) t))
  (should (eq (canprove-test--simp nil) nil)))

(ert-deftest canprove-simplify-nested-constants ()
  (should (equal (canprove-test--simp '(and (or p nil) t)) 'p))
  (should (eq (canprove-test--simp '(and (or p t) nil)) nil)))

;;; Idempotence

(ert-deftest canprove-simplify-idempotence-basic ()
  (should (equal (canprove-test--simp '(and p p)) 'p))
  (should (equal (canprove-test--simp '(or p p)) 'p)))

(ert-deftest canprove-simplify-idempotence-many ()
  (should (equal (canprove-test--simp '(and p p q)) '(and p q)))
  (should (equal (canprove-test--simp '(or p q p)) '(or p q)))
  (should (equal (canprove-test--simp '(and p q p q p)) '(and p q))))

;;; Complementarity

(ert-deftest canprove-simplify-complement-basic ()
  (should (eq (canprove-test--simp '(and p (not p))) nil))
  (should (eq (canprove-test--simp '(and (not p) p)) nil))
  (should (eq (canprove-test--simp '(or p (not p))) t))
  (should (eq (canprove-test--simp '(or (not p) p)) t)))

(ert-deftest canprove-simplify-complement-literal-in-nary ()
  (should (eq (canprove-test--simp '(and p q (not q))) nil))
  (should (eq (canprove-test--simp '(or p q (not q))) t))
  (should (eq (canprove-test--simp '(and p (not p) q r)) nil)))

(ert-deftest canprove-simplify-complement-compound-literal ()
  "Complementarity works when the negation is a literal match."
  (should (eq (canprove-test--simp '(and (or p q) (not (or p q)))) nil))
  (should (eq (canprove-test--simp '(or (and p q) (not (and p q)))) t)))

;;; Double negation

(ert-deftest canprove-simplify-double-negation ()
  (should (equal (canprove-test--simp '(not (not p))) 'p))
  (should (equal (canprove-test--simp '(not (not (not p)))) '(not p)))
  (should (eq (canprove-test--simp '(not (not t))) t))
  (should (eq (canprove-test--simp '(not (not nil))) nil)))

;;; Absorption

(ert-deftest canprove-simplify-absorption-and ()
  (should (equal (canprove-test--simp '(and p (or p q))) 'p))
  (should (equal (canprove-test--simp '(and (or p q) p)) 'p))
  (should (equal (canprove-test--simp '(and p q (or p q))) '(and p q))))

(ert-deftest canprove-simplify-absorption-or ()
  (should (equal (canprove-test--simp '(or p (and p q))) 'p))
  (should (equal (canprove-test--simp '(or (and p q) p)) 'p))
  (should (equal (canprove-test--simp '(or p q (and p q))) '(or p q))))

;;; Flattening, reassociation, commutativity

(ert-deftest canprove-simplify-reassociation ()
  (should (equal (canprove-test--simp '(and (and p q) r))
                 (canprove-test--simp '(and p (and q r)))))
  (should (equal (canprove-test--simp '(or (or p q) r))
                 (canprove-test--simp '(or p (or q r))))))

(ert-deftest canprove-simplify-commutativity ()
  (should (equal (canprove-test--simp '(and p q))
                 (canprove-test--simp '(and q p))))
  (should (equal (canprove-test--simp '(or p q))
                 (canprove-test--simp '(or q p)))))

(ert-deftest canprove-simplify-flatten-detects-complement ()
  (should (eq (canprove-test--simp '(and (and p q) (not p))) nil))
  (should (eq (canprove-test--simp '(or (or p q) (not q))) t)))

;;; De Morgan (opt-in)

(ert-deftest canprove-simplify-demorgan-off-by-default ()
  (should (equal (canprove-test--simp '(not (and p q))) '(not (and p q))))
  (should (equal (canprove-test--simp '(not (or p q))) '(not (or p q)))))

(ert-deftest canprove-simplify-demorgan-on ()
  (let ((can-prove-simplify-demorgan t))
    (should (equal (canprove-test--simp '(not (and p q)))
                   '(or (not p) (not q))))
    (should (equal (canprove-test--simp '(not (or p q)))
                   '(and (not p) (not q))))
    (should (equal (canprove-test--simp '(not (and (or p q) r)))
                   '(or (and (not p) (not q)) (not r))))))

;;; Equivalence invariant

(ert-deftest canprove-simplify-preserves-meaning ()
  "The simplification of F must be logically equivalent to F."
  (dolist (f '((and p q)
               (or p q)
               (not p)
               (and (or p q) r)
               (or (and p q) r)
               (and p p)
               (or p p)
               (and p (not p))
               (or p (not p))
               (and p t)
               (and p nil)
               (or p t)
               (or p nil)
               (implies p q)
               (iff p q)
               (xor p q)
               (and (or p q) (not (or p q)))
               (and p q (or p q))
               (implies (and p q) (or p q))))
    (should (canprove-test--equiv f (canprove-test--simp f)))))

;;; Pair version

(ert-deftest canprove-simplify-pair ()
  (let* ((s (can-prove-simplify '((and p p) (or q q)) '(and p q)))
         (premises (car s))
         (conclusion (cdr s)))
    (should (= (length premises) 2))
    (should (canprove-test--equiv (nth 0 premises) 'p))
    (should (canprove-test--equiv (nth 1 premises) 'q))
    (should (canprove-test--equiv conclusion '(and p q)))))

;;; Round trip: render then parse

(ert-deftest canprove-simplify-output-round-trips ()
  (dolist (f '((and p q)
               (or p (and q r))
               (not (and p q))
               (implies p q)
               (and p p (or p q))))
    (let* ((simp (canprove-test--simp f))
           (str  (can-prove--render simp)))
      (should (canprove-test--equiv simp (can-prove-parse str))))))

;;; Randomised equivalence

(defun canprove-test--random-norm (atoms depth)
  (if (or (<= depth 0) (< (random 100) 35))
      (if (zerop (random 8))
          (if (zerop (random 2)) t nil)
        (seq-random-elt atoms))
    (pcase (random 3)
      (0 (list 'not (canprove-test--random-norm atoms (1- depth))))
      (1 (list 'and (canprove-test--random-norm atoms (1- depth))
               (canprove-test--random-norm atoms (1- depth))))
      (_ (list 'or (canprove-test--random-norm atoms (1- depth))
               (canprove-test--random-norm atoms (1- depth)))))))

(ert-deftest canprove-simplify-random-equivalence ()
  (let ((atoms '(a b c)))
    (dotimes (_ 200)
      (let ((f (canprove-test--random-norm atoms 3)))
        (should (canprove-test--equiv f (canprove-test--simp f)))))))

;;; Known limitations (documented, not bugs)

(ert-deftest canprove-simplify-known-limitation-no-distribution ()
  "No distributivity: p AND (q OR r) stays put."
  (should (equal (canprove-test--simp '(and p (or q r)))
                 '(and (or q r) p))))  ; reordered by sort, not distributed

(ert-deftest canprove-simplify-known-limitation-compound-complement ()
  "Compound complementarity is not detected.
p AND q AND NOT(p AND q) is a contradiction, but the simplifier
only detects literal-level complements, so it survives."
  (let ((result (canprove-test--simp '(and p q (not (and p q))))))
    (should (canprove-test--equiv result '(and p q (not (and p q)))))
    ;; It is NOT reduced to nil.
    (should-not (null result))))

(provide 'canprove-simplify-tests)
;;; canprove-simplify-tests.el ends here
