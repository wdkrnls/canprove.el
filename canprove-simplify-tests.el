;;; can-prove-simplify-tests.el --- Tests for Calc simplification  -*- lexical-binding: t; -*-

(require 'ert)
(require 'calc)
(require 'can-prove)

;;; ---------------------------------------------------------------------
;;; 1. Translation layer (pure; no Calc involved)
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-to-calc-translation ()
  (should (equal (can-prove--to-calc '(and p q))        "(p) && (q)"))
  (should (equal (can-prove--to-calc '(or p q))         "(p) || (q)"))
  (should (equal (can-prove--to-calc '(not p))          "!(p)"))
  (should (equal (can-prove--to-calc '(and (or p q) r)) "((p) || (q)) && (r)"))
  (should (equal (can-prove--to-calc t)                 "1"))
  (should (equal (can-prove--to-calc nil)               "0")))

(ert-deftest can-prove-to-calc-normalized-only ()
  "Translation is only defined on normalized (and/or/not) formulas."
  (should-error (can-prove--to-calc '(implies p q)))
  (should (equal (can-prove--to-calc (can-prove--normalize '(implies p q)))
                 "(!(p)) || (q)")))

;;; ---------------------------------------------------------------------
;;; 2. Probe: does Calc accept our syntax and round-trip?
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-calc-accepts-our-syntax ()
  (dolist (s '("(p) && (q)" "(p) || (q)" "!(p)"
               "((p) || (q)) && (r)" "1" "0"))
    (let ((out (calc-eval s)))
      (should (stringp out))
      ;; Whatever Calc emits must re-parse in our notation.
      (should
       (condition-case nil
           (progn (can-prove-parse out) t)
         (error nil))))))

(ert-deftest can-prove-calc-simplifies-constants ()
  "Constant folding: Calc must reduce these on its own."
  (should (equal (calc-eval "(p) && (0)") "0"))
  (should (equal (calc-eval "(p) || (1)") "1"))
  (should (equal (calc-eval "(p) && (1)") "p"))
  (should (equal (calc-eval "(p) || (0)") "p")))

;;; ---------------------------------------------------------------------
;;; 3. Equivalence invariant (the important one)
;;; ---------------------------------------------------------------------

(defun can-prove-test--equiv (a b)
  "Non-nil if A and B are logically equivalent, per our own engine."
  (can-prove-tautology (list 'iff a b)))

(ert-deftest can-prove-simplify-preserves-meaning ()
  "Simplification must never change the meaning of a formula."
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
               (xor p q)))
    (should (can-prove-test--equiv f (can-prove-simplify-formula f)))))

;;; ---------------------------------------------------------------------
;;; 4. Strength tests — how much does Calc actually reduce?
;;;    These may fail if `simplify' is not taking effect; that is the
;;;    whole point of including them.
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-simplify-idempotence ()
  (should (equal (can-prove-simplify-formula '(and p p)) 'p))
  (should (equal (can-prove-simplify-formula '(or p p))  'p)))

(ert-deftest can-prove-simplify-constants ()
  (should (equal (can-prove-simplify-formula '(and p t)) 'p))
  (should (equal (can-prove-simplify-formula '(or p nil)) 'p))
  (should (eq    (can-prove-simplify-formula '(or p t))  t))
  (should (null  (can-prove-simplify-formula '(and p nil)))))

(ert-deftest can-prove-simplify-contradiction ()
  (should (null (can-prove-simplify-formula '(and p (not p)))))
  (should (eq   (can-prove-simplify-formula '(or p (not p))) t)))

;;; ---------------------------------------------------------------------
;;; 5. Pair version and re-parseability
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-simplify-pair ()
  (let* ((s (can-prove-simplify '((and p p) (or q q)) '(and p q)))
         (premises (car s))
         (conclusion (cdr s)))
    (should (can-prove-test--equiv (nth 0 premises) 'p))
    (should (can-prove-test--equiv (nth 1 premises) 'q))
    (should (can-prove-test--equiv conclusion '(and p q)))
    (should (can-prove-test--equiv (car (car s)) 'p))
    (should (can-prove-test--equiv (car (cdr s)) 'q))
    (should (can-prove-test--equiv (cdr s) '(and p q)))))

(ert-deftest can-prove-simplify-output-reparses ()
  "Rendering the simplified formula and re-parsing must be equivalent."
  (dolist (f '((and p q) (or p (and q r)) (not (and p q)) (implies p q)))
    (let* ((simp (can-prove-simplify-formula f))
           (str  (can-prove--render simp)))
      (should (can-prove-test--equiv simp (can-prove-parse str))))))

(provide 'can-prove-simplify-tests)
