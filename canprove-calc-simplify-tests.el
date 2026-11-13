;;; canprove-calc-tests.el --- Tests for the Calc-backed simplifier  -*- lexical-binding: t; -*-

;;; Commentary:

;; Tests for `canprove-calc', the optional Calc-backed reference
;; simplifier.  Three concerns:
;;
;;   1. the translation layer (pure; no Calc involved),
;;   2. the equivalence invariant (must always hold), and
;;   3. the known limits of Calc's simplifier (documented, not bugs).
;;
;; Run with:
;;   emacs -batch -L . -l canprove-calc-tests.el \
;;         -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'canprove)
(require 'canprove-calc)

(defun canprove-calc-test--equiv (a b)
  "Non-nil if A and B are logically equivalent, per our own engine."
  (can-prove-tautology (list 'iff a b)))

;;; Translation layer (pure; no Calc involved)

(ert-deftest canprove-calc-translation-basic ()
  (should (equal (can-prove-calc--to-calc '(and p q))  "(p) && (q)"))
  (should (equal (can-prove-calc--to-calc '(or p q))   "(p) || (q)"))
  (should (equal (can-prove-calc--to-calc '(not p))    "!(p)")))

(ert-deftest canprove-calc-translation-constants ()
  (should (equal (can-prove-calc--to-calc t)   "1"))
  (should (equal (can-prove-calc--to-calc nil) "0")))

(ert-deftest canprove-calc-translation-nested ()
  (should (equal (can-prove-calc--to-calc '(and (or p q) r))
                 "((p) || (q)) && (r)"))
  (should (equal (can-prove-calc--to-calc '(not (and p q)))
                 "!((p) && (q))")))

(ert-deftest canprove-calc-translation-rejects-non-normalized ()
  (should-error (can-prove-calc--to-calc '(implies p q)))
  (should-error (can-prove-calc--to-calc '(iff p q))))

(ert-deftest canprove-calc-translation-after-normalization ()
  (should (equal (can-prove-calc--to-calc
                  (can-prove--normalize '(implies p q)))
                 "(!(p)) || (q)")))

;;; Calc accepts our syntax and round-trips

(ert-deftest canprove-calc-accepts-syntax ()
  (dolist (s '("(p) && (q)" "(p) || (q)" "!(p)"
               "((p) || (q)) && (r)" "1" "0"))
    (let ((out (calc-eval s)))
      (should (stringp out))
      ;; Whatever Calc emits must re-parse in our notation.
      (should (condition-case nil
                  (progn (can-prove-parse out) t)
                (error nil))))))

;;; Constant folding (Calc does this)

(ert-deftest canprove-calc-constant-folding ()
  (should (eq (can-prove-calc-simplify-formula '(and p nil)) nil))
  (should (eq (can-prove-calc-simplify-formula '(or p t)) t))
  (should (equal (can-prove-calc-simplify-formula '(and p t)) 'p))
  (should (equal (can-prove-calc-simplify-formula '(or p nil)) 'p)))

;;; Equivalence invariant (must always hold)

(ert-deftest canprove-calc-preserves-meaning ()
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
    (should (canprove-calc-test--equiv f
                                       (can-prove-calc-simplify-formula f)))))

;;; Pair and comparison helpers

(ert-deftest canprove-calc-simplify-pair ()
  (let* ((s (can-prove-calc-simplify '((and p p)) '(or q q)))
         (premises (car s))
         (conclusion (cdr s)))
    (should (= (length premises) 1))
    (should (canprove-calc-test--equiv (nth 0 premises) 'p))
    (should (canprove-calc-test--equiv conclusion 'q))))

(ert-deftest canprove-calc-compare-returns-two ()
  (let ((r (can-prove-calc-compare '(and p p))))
    (should (= (length r) 2))
    (should (canprove-calc-test--equiv (nth 0 r) '(and p p)))
    (should (canprove-calc-test--equiv (nth 1 r) '(and p p)))))

(ert-deftest canprove-calc-compare-agrees-on-meaning ()
  "Both simplifiers must preserve meaning, even if they disagree on form."
  (dolist (f '((and p p) (or p (not p)) (and p (or p q)) (implies p q)))
    (let* ((r (can-prove-calc-compare f))
           (direct (nth 0 r))
           (calc   (nth 1 r)))
      (should (canprove-calc-test--equiv f direct))
      (should (canprove-calc-test--equiv f calc)))))

;;; Known limitations of Calc (documented; expected to fail)

(ert-deftest canprove-calc-known-limitation-idempotence ()
  "Calc does NOT simplify (and p p) to p.  Documented limitation."
  :expected-result :failed
  (should (equal (can-prove-calc-simplify-formula '(and p p)) 'p)))

(ert-deftest canprove-calc-known-limitation-complement ()
  "Calc does NOT simplify (and p (not p)) to nil.  Documented limitation."
  :expected-result :failed
  (should (null (can-prove-calc-simplify-formula '(and p (not p))))))

(ert-deftest canprove-calc-known-limitation-absorption ()
  "Calc does NOT simplify (and p (or p q)) to p.  Documented limitation."
  :expected-result :failed
  (should (equal (can-prove-calc-simplify-formula '(and p (or p q))) 'p)))

(provide 'canprove-calc-tests)
;;; canprove-calc-tests.el ends here