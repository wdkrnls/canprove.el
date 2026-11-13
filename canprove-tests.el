;;; can-prove-tests.el --- Tests for can-prove  -*- lexical-binding: t; -*-

;;; Commentary:

;; Run with:
;;   M-x ert-run-tests-interactively RET t
;; or:
;;   emacs -batch -L . -l can-prove-tests.el -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'seq)
(require 'can-prove)

;;; ---------------------------------------------------------------------
;;; Independent oracle (does NOT use the implementation)
;;; ---------------------------------------------------------------------

(defun can-prove-test--eval (f asg)
  "Evaluate F under ASG (a list of true atoms)."
  (cond
   ((eq f t) t)
   ((null f) nil)
   ((symbolp f) (and (memq f asg) t))
   (t (pcase (car f)
        ('not (not (can-prove-test--eval (nth 1 f) asg)))
        ('and (seq-every-p (lambda (x) (can-prove-test--eval x asg))
                           (cdr f)))
        ('or  (seq-some (lambda (x) (can-prove-test--eval x asg))
                        (cdr f)))
        ('implies (or (not (can-prove-test--eval (nth 1 f) asg))
                      (can-prove-test--eval (nth 2 f) asg)))
        ('iff (eq (and (can-prove-test--eval (nth 1 f) asg) t)
                  (and (can-prove-test--eval (nth 2 f) asg) t)))
        ('xor (not (eq (and (can-prove-test--eval (nth 1 f) asg) t)
                       (and (can-prove-test--eval (nth 2 f) asg) t))))))))

(defun can-prove-test--counterexample-p (premises conclusion ce)
  (and (seq-every-p (lambda (p) (can-prove-test--eval p ce)) premises)
       (not (can-prove-test--eval conclusion ce))))

(defun can-prove-test--bitp (k i)
  (not (zerop (logand (ash 1 k) i))))

(defun can-prove-test--all-assignments (atoms)
  (let ((n (length atoms)) (result nil))
    (dotimes (i (ash 1 n) (nreverse result))
      (let ((asg nil) (k 0))
        (dolist (a atoms)
          (when (can-prove-test--bitp k i) (push a asg))
          (setq k (1+ k)))
        (push asg result)))))

(defun can-prove-test--brute-valid-p (premises conclusion atoms)
  (seq-every-p
   (lambda (asg)
     (or (not (seq-every-p (lambda (p) (can-prove-test--eval p asg))
                           premises))
         (can-prove-test--eval conclusion asg)))
   (can-prove-test--all-assignments atoms)))

;;; ---------------------------------------------------------------------
;;; Run a check against BOTH backends
;;; ---------------------------------------------------------------------

(defun can-prove-test--both (premises conclusion)
  (list (let ((can-prove-bitvec-threshold 1000))
          (can-prove-counterexample premises conclusion))
        (let ((can-prove-bitvec-threshold -1))   ; force SAT
          (can-prove-counterexample premises conclusion))))

(defun can-prove-test--assert-valid (premises conclusion)
  (dolist (r (can-prove-test--both premises conclusion))
    (should (eq r :valid))))

(defun can-prove-test--assert-invalid (premises conclusion)
  (dolist (r (can-prove-test--both premises conclusion))
    (should-not (eq r :valid))
    (should (can-prove-test--counterexample-p premises conclusion r))))

;;; ---------------------------------------------------------------------
;;; Parser tests
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-parse-basic ()
  (should (equal (can-prove-parse "p and q")     '(and p q)))
  (should (equal (can-prove-parse "p -> q")      '(implies p q)))
  (should (equal (can-prove-parse "p implies q") '(implies p q)))
  (should (equal (can-prove-parse "not p")       '(not p)))
  (should (equal (can-prove-parse "-p")          '(not p)))  
  (should (equal (can-prove-parse "p && q")      '(and p q)))
  (should (equal (can-prove-parse "p || q")      '(or p q))))

(ert-deftest can-prove-parse-precedence ()
  (should (equal (can-prove-parse "p or q and r")     '(or p (and q r))))
  (should (equal (can-prove-parse "p and q or r")     '(or (and p q) r)))
  (should (equal (can-prove-parse "not p and q")      '(and (not p) q)))
  (should (equal (can-prove-parse "(p or q) and r")   '(and (or p q) r))))

(ert-deftest can-prove-parse-assoc ()
  (should (equal (can-prove-parse "p -> q -> r")   '(implies p (implies q r))))
  (should (equal (can-prove-parse "p -> (q -> r)") '(implies p (implies q r))))
  (should (equal (can-prove-parse "(p -> q) -> r") '(implies (implies p q) r))))

(ert-deftest can-prove-parse-unicode ()
  (should (equal (can-prove-parse "p → q") '(implies p q)))
  (should (equal (can-prove-parse "p ∧ q") '(and p q)))
  (should (equal (can-prove-parse "p ∨ q") '(or p q)))
  (should (equal (can-prove-parse "¬p")    '(not p))))

(ert-deftest can-prove-parse-jaynes-operators ()
  (should (equal (can-prove-parse "p + q")     '(or p q)))
  (should (equal (can-prove-parse "p * q")     '(and p q)))
  (should (equal (can-prove-parse "p * q + r") '(or (and p q) r)))
  (should (equal (can-prove-parse "p + q * r") '(or p (and q r)))))

(ert-deftest can-prove-parse-juxtaposition ()
  (should (equal (can-prove-parse "p q")   '(and p q)))
  (should (equal (can-prove-parse "p q r") '(and (and p q) r)))
  (should (equal (can-prove-parse "¬p q")  '(and (not p) q)))
  (should (equal (can-prove-parse "p ¬q")  '(and p (not q)))))

(ert-deftest can-prove-parse-jaynes-mix ()
  (should (equal (can-prove-parse "p + q ≡ ¬(¬p * ¬q)")
                 '(iff (or p q) (not (and (not p) (not q)))))))

(ert-deftest can-prove-parse-dash-negation ()
  (should (equal (can-prove-parse "p * -q")  '(and p (not q))))
  (should (equal (can-prove-parse "-p + q")  '(or (not p) q)))
  (should (equal (can-prove-parse "p -> -q") '(implies p (not q)))))

(ert-deftest can-prove-parse-boolean-literals ()
  (should (eq (can-prove-parse "T") t))
  (should (eq (can-prove-parse "F") nil))
  (should (eq (can-prove-parse "1") t))
  (should (eq (can-prove-parse "0") nil))
  (should (equal (can-prove-parse "T * p") '(and t p))))

(ert-deftest can-prove-boolean-literal-arguments ()
  (should (eq (can-prove-string "T + ¬T") :valid))
  (should (equal (can-prove-string "F") '()))
  (should (eq (can-prove-argument "p -> q. p. F. therefore q.") :valid)))

;;; ---------------------------------------------------------------------
;;; Validity tests (both backends)
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-modus-ponens ()
  (can-prove-test--assert-valid '((implies p q) p) 'q))

(ert-deftest can-prove-modus-tollens ()
  (can-prove-test--assert-valid '((implies p q) (not q)) '(not p)))

(ert-deftest can-prove-disjunctive-syllogism ()
  (can-prove-test--assert-valid '((or p q) (not p)) 'q))

(ert-deftest can-prove-hypothetical-syllogism ()
  (can-prove-test--assert-valid '((implies p q) (implies q r)) '(implies p r)))

(ert-deftest can-prove-excluded-middle ()
  (can-prove-test--assert-valid nil '(or p (not p))))

(ert-deftest can-prove-de-morgan ()
  (can-prove-test--assert-valid
   nil '(iff (not (and p q)) (or (not p) (not q)))))

(ert-deftest can-prove-affirming-consequent ()
  (can-prove-test--assert-invalid '((implies p q) q) 'p))

(ert-deftest can-prove-denying-antecedent ()
  (can-prove-test--assert-invalid '((implies p q) (not p)) '(not q)))

;;; ---------------------------------------------------------------------
;;; Counterexample exactness (this catches the bit-vector bug)
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-counterexample-exact ()
  ;; (p -> q) ⊢ q : unique counterexample p=0, q=0  =>  ()
  (should (equal (can-prove-counterexample '((implies p q)) 'q) '()))
  ;; ⊢ p : counterexample p=f  =>  ()
  (should (equal (can-prove-counterexample nil 'p) '()))
  ;; (p -> q), q ⊢ p : unique counterexample p=0, q=1  =>  (q)
  (should (equal (sort (can-prove-counterexample '((implies p q) q) 'p)
                       #'string<)
                 '(q))))

;;; ---------------------------------------------------------------------
;;; String API
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-string-tests ()
  (should (eq (can-prove-string "p or not p") :valid))
  (should (eq (can-prove-string "p -> p")     :valid))
  (should (equal (can-prove-string "p") '())))

(ert-deftest can-prove-string-jaynes ()
  (should (eq (can-prove-string "p + ¬p") :valid))
  (should (eq (can-prove-string "¬(p * q) ≡ (¬p + ¬q)") :valid))
  (should (equal (can-prove-string "p * q") '())))

(ert-deftest can-prove-argument-tests ()
  (should (eq (can-prove-argument "p -> q, p |- q") :valid))
  (should (eq (can-prove-argument "p ∨ q; ¬p ⊢ q") :valid))
  (should (equal (sort (can-prove-argument "p -> q, q |- p") #'string<)
                 '(q))))

(ert-deftest can-prove-argument-periods ()
  (should (eq (can-prove-argument "p => q. p. therefore q.") :valid))
  (should (eq (can-prove-argument "p + q. ¬p. therefore q.") :valid)))

(ert-deftest can-prove-argument-periods-invalid ()
  (should (equal (sort (can-prove-argument "p => q. q. therefore p.") #'string<)
                 '(q))))

(ert-deftest can-prove-argument-jaynes ()
  (should (eq (can-prove-argument "p -> q, p |- q") :valid))
  (should (eq (can-prove-argument "p + q, ¬p ⊢ q") :valid))
  (should (eq (can-prove-argument "(p ⊃ q) * (q ⊃ r) |- p ⊃ r") :valid))
  (should (equal (sort (can-prove-argument "p ⊃ q, q |- p") #'string<)
                 '(q))))

(ert-deftest can-prove-argument-dash ()
  (should (eq (can-prove-argument "p -> q. p. therefore q.") :valid))
  (should (eq (can-prove-argument "p + q. -p. therefore q.") :valid))
  ;; p * -q ⊢ -p * -q is invalid: p=t, q=f satisfies the premise but not
  ;; the conclusion, so the unique counterexample is (p).
  (should (equal (can-prove-argument "p * -q. therefore -p * -q.") '(p))))

;;; ---------------------------------------------------------------------
;;; Renderer
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-render-tests ()
  (should (equal (can-prove--render '(and p (not q)))           "p and not q"))
  (should (equal (can-prove--render '(or p (and q r)))          "p or q and r"))
  (should (equal (can-prove--render '(and (or p q) r))          "(p or q) and r"))
  (should (equal (can-prove--render '(not (and p q)))           "not (p and q)"))
  (should (equal (can-prove--render '(implies p (implies q r))) "p implies q implies r"))
  (should (equal (can-prove--render '(implies (implies p q) r)) "(p implies q) implies r")))

;;; ---------------------------------------------------------------------
;;; Explanation
;;; ---------------------------------------------------------------------

(ert-deftest can-prove-explain-tests ()
  (should (string-match-p "Valid"
                          (can-prove-explain '((implies p q) p) 'q)))
  (let ((s (can-prove-explain '((implies p q)) 'q)))
    (should (string-match-p "Invalid" s))
    (should (string-match-p "p=0" s))
    (should (string-match-p "q=0" s))))

(ert-deftest can-prove-explain-echo ()
  (let ((s (can-prove-explain '((implies p q) p) 'q)))
    (should (string-match-p "p implies q. p. therefore q." s))
    (should (string-match-p "Valid" s)))
  (should (string-match-p "q=1"
                          (can-prove-explain '((implies p q) q) 'p))))

(ert-deftest can-prove-explain-argument-tests ()
  (should (string-match-p
           "Valid"
           (can-prove-explain-argument "p => q. p. therefore q.")))
  (should (string-match-p
           "q=1"
           (can-prove-explain-argument "p => q. q. therefore p."))))

;;; ---------------------------------------------------------------------
;;; Randomized property test: both backends vs. the oracle
;;; ---------------------------------------------------------------------

(defun can-prove-test--random-formula (atoms depth)
  (if (or (<= depth 0) (< (random 100) 30))
      (if (zerop (random 6))
          (if (zerop (random 2)) t nil)
        (seq-random-elt atoms))
    (pcase (random 5)
      (0 (list 'not (can-prove-test--random-formula atoms (1- depth))))
      (1 (list 'and (can-prove-test--random-formula atoms (1- depth))
               (can-prove-test--random-formula atoms (1- depth))))
      (2 (list 'or (can-prove-test--random-formula atoms (1- depth))
               (can-prove-test--random-formula atoms (1- depth))))
      (3 (list 'implies (can-prove-test--random-formula atoms (1- depth))
               (can-prove-test--random-formula atoms (1- depth))))
      (4 (list 'iff (can-prove-test--random-formula atoms (1- depth))
               (can-prove-test--random-formula atoms (1- depth)))))))

(ert-deftest can-prove-random-agreement ()
  (let ((atoms '(a b c)))
    (dotimes (_ 200)
      (let* ((premises (list (can-prove-test--random-formula atoms 3)))
             (conclusion (can-prove-test--random-formula atoms 3))
             (bv (let ((can-prove-bitvec-threshold 1000))
                   (can-prove-counterexample premises conclusion)))
             (sat (let ((can-prove-bitvec-threshold -1))
                    (can-prove-counterexample premises conclusion))))
        ;; Both backends agree on validity.
        (should (eq (eq bv :valid) (eq sat :valid)))
        ;; Any counterexample they report is genuine.
        (unless (eq bv :valid)
          (should (can-prove-test--counterexample-p premises conclusion bv)))
        (unless (eq sat :valid)
          (should (can-prove-test--counterexample-p premises conclusion sat)))
        ;; Validity agrees with brute force over all assignments.
        (should (eq (eq bv :valid)
                    (can-prove-test--brute-valid-p premises conclusion atoms)))
        (should (eq (eq sat :valid)
                    (can-prove-test--brute-valid-p premises conclusion atoms)))))))

(provide 'can-prove-tests)
;;; can-prove-tests.el ends here
