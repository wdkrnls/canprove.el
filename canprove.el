;;; canprove.el --- Propositional validity checker  -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Kyle Andrews

;; Author: Kyle Andrews <kyle.c.andrews@gmail.com>
;; Maintainer: Kyle Andrews <kyle.c.andrews@gmail.com>
;; URL: https://github.com/wdkrnls/canprove.el
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1") (seq "2.20"))
;; Keywords: convenience tools lisp

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;;; Commentary:

;; A propositional-logic checker with two interchangeable strategies
;; behind one API:
;;
;;   * a bit-vector truth-table evaluator (fast for <= ~20 atoms), and
;;   * a Tseitin + memoized DPLL SAT backend (scales further).
;;
;; Includes a friendly infix parser (Jaynes-style `+' for OR and `*'
;; for AND, ASCII and Unicode operators, `.'/`,'-separated premises),
;; an explainer that renders counterexamples, and no dependency on
;; cl-lib (seq.el only).
;;
;; Quick start:
;;
;;   (can-prove '((implies p q) p) 'q)              ; => t
;;   (can-prove-argument "p => q. p. therefore q.") ; => :valid
;;   (can-prove-explain-argument "p then q. q. therefore p.")
;;
;; See the README for notation and the full API.

;;; Change Log:

;; 0.1.0  2026-11-13  Initial release.

;;; Code:

(require 'seq)
(require 'subr-x)                       ; string-trim-right
(require 'calc)                         ; simplify

;;; ---------------------------------------------------------------------
;;; Normalization
;;; ---------------------------------------------------------------------

(defun can-prove--normalize (f)
  "Rewrite IMPLIES/IFF/XOR in F into AND/OR/NOT."
  (if (atom f)
      f
    (let ((args (mapcar #'can-prove--normalize (cdr f))))
      (pcase (car f)
        ('implies `(or (not ,(nth 0 args)) ,(nth 1 args)))
        ('iff `(or (and ,(nth 0 args) ,(nth 1 args))
                   (and (not ,(nth 0 args)) (not ,(nth 1 args)))))
        ('xor `(and (or ,(nth 0 args) ,(nth 1 args))
                    (not (and ,(nth 0 args) ,(nth 1 args)))))
        ((or 'and 'or) (cons (car f) args))
        ('not (list 'not (car args)))
        (_ (error "Unknown connective: %s" (car f)))))))

(defun can-prove--atoms (f &optional acc)
  "Return the atoms of F (order of first appearance, reversed)."
  (cond ((or (eq f t) (null f)) acc)
        ((symbolp f) (if (memq f acc) acc (cons f acc)))
        (t (let ((acc acc))
             (dolist (x (cdr f) acc)
               (setq acc (can-prove--atoms x acc)))))))

;;; ---------------------------------------------------------------------
;;; Bit-vector truth-table strategy
;;; ---------------------------------------------------------------------

(defun can-prove--logbitp (index num)
  "Non-nil if bit INDEX of NUM is set."
  (/= 0 (logand (ash 1 index) num)))

(defun can-prove--atom-mask (k n)
  "Bitmask over 2^N assignments where atom K is true."
  (let ((mask 0))
    (dotimes (j (ash 1 n) mask)
      (when (can-prove--logbitp k j)
        (setq mask (logior mask (ash 1 j)))))))

(defun can-prove--eval (f env full)
  "Evaluate F to a bitmask under ENV (alist atom . mask).  FULL is all-ones."
  (cond ((eq f t) full)
        ((null f) 0)
        ((symbolp f) (or (cdr (assq f env)) (error "Unbound atom: %s" f)))
        (t (pcase (car f)
             ('not (logand (lognot (can-prove--eval (cadr f) env full)) full))
             ('and (seq-reduce (lambda (a x)
                                 (logand a (can-prove--eval x env full)))
                               (cdr f) full))
             ('or  (seq-reduce (lambda (a x)
                                 (logior a (can-prove--eval x env full)))
                               (cdr f) 0))))))

(defun can-prove--table (formula)
  "Return (MASK . ATOMS) for FORMULA's truth table."
  (let* ((atoms (can-prove--atoms formula))
         (n (length atoms))
         (full (1- (ash 1 (ash 1 n))))
         (env nil)
         (k 0))
    (dolist (a atoms)
      (push (cons a (can-prove--atom-mask k n)) env)
      (setq k (1+ k)))
    (cons (can-prove--eval formula (nreverse env) full) atoms)))

(defun can-prove--counterexample-bitvec (formula)
  "Return :valid, or a list of atoms true in a falsifying assignment."
  (let* ((tbl (can-prove--table formula))
         (mask (car tbl))
         (atoms (cdr tbl)))
    (if (zerop mask)
        :valid
      (let ((j 0)
            (limit (ash 1 (length atoms))))
        ;; Find the first assignment that SATISFIES the refutation formula.
        (while (and (< j limit) (not (can-prove--logbitp j mask)))
          (setq j (1+ j)))
        (let ((result nil) (k 0))
          (dolist (a atoms (nreverse result))
            (when (can-prove--logbitp k j) (push a result))
            (setq k (1+ k))))))))

;;; ---------------------------------------------------------------------
;;; Tseitin + memoized DPLL strategy
;;; ---------------------------------------------------------------------

(defvar can-prove--var-counter 0)
(defvar can-prove--atom-vars nil)
(defvar can-prove--sat-memo nil)

(defun can-prove--fresh ()
  (setq can-prove--var-counter (1+ can-prove--var-counter))
  can-prove--var-counter)

(defun can-prove--tseitin (f)
  "Return (LIT . CLAUSES) for normalized formula F."
  (cond
   ((eq f t)
    (let ((v (can-prove--fresh))) (cons v (list (list v)))))
   ((null f)
    (let ((v (can-prove--fresh))) (cons v (list (list (- v))))))
   ((symbolp f)
    (cons (or (cdr (assq f can-prove--atom-vars))
              (let ((new (can-prove--fresh)))
                (push (cons f new) can-prove--atom-vars)
                new))
          nil))
   (t
    (pcase (car f)
      ('not
       (let* ((sub (can-prove--tseitin (cadr f)))
              (a (car sub))
              (v (can-prove--fresh)))
         (cons v (append (cdr sub)
                         (list (list v a) (list (- v) (- a)))))))
      ((or 'and 'or)
       (let* ((subs (mapcar #'can-prove--tseitin (cdr f)))
              (lits (mapcar #'car subs))
              (clauses (apply #'append (mapcar #'cdr subs)))
              (v (can-prove--fresh)))
         (pcase (car f)
           ('and
            (dolist (l lits) (push (list (- v) l) clauses))
            (push (cons v (mapcar (lambda (l) (- l)) lits)) clauses))
           ('or
            (dolist (l lits) (push (list v (- l)) clauses))
            (push (cons (- v) lits) clauses)))
         (cons v clauses)))))))

(defun can-prove--remove-lit (lit clause)
  (let ((result nil))
    (dolist (x clause (nreverse result))
      (unless (equal x lit) (push x result)))))

(defun can-prove--assign (clauses lit)
  "Simplify CLAUSES with LIT true; return :conflict on contradiction."
  (let ((result nil) (conflict nil))
    (dolist (c clauses)
      (cond
       ((memq lit c) nil)
       ((memq (- lit) c)
        (let ((c2 (can-prove--remove-lit (- lit) c)))
          (if (null c2) (setq conflict t) (push c2 result))))
       (t (push c result))))
    (if conflict :conflict (nreverse result))))

(defun can-prove--unit-propagate (clauses)
  "Propagate unit clauses.  Return (CLAUSES . MODEL) or :conflict."
  (catch 'done
    (let ((clauses clauses) (model nil))
      (while t
        (let ((unit nil))
          (dolist (c clauses)
            (when (and (= (length c) 1) (not unit))
              (setq unit (car c))))
          (unless unit (throw 'done (cons clauses model)))
          (let ((next (can-prove--assign clauses unit)))
            (if (eq next :conflict)
                (throw 'done :conflict)
              (setq clauses next)
              (setq model (cons unit model)))))))))

(defun can-prove--clause-key (clauses)
  "Canonical string key for CLAUSES."
  (let ((parts nil))
    (dolist (c clauses)
      (push (mapconcat #'number-to-string (sort (copy-sequence c) #'<) ",")
            parts))
    (mapconcat #'identity (sort parts #'string<) ";")))

(defun can-prove--dpll (clauses)
  "Return :unsat, or a list of literals satisfying CLAUSES."
  (let* ((key (can-prove--clause-key clauses))
         (cached (gethash key can-prove--sat-memo 'miss)))
    (if (not (eq cached 'miss))
        cached
      (let ((result (can-prove--dpll-1 clauses)))
        (puthash key result can-prove--sat-memo)
        result))))

(defun can-prove--dpll-1 (clauses)
  (let ((p (can-prove--unit-propagate clauses)))
    (cond
     ((eq p :conflict) :unsat)
     ((null (car p)) (cdr p))           ; all satisfied; model = units
     (t (can-prove--dpll-branch (car p) (cdr p))))))

(defun can-prove--dpll-branch (residual unit-model)
  (let* ((lit (caar residual))
         (pos (can-prove--assign residual lit))
         (sub (if (eq pos :conflict) :unsat (can-prove--dpll pos))))
    (if (not (eq sub :unsat))
        (append (cons lit sub) unit-model)
      (let* ((neg (can-prove--assign residual (- lit)))
             (sub2 (if (eq neg :conflict) :unsat (can-prove--dpll neg))))
        (if (eq sub2 :unsat)
            :unsat
          (append (cons (- lit) sub2) unit-model))))))

(defun can-prove--model-atoms (model)
  "Atoms assigned true in MODEL (a list of literals)."
  (let ((result nil))
    (dolist (pair can-prove--atom-vars (nreverse result))
      (when (memq (cdr pair) model)
        (push (car pair) result)))))

(defun can-prove--counterexample-sat (formula)
  "Return :valid, or a counterexample for FORMULA via memoized DPLL."
  (let ((can-prove--var-counter 0)
        (can-prove--atom-vars nil)
        (can-prove--sat-memo (make-hash-table :test 'equal)))
    (let* ((res (can-prove--tseitin formula))
           (clauses (cons (list (car res)) (cdr res)))
           (model (can-prove--dpll clauses)))
      (if (eq model :unsat)
          :valid
        (can-prove--model-atoms model)))))

;;; ---------------------------------------------------------------------
;;; Dispatcher
;;; ---------------------------------------------------------------------

(defcustom can-prove-bitvec-threshold 20
  "Max atom count before switching from bit-vector to SAT."
  :type 'integer
  :group 'can-prove)

(defun can-prove-counterexample (premises conclusion)
  "Return :valid if PREMISES entail CONCLUSION.
Otherwise return a list of atoms true in a falsifying assignment
(the empty list means \"all atoms false\")."
  (let* ((formula (can-prove--normalize
                   `(and ,@premises (not ,conclusion))))
         (n (length (can-prove--atoms formula))))
    (if (<= n can-prove-bitvec-threshold)
        (can-prove--counterexample-bitvec formula)
      (can-prove--counterexample-sat formula))))

(defun can-prove-counterexample-bits (premises conclusion)
  "Return :valid, or an alist of (atom . 0/1) for all atoms."
  (let ((ce (can-prove-counterexample premises conclusion)))
    (unless (eq ce :valid)
      (let ((formula (can-prove--normalize `(and ,@premises (not ,conclusion)))))
        (mapcar (lambda (a) (cons a (if (memq a ce) 1 0)))
                (sort (can-prove--atoms formula)
                      (lambda (a b) (string< (symbol-name a) (symbol-name b)))))))))

(defun can-prove (premises conclusion)
  "Non-nil if PREMISES entail CONCLUSION."
  (eq :valid (can-prove-counterexample premises conclusion)))

(defun can-prove-tautology (formula)
  "Non-nil if FORMULA is a tautology."
  (can-prove nil formula))

;;; ---------------------------------------------------------------------
;;; Infix parser
;;; ---------------------------------------------------------------------

(defconst can-prove--operators
  '(("<=>" . iff) ("<->" . iff) ("↔" . iff) ("≡" . iff)
    ("=>" . implies) ("->" . implies) ("→" . implies) ("⊃" . implies)
    ("&&" . and) ("/\\" . and) ("∧" . and) ("&" . and) ("*" . and)
    ("||" . or)  ("\\/" . or)  ("∨" . or)  ("|" . or)  ("+" . or)
    ("~" . not) ("!" . not) ("¬" . not)
    ("-" . not))                        ; last, so "->" wins first
  "Operator spellings, longest/most-specific first.")

(defun can-prove--tokenize (str)
  "Tokenize STR into operators (symbols) and atoms (strings)."
  (let ((i 0) (n (length str)) (tokens nil))
    (while (< i n)
      (let ((c (aref str i)))
        (cond
         ((memq c '(?\s ?\t ?\n ?\r)) (setq i (1+ i)))
         ((= c ?\() (push 'lparen tokens) (setq i (1+ i)))
         ((= c ?\)) (push 'rparen tokens) (setq i (1+ i)))
         ((or (and (>= c ?a) (<= c ?z))
              (and (>= c ?A) (<= c ?Z))
              (= c ?_)
              (and (>= c ?0) (<= c ?9)))
          (let ((j i))
            (while (and (< j n)
                        (let ((d (aref str j)))
                          (or (and (>= d ?a) (<= d ?z))
                              (and (>= d ?A) (<= d ?Z))
                              (and (>= d ?0) (<= d ?9))
                              (= d ?_))))
              (setq j (1+ j)))
            (let ((word (downcase (substring str i j))))
              (push (cond ((member word '("and")) 'and)
                          ((member word '("or")) 'or)
                          ((member word '("not")) 'not)
                          ((member word '("implies" "imp" "then")) 'implies)
                          ((member word '("iff" "equiv" "equivalent")) 'iff)
                          ((member word '("xor")) 'xor)
                          (t word))
                    tokens))
            (setq i j)))
         (t
          (let ((matched nil))
            (dolist (op can-prove--operators)
              (unless matched
                (let* ((s (car op)) (len (length s)))
                  (when (and (<= (+ i len) n)
                             (string= s (substring str i (+ i len))))
                    (push (cdr op) tokens)
                    (setq i (+ i len))
                    (setq matched t)))))
            (unless matched
              (error "Unexpected character %S at position %d" c i)))))))
    (nreverse tokens)))

;; Recursive descent; each returns (EXPR . REST).

(defun can-prove--p-iff (tokens)
  (let* ((l (can-prove--p-implies tokens))
         (e (car l))
         (r (cdr l)))
    (while (eq (car r) 'iff)
      (let ((rhs (can-prove--p-implies (cdr r))))
        (setq e (list 'iff e (car rhs))
              r (cdr rhs))))
    (cons e r)))

(defun can-prove--p-implies (tokens)
  (let* ((l (can-prove--p-or tokens))
         (e (car l))
         (r (cdr l)))
    (if (eq (car r) 'implies)
        (let ((rhs (can-prove--p-implies (cdr r))))
          (cons (list 'implies e (car rhs)) (cdr rhs)))
      (cons e r))))

(defun can-prove--p-or (tokens)
  (let* ((l (can-prove--p-and tokens))
         (e (car l))
         (r (cdr l)))
    (while (memq (car r) '(or xor))
      (let ((op (car r))
            (rhs (can-prove--p-and (cdr r))))
        (setq e (list op e (car rhs))
              r (cdr rhs))))
    (cons e r)))

(defun can-prove--starts-term-p (tokens)
  "Non-nil if TOKENS begins a term (for implicit conjunction)."
  (let ((tok (car tokens)))
    (or (eq tok 'lparen) (eq tok 'not) (stringp tok))))

(defun can-prove--p-and (tokens)
  (let* ((l (can-prove--p-not tokens))
         (e (car l))
         (r (cdr l)))
    (while (or (eq (car r) 'and) (can-prove--starts-term-p r))
      (let* ((toks (if (eq (car r) 'and) (cdr r) r))
             (rhs (can-prove--p-not toks)))
        (setq e (list 'and e (car rhs))
              r (cdr rhs))))
    (cons e r)))

(defun can-prove--p-not (tokens)
  (if (eq (car tokens) 'not)
      (let ((s (can-prove--p-not (cdr tokens))))
        (cons (list 'not (car s)) (cdr s)))
    (can-prove--p-atom tokens)))

(defun can-prove--p-atom (tokens)
  (cond
   ((null tokens) (error "Unexpected end of input"))
   ((eq (car tokens) 'lparen)
    (let ((s (can-prove--p-iff (cdr tokens))))
      (unless (and (consp (cdr s)) (eq (car (cdr s)) 'rparen))
        (error "Expected ')'"))
      (cons (car s) (cdr (cdr s)))))
   ((symbolp (car tokens)) (error "Unexpected operator: %s" (car tokens)))
   (t (let ((tok (car tokens)))
        (cond ((member tok '("true" "t" "1"))  (cons t (cdr tokens)))
              ((member tok '("false" "f" "0")) (cons nil (cdr tokens)))
              ((string-match-p "\\`[0-9]+\\'" tok)
               (error "Unknown numeric literal: %s" tok))
              (t (cons (intern tok) (cdr tokens))))))))

(defun can-prove--p-atom (tokens)
  (cond
   ((null tokens) (error "Unexpected end of input"))
   ((eq (car tokens) 'lparen)
    (let ((s (can-prove--p-iff (cdr tokens))))
      (unless (and (consp (cdr s)) (eq (car (cdr s)) 'rparen))
        (error "Expected ')'"))
      (cons (car s) (cdr (cdr s)))))
   ((symbolp (car tokens)) (error "Unexpected operator: %s" (car tokens)))
   (t (let ((tok (car tokens)))
        (cond ((member tok '("true" "t" "1"))  (cons t (cdr tokens)))
              ((member tok '("false" "f" "0" "nil")) (cons nil (cdr tokens)))
              ((string-match-p "\\`[0-9]+\\'" tok)
               (error "Unknown numeric literal: %s" tok))
              (t (cons (intern tok) (cdr tokens))))))))

(defun can-prove-parse (str)
  "Parse STR (infix notation) into an S-expression."
  (let ((res (can-prove--p-iff (can-prove--tokenize str))))
    (when (cdr res)
      (error "Trailing input: %S" (cdr res)))
    (car res)))

;;; ---------------------------------------------------------------------
;;; String-level entry points
;;; ---------------------------------------------------------------------

(defconst can-prove--turnstile
  "\\(?:|-+\\||--\\|⊢\\|⊨\\|∴\\|therefore\\|hence\\|⟹\\)"
  "Regexp matching a turnstile separating premises from conclusion.")

(defun can-prove--clean (str)
  "Trim whitespace and trailing periods from STR."
  (string-trim-right str "[ \t\n\r.]+"))

(defun can-prove--parse-premises (str)
  "Parse premises in STR, separated by `,', `;' or `.'."
  (let ((result nil))
    (dolist (part (split-string str "[,;.]"))
      (unless (string-match-p "\\`[ \t\n\r]*\\'" part)
        (push (can-prove-parse part) result)))
    (nreverse result)))

(defun can-prove--parse-argument (str)
  "Parse STR into (PREMISES . CONCLUSION)."
  (let ((case-fold-search t) beg end)
    (unless (string-match can-prove--turnstile str)
      (error "No turnstile (e.g. \"|-\" or \"therefore\") in: %s" str))
    (setq beg (match-beginning 0)
          end (match-end 0))
    (cons (can-prove--parse-premises (substring str 0 beg))
          (can-prove-parse (can-prove--clean (substring str end))))))

(defun can-prove-string (str)
  "Return :valid if STR is a tautology, else a counterexample."
  (can-prove-counterexample nil (can-prove-parse str)))

(defun can-prove-argument (str)
  "Check the argument in STR, e.g. \"p => q. p. therefore q.\"."
  (let ((p (can-prove--parse-argument str)))
    (can-prove-counterexample (car p) (cdr p))))

;;; ---------------------------------------------------------------------
;;; Rendering and explanation
;;; ---------------------------------------------------------------------

(defconst can-prove--prec
  '((iff . 1) (implies . 2) (xor . 3) (or . 3) (and . 4) (not . 5))
  "Precedence table for rendering.")

(defun can-prove--render-bin (sep lhs lp rhs rp)
  (format "%s %s %s"
          (can-prove--render lhs lp) sep (can-prove--render rhs rp)))

(defun can-prove--render (f &optional parent-prec)
  "Render F in plain English, adding parentheses when needed."
  (let ((pp (or parent-prec 0)))
    (cond
     ((eq f t) "true")
     ((null f) "false")
     ((symbolp f) (symbol-name f))
     (t
      (let* ((op (car f))
             (prec (cdr (assq op can-prove--prec)))
             (s (pcase op
                  ('not (concat "not " (can-prove--render (nth 1 f) prec)))
                  ('and (can-prove--render-bin "and" (nth 1 f) prec (nth 2 f) (1+ prec)))
                  ('or  (can-prove--render-bin "or" (nth 1 f) prec (nth 2 f) (1+ prec)))
                  ('xor (can-prove--render-bin "xor" (nth 1 f) prec (nth 2 f) (1+ prec)))
                  ('implies (can-prove--render-bin "implies" (nth 1 f) (1+ prec) (nth 2 f) prec))
                  ('iff (can-prove--render-bin "iff" (nth 1 f) (1+ prec) (nth 2 f) prec))
                  (_ (error "Cannot render: %s" op)))))
        (if (< prec pp) (concat "(" s ")") s))))))

(defcustom can-prove-explain-values '(0 . 1)
  "Strings used to render false and true in explanations."
  :type '(cons string string)
  :group 'can-prove)

(defun can-prove--render-value (truthy)
  (if truthy (cdr can-prove-explain-values) (car can-prove-explain-values)))

(defun can-prove-explain (premises conclusion)
  "Explain whether PREMISES entail CONCLUSION."
  (let* ((formula (can-prove--normalize
                   `(and ,@premises (not ,conclusion))))
         (atoms (sort (can-prove--atoms formula)
                      (lambda (a b)
                        (string< (symbol-name a) (symbol-name b)))))
         (prem-str (if premises
                       (mapconcat #'can-prove--render premises ". ")
                     "(no premises)"))
         (conc-str (can-prove--render conclusion))
         (ce (can-prove-counterexample premises conclusion)))
    (concat (format "%s. therefore %s.\n" prem-str conc-str)
            (if (eq ce :valid)
                "Valid - the premises entail the conclusion."
              (concat "Invalid - counterexample: "
                      (mapconcat (lambda (a)
                                   (format "%s=%s" a
                                           (can-prove--render-value (memq a ce))))
                                 atoms ". "))))))

(defun can-prove-explain-argument (str)
  "Explain the argument in STR, e.g. \"p => q. p. therefore q.\"."
  (let ((p (can-prove--parse-argument str)))
    (can-prove-explain (car p) (cdr p))))

;;; ---------------------------------------------------------------------
;;; Boolean simplification (direct pass, no Calc dependency)
;;; ---------------------------------------------------------------------

(defcustom can-prove-simplify-demorgan nil
  "Whether to push negations inward via De Morgan's laws.
This is canonicalization (toward negation normal form), not strictly
reduction, so it is off by default."
  :type 'boolean
  :group 'can-prove)

(defun can-prove--simplify-member (x list)
  "Non-nil if X is `equal' to some element of LIST."
  (seq-some (lambda (y) (equal x y)) list))

(defun can-prove--simplify-negate (f)
  "Return the simplified negation of F, which is assumed simplified."
  (cond ((eq f t) nil)
        ((null f) t)
        ((and (consp f) (eq (car f) 'not)) (nth 1 f))
        (t (list 'not f))))

(defun can-prove--simplify-flatten (op f)
  "Return the operands of F when F is an OP node, else (F)."
  (if (and (consp f) (eq (car f) op))
      (apply #'append
             (mapcar (lambda (x) (can-prove--simplify-flatten op x))
                     (cdr f)))
    (list f)))

(defun can-prove--simplify-sort (items)
  "Sort ITEMS by printed representation, for canonical comparison."
  (sort items (lambda (a b)
                (string< (prin1-to-string a) (prin1-to-string b)))))

(defun can-prove--simplify-rebuild (op items)
  "Build a left-associated OP tree from ITEMS."
  (let ((result (car items)))
    (dolist (x (cdr items) result)
      (setq result (list op result x)))))

(defun can-prove--simplify-absorb (op items)
  "Drop items of ITEMS subsumed by others under OP.
Implements `x AND (x OR y) := x' and its dual."
  (let ((dual (if (eq op 'and) 'or 'and)))
    (seq-filter
     (lambda (a)
       (not (and (consp a)
                 (eq (car a) dual)
                 (seq-some (lambda (x) (can-prove--simplify-member x items))
                           (cdr a)))))
     items)))

(defun can-prove--simplify-nary (op operands)
  "Simplify OP applied to flat, pre-simplified OPERANDS."
  (let* ((and-p (eq op 'and))
         (absorbing (if and-p nil t))
         (unit (if and-p t nil)))
    (if (memq absorbing operands)
        absorbing
      (let ((unique nil) (conflict nil))
        (dolist (x operands)
          (unless (eq x unit)
            (unless (can-prove--simplify-member x unique)
              (if (can-prove--simplify-member
                   (can-prove--simplify-negate x) unique)
                  (setq conflict t)
                (push x unique)))))
        (cond
         (conflict absorbing)
         ((null unique) unit)
         (t
          (setq unique (can-prove--simplify-absorb
                        op (can-prove--simplify-sort unique)))
          (cond
           ((null unique) unit)
           ((null (cdr unique)) (car unique))
           (t (can-prove--simplify-rebuild op unique)))))))))

(defun can-prove--simplify-not (a)
  "Simplify `(not A)', where A is already simplified."
  (cond
   ((eq a t) nil)
   ((null a) t)
   ((and (consp a) (eq (car a) 'not)) (nth 1 a))          ; !!a := a
   ((and can-prove-simplify-demorgan (consp a) (eq (car a) 'and))
    (can-prove--simplify-nary 'or (mapcar #'can-prove--simplify-not (cdr a))))
   ((and can-prove-simplify-demorgan (consp a) (eq (car a) 'or))
    (can-prove--simplify-nary 'and (mapcar #'can-prove--simplify-not (cdr a))))
   (t (list 'not a))))

(defun can-prove--simplify (f)
  "Simplify the normalized formula F using Boolean-algebra rules."
  (cond
   ((or (eq f t) (null f) (symbolp f)) f)
   ((eq (car f) 'not)
    (can-prove--simplify-not (can-prove--simplify (nth 1 f))))
   ((memq (car f) '(and or))
    (can-prove--simplify-nary
     (car f)
     (mapcar #'can-prove--simplify (can-prove--simplify-flatten (car f) f))))
   (t (error "Not a normalized formula: %S" f))))

(defun can-prove-simplify-formula (f)
  "Return a formula equivalent to F, simplified by Boolean-algebra rules.
F is normalized to and/or/not first, so the result is in that form."
  (can-prove--simplify (can-prove--normalize f)))

(defun can-prove-simplify (premises conclusion)
  "Return (PREMISES . CONCLUSION) with each formula simplified."
  (cons (mapcar #'can-prove-simplify-formula premises)
        (can-prove-simplify-formula conclusion)))

(defun can-prove--render-argument (premises conclusion)
  "Render PREMISES and CONCLUSION as a readable argument."
  (format "%s therefore %s."
          (if premises
              (mapconcat #'can-prove--render premises ". ")
            "(no premises)")
          (can-prove--render conclusion)))

(defun can-prove-simplify-argument (str)
  "Display a simplified, equivalent version of the argument in STR."
  (interactive "sArgument: ")
  (let* ((p (can-prove--parse-argument str))
         (s (can-prove-simplify (car p) (cdr p))))
    (message "%s" (can-prove--render-argument (car s) (cdr s)))))

(provide 'canprove)
;;; can-prove.el ends here
