;;; canprove-calc.el --- Calc-backed reference simplifier  -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Your Name

;; Author: Your Name <you@example.com>
;; Maintainer: Your Name <you@example.com>
;; URL: https://example.com/canprove
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1") (canprove "0.1.0"))
;; Keywords: convenience tools lisp

;; This file is not part of GNU Emacs.

;;; Commentary:

;; An optional, Calc-backed reference simplifier for `canprove'.  The
;; main package is Calc-free and uses a direct Boolean-algebra pass;
;; this extension exists so you can cross-check that pass against an
;; independent simplifier.
;;
;; Honest expectation: Calc's simplifier folds constants (`p && 0',
;; `p || 1', ...) but implements NO idempotence, complementarity, or
;; absorption rules for `&&'/`||'.  It will look weaker than the direct
;; pass approach on anything interesting.  Thus, its main value is as
;; a second opinion.
;;
;; Usage:
;;
;;   (require 'canprove-calc)
;;   (can-prove-calc-simplify-formula '(and p p))
;;   (can-prove-calc-simplify-argument "p and p. therefore p.")
;;   (can-prove-calc-compare '(and p (or p q)))
;;   (can-prove-calc-compare-argument "p and p. therefore p.")

;;; Code:

(require 'calc)
(require 'canprove)

(defcustom can-prove-calc-verify t
  "Whether to verify that Calc's output is equivalent to its input.
Verification uses `canprove' itself, so it is exact but costs one
tautology check per formula."
  :type 'boolean
  :group 'canprove)

(defun can-prove-calc--to-calc (f)
  "Translate normalized formula F into a Calc expression string."
  (cond
   ((eq f t) "1")
   ((null f) "0")
   ((symbolp f) (symbol-name f))
   (t (pcase (car f)
        ('not (format "!(%s)" (can-prove-calc--to-calc (nth 1 f))))
        ('and (format "(%s) && (%s)"
                     (can-prove-calc--to-calc (nth 1 f))
                     (can-prove-calc--to-calc (nth 2 f))))
        ('or  (format "(%s) || (%s)"
                     (can-prove-calc--to-calc (nth 1 f))
                     (can-prove-calc--to-calc (nth 2 f))))
        (_ (error "Cannot translate %S to Calc syntax" f))))))

(defun can-prove-calc-simplify-formula (f)
  "Return a formula equivalent to F, simplified by Calc.
F is normalized to and/or/not first, so the result is in that form."
  (let* ((norm (can-prove--normalize f))
         ;; Note: `calc-eval' simplifies on its own.  Its second
         ;; argument is a separator for multi-value results, NOT a
         ;; mode; wrapping in `simplify(...)' would invoke Calc's
         ;; stronger algebraic simplifier but adds no Boolean rules.
         (str  (can-prove-calc--to-calc norm))
         (out  (condition-case err
                   (can-prove-parse (calc-eval str))
                 (error (error "Calc failed on %S: %s" str err)))))
    (when (and can-prove-calc-verify
               (not (can-prove-tautology (list 'iff norm out))))
      (error "Calc's simplification is not equivalent: %S -> %S" norm out))
    out))

(defun can-prove-calc-simplify (premises conclusion)
  "Return (PREMISES . CONCLUSION) with each formula simplified by Calc."
  (cons (mapcar #'can-prove-calc-simplify-formula premises)
        (can-prove-calc-simplify-formula conclusion)))

(defun can-prove-calc-simplify-argument (str)
  "Display a Calc-simplified version of the argument in STR."
  (interactive "sArgument: ")
  (let* ((p (can-prove--parse-argument str))
         (s (can-prove-calc-simplify (car p) (cdr p))))
    (message "%s" (can-prove--render-argument (car s) (cdr s)))))

(defun can-prove-calc-compare (f)
  "Return (DIRECT CALC) simplifications of F, for comparison."
  (list (can-prove-simplify-formula f)
        (can-prove-calc-simplify-formula f)))

(defun can-prove-calc-compare-argument (str)
  "Display both the direct and Calc simplifications of the argument in STR."
  (interactive "sArgument: ")
  (let* ((p (can-prove--parse-argument str))
         (premises (car p))
         (conclusion (cdr p))
         (direct (can-prove-simplify premises conclusion))
         (calc   (can-prove-calc-simplify premises conclusion)))
    (message "Direct: %s\nCalc:   %s"
             (can-prove--render-argument (car direct) (cdr direct))
             (can-prove--render-argument (car calc) (cdr calc)))))

(provide 'canprove-calc)
;;; canprove-calc.el ends here
