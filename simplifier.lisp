;;;; simplifier.lisp
;;;; Complete, clean boolean formula simplifier (drop-in replacement)
;;;; Package name :simplifier so previous calls remain compatible.

(defpackage :simplifier
  (:use :cl)
  (:export :simplify :main :save-executable))
(in-package :simplifier)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operator metadata
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *op-meta*
  '((and     :identity t    :idem t   :sink nil  :ac t)
    (or      :identity nil  :idem t   :sink t   :ac t)
    (not     :identity :none :idem nil :sink :none :ac nil)
    (implies :identity :none :idem nil :sink :none :ac nil)
    (iff     :identity t    :idem nil :sink :none :ac t)
    (xor     :identity nil  :idem nil :sink :none :ac t)
    (if      :identity :none :idem nil :sink :none :ac nil)))

(defun op-name= (a b)
  "Compare operator names regardless of package."
  (string= (symbol-name a) (symbol-name b)))

(defun op-meta (op)
  (find op *op-meta* :key #'car :test #'op-name=))

(defun identity-of (op) (getf (cdr (op-meta op)) :identity :none))
(defun sink-of     (op) (getf (cdr (op-meta op)) :sink :none))
(defun idempotent-p (op) (getf (cdr (op-meta op)) :idem))

(defun true-p (x) (eq x 't))
(defun false-p (x) (eq x 'nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun has-value-p (val lst)
  "Check if val is in lst, handling T/NIL specially."
  (cond ((eq val 't) (member 't lst))
        ((eq val 'nil) (member 'nil lst))
        (t (member val lst :test #'equal))))

(defun remove-value (val lst)
  "Remove val from lst, handling T/NIL specially."
  (cond ((eq val 't) (remove 't lst :test #'eq))
        ((eq val 'nil) (remove 'nil lst :test #'eq))
        (t (remove val lst :test #'equal))))

(defun flatten-ac (op args)
  "Flatten associative/commutative nested occurrences of op."
  (loop for a in args append
        (if (and (consp a) (op-name= (car a) op)) (cdr a) (list a))))

(defun canonicalize-ac-args (args)
  "Deterministic ordering for AC argument lists: sort by printed representation."
  (sort (copy-list args) #'string< :key #'prin1-to-string))

(defun unique-preserve (lst)
  "Return a list where duplicates (by equal) are removed preserving first occurrence order."
  (let ((seen (make-hash-table :test 'equal)) out)
    (dolist (x lst (nreverse out))
      (unless (gethash x seen)
        (setf (gethash x seen) t)
        (push x out)))))

(defun make-neg (x)
  "Return the logical negation of x in normalized form:
   if x is (not Y) return Y, else return (not x)."
  (if (and (consp x) (op-name= (car x) 'not)) (cadr x) (list 'not x)))

(defun intern-in-cl (symbol)
  "Intern a symbol in the CL package to avoid package prefixes in output."
  (if (symbolp symbol)
      (intern (symbol-name symbol) :cl)
      symbol))

(defun unintern-form (form)
  "Recursively convert all symbols in form to CL package."
  (cond
    ((null form) nil)
    ((symbolp form) (intern-in-cl form))
    ((consp form) (cons (unintern-form (car form))
                       (unintern-form (cdr form))))
    (t form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Core simplification helpers (these implement the rules)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-not-once (arg)
  "Simplify a NOT node when its (single) argument has already been simplified."
  (cond
    ;; double negation: not(not p) => p
    ((and (consp arg) (op-name= (car arg) 'not)) (cadr arg))
    ;; constants
    ((true-p arg) 'nil)
    ((false-p arg) 't)
    ;; De Morgan: not (and ...) => or (not ...) ; not (or ...) => and (not ...)
    ((and (consp arg) (op-name= (car arg) 'and))
     (cons 'or (mapcar (lambda (x) (list 'not x)) (cdr arg))))
    ((and (consp arg) (op-name= (car arg) 'or))
     (cons 'and (mapcar (lambda (x) (list 'not x)) (cdr arg))))
    ;; not (implies p q) => and p (not q)  (we choose P AND NOT Q ordering)
    ((and (consp arg) (op-name= (car arg) 'implies))
     (let ((p (cadr arg)) (q (caddr arg)))
       (list 'and p (list 'not q))))
    ;; not (iff p q) where 2 args => xor p q
    ((and (consp arg) (op-name= (car arg) 'iff) (= (length (cdr arg)) 2))
     (cons 'xor (cdr arg)))
    ;; not (xor p q) => iff p q (for binary case)
    ((and (consp arg) (op-name= (car arg) 'xor) (= (length (cdr arg)) 2))
     (cons 'iff (cdr arg)))
    (t (list 'not arg))))

(defun simplify-implies-once (p q)
  "Simplify implies where p and q are already simplified."
  (cond
    ((true-p q) 't)                     ; p -> t = t
    ((false-p p) 't)                    ; nil -> q = t
    ((true-p p) q)                      ; t -> q = q
    ((false-p q) (list 'not p))         ; p -> nil = not p
    ((equal p q) 't)                    ; p -> p = t
    ;; p -> (not p) = not p  (redundant but fine)
    ((and (consp q) (op-name= (car q) 'not) (equal p (cadr q))) (list 'not p))
    ((and (consp p) (op-name= (car p) 'not) (equal (cadr p) q)) q)
    (t (list 'implies p q))))

(defun simplify-if-once (c tbr ebr)
  "Simplify ternary if with already-simplified branches."
  (cond
    ((true-p c) tbr)
    ((false-p c) ebr)
    ((equal tbr ebr) tbr)
    ((and (true-p tbr) (false-p ebr)) c)
    ((and (false-p tbr) (true-p ebr)) (list 'not c))
    (t (list 'if c tbr ebr))))

(defun apply-absorption (op args)
  "Simple absorption:
   and: remove (or ...) args that contain an element present at top-level
   or: remove (and ...) args that contain an element present at top-level"
  (cond
    ((op-name= op 'and)
     (remove-if
      (lambda (arg)
        (and (consp arg) (op-name= (car arg) 'or)
             (some (lambda (x) (member x args :test #'equal)) (cdr arg))))
      args))
    ((op-name= op 'or)
     (remove-if
      (lambda (arg)
        (and (consp arg) (op-name= (car arg) 'and)
             (some (lambda (x) (member x args :test #'equal)) (cdr arg))))
      args))
    (t args)))

(defun apply-redundancy (op args)
  "Detect patterns like (P∨Q)∧(P∨¬Q) => P and dual for OR.
   Works on binary inner AND/OR terms; repeats until no change."
  (when (and (or (op-name= op 'and) (op-name= op 'or)) 
             (> (length args) 1))
    (let ((changed t))
      (loop while changed do
        (setf changed nil)
        (block out
          (loop for i from 0 below (length args) do
            (loop for j from (1+ i) below (length args) do
              (let ((a1 (nth i args)) 
                    (a2 (nth j args)))
                (when (and (consp a1) 
                           (consp a2)
                           (op-name= (car a1) (car a2))
                           (or (op-name= (car a1) 'or) 
                               (op-name= (car a1) 'and))
                           (= (length (cdr a1)) 2) 
                           (= (length (cdr a2)) 2))
                  (let* ((p1 (first (cdr a1))) 
                         (q1 (second (cdr a1)))
                         (p2 (first (cdr a2))) 
                         (q2 (second (cdr a2)))
                         common-term)
                    ;; For AND over OR: (P∨Q) ∧ (P∨¬Q) => P
                    (when (and (op-name= op 'and) 
                               (op-name= (car a1) 'or))
                      (cond
                        ;; P matches P, Q matches ¬Q2
                        ((and (equal p1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal q1 (cadr q2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) q2))))
                         (setf common-term p1))
                        ;; P matches Q2, Q matches ¬P2
                        ((and (equal p1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal q1 (cadr p2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) p2))))
                         (setf common-term p1))
                        ;; Q matches P2, P matches ¬Q2
                        ((and (equal q1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal p1 (cadr q2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) q2))))
                         (setf common-term q1))
                        ;; Q matches Q2, P matches ¬P2
                        ((and (equal q1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal p1 (cadr p2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) p2))))
                         (setf common-term q1)))
                      (when common-term
                        (setf args (remove a1 args :test #'equal :count 1))
                        (setf args (remove a2 args :test #'equal :count 1))
                        (push common-term args)
                        (setf changed t)
                        (return-from out nil)))

                    ;; For OR over AND: (P∧Q) ∨ (P∧¬Q) => P
                    (when (and (op-name= op 'or) 
                               (op-name= (car a1) 'and))
                      (cond
                        ;; P matches P, Q matches ¬Q2
                        ((and (equal p1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal q1 (cadr q2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) q2))))
                         (setf common-term p1))
                        ;; P matches Q2, Q matches ¬P2
                        ((and (equal p1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal q1 (cadr p2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) p2))))
                         (setf common-term p1))
                        ;; Q matches P2, P matches ¬Q2
                        ((and (equal q1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal p1 (cadr q2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) q2))))
                         (setf common-term q1))
                        ;; Q matches Q2, P matches ¬P2
                        ((and (equal q1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal p1 (cadr p2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) p2))))
                         (setf common-term q1)))
                      (when common-term
                        (setf args (remove a1 args :test #'equal :count 1))
                        (setf args (remove a2 args :test #'equal :count 1))
                        (push common-term args)
                        (setf changed t)
                        (return-from out nil))))))))))))
  args)

(defun finalize-xor (args)
  "Given simplified XOR args (flattened), apply parity cancellation and return an appropriate form."
  (let ((table (make-hash-table :test 'equal)))
    (dolist (a args) (incf (gethash a table 0)))
    (let (kept)
      (maphash (lambda (k v) (when (oddp v) (push k kept))) table)
      (cond ((null kept) 'nil)
            ((= (length kept) 1) (first kept))
            (t (cons 'xor (canonicalize-ac-args kept)))))))

(defun finalize-iff (args)
  "Final handling for IFF (mostly binary rules)."
  (cond
    ((and (= (length args) 2) (equal (first args) (second args))) 't)
    ((and (= (length args) 2)
          (or (and (consp (second args)) (op-name= (car (second args)) 'not)
                   (equal (first args) (cadr (second args))))
              (and (consp (first args)) (op-name= (car (first args)) 'not)
                   (equal (cadr (first args)) (second args)))))
     'nil)
    (t (cons 'iff (canonicalize-ac-args args)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The main one-step simplifier (called repeatedly by simplify)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify-once (form)
  "Perform one pass of simplification on FORM."
  (cond
    ;; atom (variable or t/nil)
    ((atom form) form)

    ;; NOT
    ((and (consp form) (op-name= (car form) 'not))
     (let ((a (simplify-once (cadr form))))
       (simplify-not-once a)))

    ;; IF (ternary)
    ((and (consp form) (op-name= (car form) 'if))
     (let ((c (simplify-once (cadr form)))
           (tbr (simplify-once (caddr form)))
           (ebr (simplify-once (cadddr form))))
       (simplify-if-once c tbr ebr)))

    ;; IMPLIES
    ((and (consp form) (op-name= (car form) 'implies))
     (let ((p (simplify-once (cadr form)))
           (q (simplify-once (caddr form))))
       (simplify-implies-once p q)))

    ;; AND / OR / XOR / IFF (AC operators)
    ((and (consp form)
          (or (op-name= (car form) 'and)
              (op-name= (car form) 'or)
              (op-name= (car form) 'xor)
              (op-name= (car form) 'iff)))
     (let* ((op (car form))
            ;; simplify child args
            (args (mapcar #'simplify-once (cdr form)))
            ;; flatten associative ops
            (args (flatten-ac op args))
            ;; sink and identity
            (sink (sink-of op))
            (ident (identity-of op)))
       ;; sink check
       (when (not (eq sink :none))
         (when (has-value-p sink args) (return-from simplify-once sink)))
       ;; identity removal
       (when (not (eq ident :none))
         (setf args (remove-value ident args)))
       ;; zero/one arity short-circuits
       (when (null args) (return-from simplify-once ident))
       (when (= (length args) 1) (return-from simplify-once (first args)))
       ;; idempotence for AND/OR
       (when (and (idempotent-p op) (or (op-name= op 'and) (op-name= op 'or)))
         (setf args (unique-preserve args)))
       (when (= (length args) 1) (return-from simplify-once (first args)))
       (when (null args) (return-from simplify-once ident))
       ;; complementary pairs (x and not x) or (x or not x)
       (when (or (op-name= op 'and) (op-name= op 'or))
         (dolist (a args)
           (let ((neg-a (if (and (consp a) (op-name= (car a) 'not)) (cadr a) (list 'not a))))
             (when (member neg-a args :test #'equal)
               (return-from simplify-once (if (op-name= op 'and) 'nil 't))))))

       ;; absorption
       (when (or (op-name= op 'and) (op-name= op 'or))
         (setf args (apply-absorption op args))
         (when (= (length args) 1) (return-from simplify-once (first args)))
         (when (null args) (return-from simplify-once ident))
         ;; redundancy patterns
         (setf args (apply-redundancy op args))
         (when (= (length args) 1) (return-from simplify-once (first args)))
         (when (null args) (return-from simplify-once ident)))

       ;; finalize per operator
       (cond
         ((op-name= op 'xor) (finalize-xor args))
         ((op-name= op 'iff) (finalize-iff args))
         (t ;; and / or default: canonicalize and return
          (cons op (canonicalize-ac-args args))))))

    ;; fallback: unknown operator - simplify arguments
    (t (cons (car form) (mapcar #'simplify-once (cdr form))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Outer fixpoint loop
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun simplify (form)
  "Repeatedly apply simplify-once until a fixpoint is reached."
  (let ((prev nil) (curr form))
    (loop while (not (equal prev curr)) do
          (setf prev curr)
          (setf curr (simplify-once curr)))
    ;; Convert all symbols to CL package to avoid package prefixes
    (unintern-form curr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; I/O helpers and CLI
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-formula-from-file (filename)
  (with-open-file (in filename :direction :input) (read in)))

(defun write-formula-to-file (formula filename)
  (with-open-file (out filename :direction :output :if-exists :supersede)
    (prin1 formula out) (terpri out)))

(defun main ()
  (let ((args (rest sb-ext:*posix-argv*)))
    (if (= (length args) 2)
        (handler-case
            (let* ((formula (read-formula-from-file (first args)))
                   (simplified (simplify formula)))
              (write-formula-to-file simplified (second args))
              (format t "Success: ~A -> ~A~%" (first args) (second args))
              (sb-ext:exit :code 0))
          (error (e)
            (format *error-output* "Error: ~A~%" e)
            (sb-ext:exit :code 1)))
        (progn
          (format *error-output* "Usage: simplifier <input> <output>~%")
          (sb-ext:exit :code 1)))))

(defun save-executable ()
  (sb-ext:save-lisp-and-die "simplifier"
                            :toplevel #'main
                            :executable t
                            :compression t))

(format t "~%Clean simplifier loaded (package :simplifier).~%")