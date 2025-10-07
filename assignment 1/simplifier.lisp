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

(defun cl-sym (name)
  "Return a symbol interned in CL-USER package."
  (intern (string name) :cl-user))

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
  (if (and (consp x) (op-name= (car x) 'not)) 
      (cadr x) 
      (list (cl-sym 'not) x)))

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
     (cons (cl-sym 'or) (mapcar (lambda (x) (list (cl-sym 'not) x)) (cdr arg))))
    ((and (consp arg) (op-name= (car arg) 'or))
     (cons (cl-sym 'and) (mapcar (lambda (x) (list (cl-sym 'not) x)) (cdr arg))))
    ;; not (implies p q) => and p (not q)
    ((and (consp arg) (op-name= (car arg) 'implies))
     (let ((p (cadr arg)) (q (caddr arg)))
       (list (cl-sym 'and) p (list (cl-sym 'not) q))))
    ;; not (iff p q) where 2 args => xor p q
    ((and (consp arg) (op-name= (car arg) 'iff) (= (length (cdr arg)) 2))
     (cons (cl-sym 'xor) (cdr arg)))
    ;; not (xor p q) => iff p q (for binary case)
    ((and (consp arg) (op-name= (car arg) 'xor) (= (length (cdr arg)) 2))
     (cons (cl-sym 'iff) (cdr arg)))
    (t (list (cl-sym 'not) arg))))

(defun simplify-implies-once (p q)
  "Simplify implies where p and q are already simplified.
   Convert to OR form: p => q ≡ ¬p ∨ q"
  (cond
    ((true-p q) 't)
    ((false-p p) 't)
    ((true-p p) q)
    ((false-p q) (list (cl-sym 'not) p))
    ((equal p q) 't)
    ((and (consp q) (op-name= (car q) 'not) (equal p (cadr q))) 
     (list (cl-sym 'not) p))
    ((and (consp p) (op-name= (car p) 'not) (equal (cadr p) q)) q)
    ;; Convert to OR form: p => q ≡ ¬p ∨ q
    (t (list (cl-sym 'or) (make-neg p) q))))

(defun simplify-if-once (c tbr ebr)
  "Simplify ternary if with already-simplified branches."
  (cond
    ((true-p c) tbr)
    ((false-p c) ebr)
    ((equal tbr ebr) tbr)
    ((and (true-p tbr) (false-p ebr)) c)
    ((and (false-p tbr) (true-p ebr)) (list (cl-sym 'not) c))
    (t (list (cl-sym 'if) c tbr ebr))))

(defun apply-absorption (op args)
  "Enhanced absorption:
   and: remove (or ...) args that contain an element present at top-level
        also handle p ∧ (¬p ∨ q) => p ∧ q
   or: remove (and ...) args that contain an element present at top-level
       also handle p ∨ (¬p ∧ q) => p ∨ q"
  (cond
    ((op-name= op 'and)
     (let ((result args))
       ;; Standard absorption: p ∧ (p ∨ q) => p
       (setf result
             (remove-if
              (lambda (arg)
                (and (consp arg) (op-name= (car arg) 'or)
                     (some (lambda (x) (member x args :test #'equal)) (cdr arg))))
              result))
       ;; Enhanced: p ∧ (¬p ∨ q) => p ∧ q
       (let (modified)
         (dolist (a result)
           (if (and (consp a) (op-name= (car a) 'or))
               (let ((or-args (cdr a))
                     found-neg)
                 ;; Check if any top-level arg has its negation in this OR
                 (dolist (top result)
                   (unless (equal top a)
                     (let ((neg-top (make-neg top)))
                       (when (member neg-top or-args :test #'equal)
                         (setf or-args (remove neg-top or-args :test #'equal))
                         (setf found-neg t)))))
                 (if found-neg
                     (cond ((null or-args) nil) ; skip empty
                           ((= (length or-args) 1) (push (first or-args) modified))
                           (t (push (cons (cl-sym 'or) or-args) modified)))
                     (push a modified)))
               (push a modified)))
         (reverse modified))))
    ((op-name= op 'or)
     (let ((result args))
       ;; Standard absorption: p ∨ (p ∧ q) => p
       (setf result
             (remove-if
              (lambda (arg)
                (and (consp arg) (op-name= (car arg) 'and)
                     (some (lambda (x) (member x args :test #'equal)) (cdr arg))))
              result))
       ;; Enhanced: p ∨ (¬p ∧ q) => p ∨ q
       (let (modified)
         (dolist (a result)
           (if (and (consp a) (op-name= (car a) 'and))
               (let ((and-args (cdr a))
                     found-neg)
                 ;; Check if any top-level arg has its negation in this AND
                 (dolist (top result)
                   (unless (equal top a)
                     (let ((neg-top (make-neg top)))
                       (when (member neg-top and-args :test #'equal)
                         (setf and-args (remove neg-top and-args :test #'equal))
                         (setf found-neg t)))))
                 (if found-neg
                     (cond ((null and-args) nil) ; skip empty
                           ((= (length and-args) 1) (push (first and-args) modified))
                           (t (push (cons (cl-sym 'and) and-args) modified)))
                     (push a modified)))
               (push a modified)))
         (reverse modified))))
    (t args)))

(defun apply-distributivity (op args)
  "Apply distributivity rules:
   AND: p ∧ (q ∨ r) => (p ∧ q) ∨ (p ∧ r)
   OR: p ∨ (q ∧ r) => (p ∨ q) ∧ (p ∨ r)"
  (cond
    ((op-name= op 'and)
     ;; Look for pattern: atom AND (OR ...)
     (let ((atoms nil)
           (or-terms nil))
       (dolist (a args)
         (if (and (consp a) (op-name= (car a) 'or))
             (push a or-terms)
             (push a atoms)))
       (if (and atoms or-terms)
           ;; Apply distributivity: distribute atoms over OR terms
           (let ((distributed nil))
             (dolist (or-term or-terms)
               (let ((or-args (cdr or-term)))
                 (push (cons (cl-sym 'or)
                            (mapcar (lambda (or-arg)
                                      (cons (cl-sym 'and)
                                            (append atoms (list or-arg))))
                                    or-args))
                       distributed)))
             (if (= (length distributed) 1)
                 (first distributed)
                 (cons (cl-sym 'and) (append atoms distributed))))
           args)))
    ((op-name= op 'or)
     ;; Look for pattern: atom OR (AND ...)
     (let ((atoms nil)
           (and-terms nil))
       (dolist (a args)
         (if (and (consp a) (op-name= (car a) 'and))
             (push a and-terms)
             (push a atoms)))
       (if (and atoms and-terms)
           ;; Apply distributivity: distribute atoms over AND terms
           (let ((distributed nil))
             (dolist (and-term and-terms)
               (let ((and-args (cdr and-term)))
                 (push (cons (cl-sym 'and)
                            (mapcar (lambda (and-arg)
                                      (cons (cl-sym 'or)
                                            (append atoms (list and-arg))))
                                    and-args))
                       distributed)))
             (if (= (length distributed) 1)
                 (first distributed)
                 (cons (cl-sym 'or) (append atoms distributed))))
           args)))
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
                        ((and (equal p1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal q1 (cadr q2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) q2))))
                         (setf common-term p1))
                        ((and (equal p1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal q1 (cadr p2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) p2))))
                         (setf common-term p1))
                        ((and (equal q1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal p1 (cadr q2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) q2))))
                         (setf common-term q1))
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
                        ((and (equal p1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal q1 (cadr q2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) q2))))
                         (setf common-term p1))
                        ((and (equal p1 q2)
                              (or (and (consp p2) 
                                       (op-name= (car p2) 'not) 
                                       (equal q1 (cadr p2)))
                                  (and (consp q1) 
                                       (op-name= (car q1) 'not) 
                                       (equal (cadr q1) p2))))
                         (setf common-term p1))
                        ((and (equal q1 p2)
                              (or (and (consp q2) 
                                       (op-name= (car q2) 'not) 
                                       (equal p1 (cadr q2)))
                                  (and (consp p1) 
                                       (op-name= (car p1) 'not) 
                                       (equal (cadr p1) q2))))
                         (setf common-term q1))
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
  ;; Check for constants first
  (let ((has-true (member 't args :test #'eq))
        (non-const (remove-if (lambda (x) (or (eq x 't) (eq x 'nil))) args)))
    (when has-true
      ;; XOR with T: flip the result of the rest
      (let ((rest-result (if (null non-const)
                            'nil
                            (finalize-xor non-const))))
        (return-from finalize-xor
          (if (eq rest-result 'nil)
              't
              (if (eq rest-result 't)
                  'nil
                  (make-neg rest-result))))))
    ;; No T, continue with parity cancellation
    (setf args non-const))
  
  (let ((table (make-hash-table :test 'equal)))
    (dolist (a args) (incf (gethash a table 0)))
    (let (kept)
      (maphash (lambda (k v) (when (oddp v) (push k kept))) table)
      (cond ((null kept) 'nil)
            ((= (length kept) 1) (first kept))
            (t (cons (cl-sym 'xor) (canonicalize-ac-args kept)))))))

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
    ;; IFF with NIL: (p ≡ false) ≡ ¬p
    ((and (= (length args) 2) (eq (first args) 'nil))
     (make-neg (second args)))
    ((and (= (length args) 2) (eq (second args) 'nil))
     (make-neg (first args)))
    (t (cons (cl-sym 'iff) (canonicalize-ac-args args)))))

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
            (op-sym (cl-sym (symbol-name op)))
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
           (let ((neg-a (if (and (consp a) (op-name= (car a) 'not)) 
                           (cadr a) 
                           (list (cl-sym 'not) a))))
             (when (member neg-a args :test #'equal)
               (return-from simplify-once (if (op-name= op 'and) 'nil 't))))))
       
       ;; XOR: check for p XOR ¬p before finalization (always true)
       (when (op-name= op 'xor)
         (dolist (a args)
           (let ((neg-a (if (and (consp a) (op-name= (car a) 'not))
                           (cadr a)
                           (list (cl-sym 'not) a))))
             (when (member neg-a args :test #'equal)
               (return-from simplify-once 't)))))

       ;; absorption
       (when (or (op-name= op 'and) (op-name= op 'or))
         (setf args (apply-absorption op args))
         (when (= (length args) 1) (return-from simplify-once (first args)))
         (when (null args) (return-from simplify-once ident))
         ;; redundancy patterns
         (setf args (apply-redundancy op args))
         (when (= (length args) 1) (return-from simplify-once (first args)))
         (when (null args) (return-from simplify-once ident))
         
         ;; Case analysis: (p => q) ∧ (¬p => q) => q
         (when (op-name= op 'and)
           (let ((implies-terms (remove-if-not 
                                 (lambda (a) (and (consp a) (op-name= (car a) 'or))) 
                                 args)))
             (when (>= (length implies-terms) 2)
               (loop for i from 0 below (length implies-terms) do
                 (loop for j from (1+ i) below (length implies-terms) do
                   (let ((t1 (nth i implies-terms))
                         (t2 (nth j implies-terms)))
                     ;; Check for (¬p ∨ q) ∧ (p ∨ q) => q (which is p=>q ∧ ¬p=>q)
                     (when (and (= (length (cdr t1)) 2) (= (length (cdr t2)) 2))
                       (let ((a1 (second t1)) (b1 (third t1))
                             (a2 (second t2)) (b2 (third t2)))
                         ;; Check if b1 = b2 and a1 = ¬a2 or a2 = ¬a1
                         (when (equal b1 b2)
                           (when (or (equal a1 (make-neg a2))
                                    (equal a2 (make-neg a1)))
                             (return-from simplify-once b1)))))))))))
         
         ;; distributivity
         (let ((dist-result (apply-distributivity op args)))
           (unless (equal dist-result args)
             (return-from simplify-once dist-result))))

       ;; finalize per operator
       (cond
         ((op-name= op 'xor) (finalize-xor args))
         ((op-name= op 'iff) (finalize-iff args))
         (t ;; and / or default: canonicalize and return
          (cons op-sym (canonicalize-ac-args args))))))

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
    curr))

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

(format t "~%Enhanced simplifier loaded (package :simplifier).~%")
(format t "Updates: XOR/IFF constants, IMPLIES->OR, distributivity, enhanced absorption, case analysis~%")