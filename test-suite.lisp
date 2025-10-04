;;;; test-suite-fixed.lisp
;;;; Fixed tests for the updated simplifier. Load whichever simplifier you prefer first:
;;;; (load "simplifier-patched.lisp") or (load "simplifier-clean.lisp")
;;;; Then run this file.

;; adjust this to the package exported by the simplifier you loaded:
;; if you loaded simplifier-patched.lisp -> package :simplifier
;; if simplifier-clean.lisp -> package :simplifier-clean
(in-package :cl-user)

;; Change the following two forms to match the simplifier you loaded:
;; (defparameter *simp-package* :simplifier)   ; for patched
(defparameter *simp-package* :simplifier)     ; default: patched; change to :simplifier-clean if needed

(defun simp-call (form)
  (funcall (intern "SIMPLIFY" (find-package *simp-package*)) form))

(defun run-comprehensive-tests ()
  "Run the comprehensive test cases. Expects canonical forms produced by the new simplifier."
  (let ((pass 0) (fail 0))
    (flet ((test-case (input expected desc)
             (let ((result (simp-call input)))
               (if (equal result expected)
                   (progn (incf pass) (format t "✓ ~A~%" desc))
                   (progn (incf fail)
                          (format t "✗ ~A~%" desc)
                          (format t "  Input: ~S~%" input)
                          (format t "  Expected: ~S~%" expected)
                          (format t "  Got: ~S~%~%" result))))))

      (format t "~%========================================~%")
      (format t "COMPREHENSIVE TEST SUITE (fixed)~%")
      (format t "========================================~%~%")

      ;; CONSTANT PROPAGATION (rules 1-12)
      (format t "--- Constant Propagation ---~%")
      (test-case '(and) 't "1. Empty AND returns T")
      (test-case '(or) 'nil "2. Empty OR returns NIL")
      (test-case '(and t x) 'x "3. AND identity elimination")
      (test-case '(or nil x) 'x "4. OR identity elimination")
      (test-case '(or t x) 't "5. OR sink T")
      (test-case '(and nil x) 'nil "6. AND sink NIL")
      (test-case '(and t nil) 'nil "7. AND T and NIL")
      (test-case '(implies x t) 't "8. X implies T")
      (test-case '(implies nil x) 't "9. NIL implies X")
      (test-case '(implies t x) 'x "10. T implies X")
      (test-case '(implies x nil) '(not x) "11. X implies NIL")

      ;; IDEMPOTENCE
      (format t "~%--- Idempotence ---~%")
      (test-case '(and p p) 'p "12. AND idempotent")
      (test-case '(or p p) 'p "13. OR idempotent")
      (test-case '(and p p p) 'p "14. AND triple idempotent")
      (test-case '(or q q q q) 'q "15. OR quad idempotent")
      (test-case '(implies p p) 't "16. P implies P = T")
      (test-case '(and x x y x) '(and x y) "17. Multiple duplicates (canonicalized)")

      ;; NEGATION
      (format t "~%--- Negation Rules ---~%")
      (test-case '(not (not p)) 'p "18. Double negation")
      (test-case '(not (not (not p))) '(not p) "19. Triple negation")
      (test-case '(not (not (not (not p)))) 'p "20. Quad negation")
      (test-case '(not t) 'nil "21. NOT T")
      (test-case '(not nil) 't "22. NOT NIL")
      (test-case '(and p (not p)) 'nil "23. P AND NOT P = NIL")
      (test-case '(or p (not p)) 't "24. P OR NOT P = T")
      (test-case '(and (not p) p) 'nil "25. NOT P AND P = NIL")
      (test-case '(or (not p) p) 't "26. NOT P OR P = T")
      (test-case '(implies p (not p)) '(not p) "27. P implies NOT P")
      (test-case '(implies (not p) p) 'p "28. NOT P implies P")

      ;; DEMORGAN
      (format t "~%--- DeMorgan's Laws ---~%")
      (test-case '(not (and p q)) '(or (not p) (not q)) "29. NOT(P AND Q)")
      (test-case '(not (or p q)) '(and (not p) (not q)) "30. NOT(P OR Q)")
      (test-case '(not (and p q r)) '(or (not p) (not q) (not r)) "31. NOT(P AND Q AND R)")
      (test-case '(not (or a b c)) '(and (not a) (not b) (not c)) "32. NOT(A OR B OR C)")

      ;; NEGATION OF CONNECTIVES
      (format t "~%--- Negation of Connectives ---~%")
      (test-case '(not (implies p q)) '(and (not q) p) "33. NOT(P implies Q)")
      (test-case '(not (iff p q)) '(xor p q) "34. NOT(P iff Q)")
      (test-case '(not (xor p q)) '(iff p q) "35. NOT(P xor Q)")

      ;; FLATTEN
      (format t "~%--- Flattening/Associativity ---~%")
      (test-case '(and p (and q r)) '(and p q r) "36. Flatten nested AND")
      (test-case '(or p (or q r)) '(or p q r) "37. Flatten nested OR")
      (test-case '(and (and p q) (and r s)) '(and p q r s) "38. Deep nested AND")
      (test-case '(or (or a b) (or c d)) '(or a b c d) "39. Multiple nested OR")
      (test-case '(xor (xor p q) r) '(xor p q r) "40. Flatten XOR")
      (test-case '(iff (iff p q) r) '(iff p q r) "41. Flatten IFF")

      ;; XOR
      (format t "~%--- XOR Rules ---~%")
      (test-case '(xor p p) 'nil "42. XOR self = NIL")
      (test-case '(xor p q p) 'q "43. XOR cancellation")
      (test-case '(xor p p p) 'p "44. XOR odd count")
      (test-case '(xor p q p q) 'nil "45. XOR double cancel")
      (test-case '(xor p q r p) '(xor q r) "46. XOR with duplicate")

      ;; IFF
      (format t "~%--- IFF Rules ---~%")
      (test-case '(iff p p) 't "47. IFF self = T")
      (test-case '(iff p (not p)) 'nil "48. IFF with negation = NIL")

      ;; ABSORPTION
      (format t "~%--- Absorption Laws ---~%")
      (test-case '(and p (or p q)) 'p "49. P AND (P OR Q) = P")
      (test-case '(or p (and p q)) 'p "50. P OR (P AND Q) = P")
      (test-case '(and (or p q) p) 'p "51. (P OR Q) AND P = P")
      (test-case '(or (and p q) p) 'p "52. (P AND Q) OR P = P")

      ;; REDUNDANCY
      (format t "~%--- Redundancy Laws ---~%")
      (test-case '(and (or p q) (or p (not q))) 'p "53. (P∨Q)∧(P∨¬Q) = P")
      (test-case '(or (and p q) (and p (not q))) 'p "54. (P∧Q)∨(P∧¬Q) = P")

      ;; IF-THEN-ELSE
      (format t "~%--- If-Then-Else Rules ---~%")
      (test-case '(if t p q) 'p "55. IF T then P")
      (test-case '(if nil p q) 'q "56. IF NIL then Q")
      (test-case '(if c p p) 'p "57. IF same branches")
      (test-case '(if c t nil) 'c "58. IF boolean (T/NIL) -> c")
      (test-case '(if c nil t) '(not c) "59. IF boolean (NIL/T) -> not c")

      ;; COMPLEX
      (format t "~%--- Complex Nested Formulas ---~%")
      (test-case '(and (and (and p q) r) s) '(and p q r s) "60. Deep nested AND")
      (test-case '(or (or (or a b) c) d) '(or a b c d) "61. Deep nested OR")
      (test-case '(and (or p (not p)) q) 'q "62. Tautology in AND")
      (test-case '(or (and p (not p)) q) 'q "63. Contradiction in OR")
      (test-case '(not (not (not (not x)))) 'x "64. Quadruple negation")

      ;; MIXED
      (format t "~%--- Mixed Operator Combinations ---~%")
      (test-case '(and (not (not p)) q) '(and p q) "65. Double neg in AND")
      (test-case '(or (not (not p)) q) '(or p q) "66. Double neg in OR")
      (test-case '(implies (not (not p)) q) '(implies p q) "67. Double neg in implies")
      (test-case '(and p q (and q r)) '(and p q r) "68. Flatten with duplicates")
      (test-case '(or p (or p q)) '(or p q) "69. Nested with duplicates")

      ;; EDGE CASES
      (format t "~%--- Edge Cases ---~%")
      (test-case 'p 'p "70. Single atom")
      (test-case 't 't "71. Constant T")
      (test-case 'nil 'nil "72. Constant NIL")
      (test-case '(and x) 'x "73. Single arg AND")
      (test-case '(or y) 'y "74. Single arg OR")
      (test-case '(not (and)) 'nil "75. NOT empty AND")
      (test-case '(not (or)) 't "76. NOT empty OR")

      ;; ADDITIONAL
      (format t "~%--- Additional Complex Patterns ---~%")
      (test-case '(and (and p q) (and q r)) '(and p q r) "77. Duplicate in nested AND")
      (test-case '(or (or p q) (or q r)) '(or p q r) "78. Duplicate in nested OR")
      (test-case '(xor (xor (xor p q) r) s) '(xor p q r s) "79. Multi-level XOR flatten")
      (test-case '(and t t t x) 'x "80. Multiple identities")
      (test-case '(or nil nil nil y) 'y "81. Multiple identities OR")

      (format t "~%========================================~%")
      (format t "RESULTS: ~A PASS, ~A FAIL out of ~A tests~%" pass fail (+ pass fail))
      (format t "Success Rate: ~,1F%~%" (* 100.0 (/ pass (+ pass fail))))
      (format t "========================================~%")
      (when (> fail 0)
        (format t "~%Note: Some failures may be due to canonicalization (different but equivalent forms)~%"))
      (= fail 0))))

;; Run tests
(run-comprehensive-tests)

