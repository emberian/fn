; Teeth for books/store-export-stream (fn-sxp-stream-is-the-export): the
; archive written a chunk at a time is the whole-list export's, byte for byte.
(in-package "ACL2")
(include-book "../../books/store-export-stream")
(include-book "../../books/codec-attach")

; A ground history of five records at sequences 0 1 2 4 5 (3 a burned
; reservation); the export does not read a record's octets, it names, copies
; and digests them.
(defconst *sxst-records*
  '((0 1 2 3) (1 4 5) (2 6) (4 7 8 9 10) (5 11)))
(defconst *sxst-configs* '(("groups" 1 2 3) ("peers" 4 5)))
(defconst *sxst-profile* '(80 82 79))
(defconst *sxst-frontier* '(70 82))
; The host's chunking at a quantum of 2: three chunks, the last short.
(defconst *sxst-chunks*
  '(((0 1 2 3) (1 4 5)) ((2 6) (4 7 8 9 10)) ((5 11))))

; Reachable positive witness of the keystone (no hypotheses): the chunking
; covers the history, and both conclusions hold at it, evaluated with the
; attached digest.
(assert-event (equal (fn-sxp-chunks-records *sxst-chunks*) *sxst-records*))
(assert-event
 (equal (fn-sxp-stream-entries *sxst-profile* *sxst-frontier* *sxst-configs* *sxst-chunks*)
        (fn-sxp-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                        (fn-sxp-chunks-records *sxst-chunks*))))
(assert-event
 (equal (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier* *sxst-configs* *sxst-chunks*)
        (fn-sxp-manifest
         (fn-sxp-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                         (fn-sxp-chunks-records *sxst-chunks*)))))
; Nine entries, and the MANIFEST is nine lines of 64 hex digits.
(assert-event
 (equal (len (fn-sxp-stream-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                                    *sxst-chunks*))
        9))
(defun sxst-count-lf (xs)
  (if (consp xs) (+ (if (equal (car xs) 10) 1 0) (sxst-count-lf (cdr xs))) 0))
(assert-event
 (equal (sxst-count-lf (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier*
                                                    *sxst-configs* *sxst-chunks*))
        9))
; Every chunking gives the same archive: one chunk, and one record per chunk.
(assert-event
 (equal (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier* *sxst-configs*
                                (list *sxst-records*))
        (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier* *sxst-configs*
                                (pairlis$ *sxst-records* nil))))

; Mutation witness (the conclusion is not vacuous): chunks written out of
; order are a different history, and neither its entries nor its MANIFEST
; are the export's.
(defconst *sxst-swapped* '(((2 6) (4 7 8 9 10)) ((0 1 2 3) (1 4 5)) ((5 11))))
(assert-event
 (not (equal (fn-sxp-stream-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                                    *sxst-swapped*)
             (fn-sxp-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                             *sxst-records*))))
(assert-event
 (not (equal (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier* *sxst-configs*
                                     *sxst-swapped*)
             (fn-sxp-manifest
              (fn-sxp-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                              *sxst-records*)))))
; A dropped chunk (a truncated stream) is not the export either.
(assert-event
 (not (equal (fn-sxp-stream-manifest *sxst-profile* *sxst-frontier* *sxst-configs*
                                     (butlast *sxst-chunks* 1))
             (fn-sxp-manifest
              (fn-sxp-entries *sxst-profile* *sxst-frontier* *sxst-configs*
                              *sxst-records*)))))
