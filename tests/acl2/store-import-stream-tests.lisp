; Teeth for books/store-import-stream (PRF-369,
; fn-sxi-stream-plan-is-the-import-plan): the import walked a chunk at a
; time, the MANIFEST read a piece at each chunk's place, decides what the
; whole-archive plan decides -- the import and every refusal by name.
(in-package "ACL2")
(include-book "../../books/store-import-stream")
(include-book "../../books/codec-attach")

; The ground history of books/store-export's teeth (tests/acl2/
; store-export-tests.lisp): five records of four kinds at sequences
; 0 1 2 4 5, sealed as the open reads them.
(defconst *sxit-events*
  (list (fn-record-make 0 0 0 "<sxit-0@example.invalid>" '(65)
                        '("fn.letters") "archive" "subject" "evidence" 1 0)
        (fn-store-retention-event-make :undertake 1 1 1
                                       "obligation-1" "article-0" "local" 1)
        (fn-store-retention-event-make :release 2 2 1
                                       "obligation-1" "article-0" "local" 0)
        (fn-cpe-make 4 3 1 '(:bootstrap (1) (2)))
        (fn-cpe-make 5 4 1 '(:register (3) (4) (5) 1 2 3))))

(defun sxit-frames (events)
  (if (consp events)
      (cons (fn-frame-seal *fn-frame-magic-store* *fn-frame-version*
                           *fn-frame-store-kind*
                           (fn-store-event-encode (car events)))
            (sxit-frames (cdr events)))
    nil))

(make-event
 `(defconst *sxit-records* ',(pairlis$ '(0 1 2 4 5) (sxit-frames *sxit-events*))))
(make-event
 `(defconst *sxit-profile* ',(fn-bs-config-encode *fn-bs-profile-development*)))
(make-event `(defconst *sxit-frontier* ',(fn-bs-frontier-encode-impl 6)))
(defconst *sxit-configs* '(("groups" 1 2 3) ("peers" 4 5)))
(make-event
 `(defconst *sxit-manifest*
    ',(fn-sxp-manifest (fn-sxp-entries *sxit-profile* *sxit-frontier*
                                       *sxit-configs* *sxit-records*))))

; Three chunkings of the history: the host's at a quantum of 2 (three
; chunks, the last short), one chunk, one record per chunk.
(defun sxit-by (n xs)
  (declare (xargs :measure (len xs)))
  (if (and (consp xs) (posp n))
      (cons (take (min n (len xs)) xs) (sxit-by n (nthcdr (min n (len xs)) xs)))
    nil))
(defun sxit-plan (m profile chunks)
  (fn-sxi-stream-plan m profile *sxit-frontier* *sxit-configs* chunks '(:current nil)))
(defun sxit-whole (m profile records)
  (fn-sxp-import-plan m profile *sxit-frontier* *sxit-configs* records '(:current nil)))

; -----------------------------------------------------------------------------
; Reachable positive witness (no hypotheses: the conclusion, at every
; chunking): the streamed import of the export is the import.
(assert-event (equal (fn-sxp-chunks-records (sxit-by 2 *sxit-records*)) *sxit-records*))
(assert-event (equal (len (sxit-by 2 *sxit-records*)) 3))
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (sxit-by 2 *sxit-records*))
        (list :import *fn-bs-profile-development* *sxit-frontier*
              *sxit-configs* *sxit-records*)))
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (sxit-by 2 *sxit-records*))
        (sxit-whole *sxit-manifest* *sxit-profile* *sxit-records*)))
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (list *sxit-records*))
        (sxit-plan *sxit-manifest* *sxit-profile* (sxit-by 1 *sxit-records*))))
; Empty chunks change nothing.
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile*
                   (list nil (take 3 *sxit-records*) nil (nthcdr 3 *sxit-records*)))
        (sxit-whole *sxit-manifest* *sxit-profile* *sxit-records*)))

; -----------------------------------------------------------------------------
; Every refusal by name, streamed as whole.

; A record changed after the export (the third, in the second chunk): the
; MANIFEST names it.
(defun sxit-flip-last (octets)
  (if (consp octets)
      (if (consp (cdr octets))
          (cons (car octets) (sxit-flip-last (cdr octets)))
        (list (logxor 1 (nfix (car octets)))))
    nil))
(defconst *sxit-tampered*
  (update-nth 2 (cons 2 (sxit-flip-last (cdr (nth 2 *sxit-records*)))) *sxit-records*))
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (sxit-by 2 *sxit-tampered*))
        (list :refused :manifest-mismatch
              (fn-sxp-text-octets "records/00000000000000000002.txn"))))
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (sxit-by 2 *sxit-tampered*))
        (sxit-whole *sxit-manifest* *sxit-profile* *sxit-tampered*)))

; A MANIFEST one octet longer than the archive's lines: named MANIFEST (the
; host's read of what follows the last chunk).
(assert-event
 (equal (sxit-plan (append *sxit-manifest* '(10)) *sxit-profile* (sxit-by 2 *sxit-records*))
        (list :refused :manifest-mismatch *fn-sxp-manifest-name*)))
; A MANIFEST cut short (an archive whose last record has no line): the
; record whose line is missing.
(assert-event
 (equal (sxit-plan (butlast *sxit-manifest* 1) *sxit-profile* (sxit-by 2 *sxit-records*))
        (list :refused :manifest-mismatch
              (fn-sxp-text-octets "records/00000000000000000005.txn"))))
; The profile line changed: named at the head, no chunk read.
(defconst *sxit-manifest-flipped*
  (cons (if (equal (car *sxit-manifest*) 48) 49 48) (cdr *sxit-manifest*)))
(assert-event
 (equal (sxit-plan *sxit-manifest-flipped* *sxit-profile* (sxit-by 2 *sxit-records*))
        (list :refused :manifest-mismatch (fn-sxp-text-octets "profile"))))

; Out of sequence ACROSS a chunk boundary: sequences (0 1 | 1 ...): the
; previous sequence is carried between chunks.
(defconst *sxit-backwards*
  (list (nth 0 *sxit-records*) (nth 1 *sxit-records*)
        (cons 1 (cdr (nth 2 *sxit-records*)))))
(make-event
 `(defconst *sxit-manifest-backwards*
    ',(fn-sxp-manifest (fn-sxp-entries *sxit-profile* *sxit-frontier*
                                       *sxit-configs* *sxit-backwards*))))
(assert-event
 (equal (sxit-plan *sxit-manifest-backwards* *sxit-profile* (sxit-by 2 *sxit-backwards*))
        '(:refused :record-out-of-sequence 1)))
(assert-event
 (equal (sxit-plan *sxit-manifest-backwards* *sxit-profile* (sxit-by 2 *sxit-backwards*))
        (sxit-whole *sxit-manifest-backwards* *sxit-profile* *sxit-backwards*)))

; A profile the codec does not read, and a request it refuses.
(assert-event
 (equal (car (sxit-plan (fn-sxp-manifest (fn-sxp-entries '(1 2 3) *sxit-frontier*
                                                         *sxit-configs* *sxit-records*))
                        '(1 2 3) (sxit-by 2 *sxit-records*)))
        :refused))
(assert-event
 (equal (fn-sxi-stream-plan *sxit-manifest* *sxit-profile* *sxit-frontier* *sxit-configs*
                            (sxit-by 2 *sxit-records*) :bogus)
        '(:refused :profile :request)))

; -----------------------------------------------------------------------------
; Mutation witnesses (the conclusion is not vacuous).

; Chunks walked out of order are another history: refused by the MANIFEST.
(assert-event
 (equal (car (sxit-plan *sxit-manifest* *sxit-profile*
                        (let ((c (sxit-by 2 *sxit-records*)))
                          (list (cadr c) (car c) (caddr c)))))
        :refused))
; A step that did not carry the previous sequence (each chunk checked from
; nil) accepts the cross-boundary regression the carried one refuses.
(defun sxit-plan-uncarried (chunks)
  (if (consp chunks)
      (if (fn-sxp-out-of-sequence (car chunks) nil)
          :refused
        (sxit-plan-uncarried (cdr chunks)))
    :accepted))
(assert-event
 (equal (sxit-plan-uncarried (sxit-by 2 *sxit-backwards*))
        :accepted))
; A dropped chunk (a truncated read) is refused by name, never imported short.
(assert-event
 (equal (sxit-plan *sxit-manifest* *sxit-profile* (butlast (sxit-by 2 *sxit-records*) 1))
        (list :refused :manifest-mismatch *fn-sxp-manifest-name*)))
