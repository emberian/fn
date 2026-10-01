; fn: the decision journal read back a bounded chunk at a time (PKT-893,
; lane correctness-i4; D27).
;
; `store ROOT journal' (host/native/io.lisp fnn-command-store-journal) read
; the whole of STORE/decisions/decisions.fnj into one octet list and asked
; books/owner-time-journal.lisp fn-otm-journal-report for its line: a 2.4 MB
; journal was some 50 MB of conses, growing with the journal.  Here the host
; reads the file a bounded chunk at a time and feeds each chunk to
; fn-otjs-feed, which parses the lines as fn-otm-jparse does and keeps, of
; the entries read so far, only their count, their segment count and the
; replay's verdict and state (fn-otm-replay from fn-otm-init).  The work and
; allocation of one step are the chunk's; nothing is truncated.
;
; KEYSTONE fn-otjs-report-of-the-chunks-is-the-journal-report: whatever the
; chunking, the report and exit of the fed state are fn-otm-journal-report's
; and fn-otm-journal-exit's over the chunks' concatenation (the file).
;
; This book has the prefix `fn-otjs-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "owner-time-journal")

; NTH under guard t (the states are the host's to carry, never inspected).
(defun fn-otjs-nth (n x)
  (declare (xargs :guard (natp n)))
  (cond ((atom x) nil)
        ((zp n) (car x))
        (t (fn-otjs-nth (- n 1) (cdr x)))))

(defthm fn-otjs-nth-is-nth
  (equal (fn-otjs-nth n x) (nth n x)))

; ---------------------------------------------------------------------------
; The summary of a list of entries, oldest first: (N STARTS VERDICT S), the
; count, the segment count and fn-otm-replay's two values from fn-otm-init.
(defun fn-otjs-start-entryp (e)
  (declare (xargs :guard t))
  (and (consp e) (consp (cdr e)) (equal (cadr e) 0)))

(defun fn-otjs-sum-init ()
  (declare (xargs :guard t))
  (list 0 0 :agrees (fn-otm-init)))

(defun fn-otjs-sum-add (sum e)
  (declare (xargs :guard t))
  (let ((n (nfix (fn-otjs-nth 0 sum))) (k (nfix (fn-otjs-nth 1 sum)))
        (v (fn-otjs-nth 2 sum)) (s (fn-otjs-nth 3 sum)))
    (if (eq v :agrees)
        (mv-let (v2 s2) (fn-otm-replay s (list e))
          (list (+ 1 n) (+ k (if (fn-otjs-start-entryp e) 1 0)) v2 s2))
      (list (+ 1 n) (+ k (if (fn-otjs-start-entryp e) 1 0)) v s))))

; What a summary is: the summary of ENTRIES by definition.
(defun fn-otjs-sum-of (entries)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (v s) (fn-otm-replay (fn-otm-init) entries)
    (list (len entries) (fn-otm-journal-starts entries) v s)))

; ---------------------------------------------------------------------------
; The scanner: fn-otm-jparse's recursion, octet for octet, with the entries
; kept as their summary.  Answers (mv STOPP ACC FIELDS SUM); STOPP when an
; octet is malformed (the rest is not read, as fn-otm-jparse stops).
(defun fn-otjs-scan (xs acc fields sum)
  (declare (xargs :guard t :measure (len xs)))
  (if (consp xs)
      (let ((o (car xs)))
        (cond ((and (natp o) (<= 48 o) (<= o 57))
               (fn-otjs-scan (cdr xs) (+ (* 10 (nfix acc)) (- o 48)) fields sum))
              ((and (equal o 32) acc)
               (fn-otjs-scan (cdr xs) nil (cons acc fields) sum))
              ((and (equal o 10) acc)
               (fn-otjs-scan (cdr xs) nil nil
                             (fn-otjs-sum-add sum (fn-otm-revonto fields (list acc)))))
              (t (mv t acc fields sum))))
    (mv nil acc fields sum)))

; The chunk the host reads per step: a work bound, not a data bound (the
; file is read to its end, a chunk a step; the keystone holds whatever the
; chunking).  64 KiB of octets is about 1 MiB of list per step.
(defconst *fn-otjs-chunk-octets* 65536)

(defun fn-otjs-chunk-octets ()
  (declare (xargs :guard t))
  *fn-otjs-chunk-octets*)

; The fed state: (STOPP ACC FIELDS SUM).
(defun fn-otjs-init ()
  (declare (xargs :guard t))
  (list nil nil nil (fn-otjs-sum-init)))

; THE STEP the host calls once per chunk (host/native/io.lisp
; fnn-command-store-journal).  A stopped state reads nothing more.
(defun fn-otjs-feed (st chunk)
  (declare (xargs :guard (fn-cbor-octet-listp chunk)))
  (if (fn-otjs-nth 0 st)
      st
    (mv-let (stopp acc fields sum)
      (fn-otjs-scan chunk (fn-otjs-nth 1 st) (fn-otjs-nth 2 st) (fn-otjs-nth 3 st))
      (list stopp acc fields sum))))

(defun fn-otjs-status (st)
  (declare (xargs :guard t))
  (cond ((fn-otjs-nth 0 st) :malformed)
        ((or (fn-otjs-nth 1 st) (fn-otjs-nth 2 st)) :torn)
        (t :whole)))

;; The line of a parse STATUS and a summary SUM.
(defun fn-otjs-report-of (status sum)
  (declare (xargs :guard t))
  (append (fn-osch-text "journal:")
          (fn-osch-kv "entries" (nfix (fn-otjs-nth 0 sum)))
          (fn-osch-kv "segments" (nfix (fn-otjs-nth 1 sum)))
          (fn-osch-text (cond ((eq status :whole) " status=whole")
                              ((eq status :torn) " status=torn")
                              (t " status=malformed")))
          (fn-osch-text " replay=")
          (fn-otm-verdict-text (fn-otjs-nth 2 sum))
          (list 10)))

; The verb's line, from the fed state (the host calls it after the last
; chunk).
(defun fn-otjs-report (st)
  (declare (xargs :guard t))
  (fn-otjs-report-of (fn-otjs-status st) (fn-otjs-nth 3 st)))

; The verb's exit: 0 when the replay agrees, 1 otherwise.
(defun fn-otjs-exit (st)
  (declare (xargs :guard t))
  (if (eq (fn-otjs-nth 2 (fn-otjs-nth 3 st)) :agrees) 0 1))

; The chunks the host fed, concatenated (the file), and the fed state: the
; keystone's vocabulary, logic only (the host calls fn-otjs-feed per chunk).
(defun fn-otjs-concat (chunks)
  (declare (xargs :verify-guards nil))
  (if (consp chunks)
      (append (car chunks) (fn-otjs-concat (cdr chunks)))
    nil))

(defun fn-otjs-feed-all (st chunks)
  (declare (xargs :verify-guards nil))
  (if (consp chunks)
      (fn-otjs-feed-all (fn-otjs-feed st (car chunks)) (cdr chunks))
    (fn-otjs-feed st nil)))

; ---------------------------------------------------------------------------
; The proof.  fn-otm-revonto is reverse-onto; the summary of one entry more
; is fn-otjs-sum-add's; the scanner is fn-otm-jparse on summaries.
(local
 (defthm fn-otjs-revonto-append-acc
   (equal (fn-otm-revonto x (append a b))
          (append (fn-otm-revonto x a) b))))

(local
 (defthm fn-otjs-revonto-cons-nil
   (equal (fn-otm-revonto (cons e r) nil)
          (append (fn-otm-revonto r nil) (list e)))
   :hints (("Goal" :use ((:instance fn-otjs-revonto-append-acc
                                    (x r) (a nil) (b (list e))))
            :in-theory (disable fn-otjs-revonto-append-acc)))))

(local
 (defthm fn-otjs-replay-append
   (equal (fn-otm-replay s (append a b))
          (mv-let (v s1) (fn-otm-replay s a)
            (if (eq v :agrees) (fn-otm-replay s1 b) (mv v s1))))
   :hints (("Goal" :induct (fn-otm-replay s a)
            :in-theory (e/d (fn-otm-replay)
                            (fn-otm-disk-event fn-otm-note fn-otm-init
                             fn-otm-kind-of-op fn-otm-word-code fn-otm-jseq
                             nth len nat-listp))))))

(local
 (defthm fn-otjs-starts-append
   (equal (fn-otm-journal-starts (append a b))
          (+ (fn-otm-journal-starts a) (fn-otm-journal-starts b)))))

(local
 (defthm fn-otjs-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-otjs-sum-of-one-more
   (equal (fn-otjs-sum-of (append entries (list e)))
          (fn-otjs-sum-add (fn-otjs-sum-of entries) e))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-otjs-sum-of fn-otjs-sum-add fn-otjs-start-entryp
                             fn-otm-journal-starts)
                            (fn-otm-replay (:e fn-otm-init) fn-otm-init))))))

; The induction both recursions take together.
(local
 (defun fn-otjs-scan-jparse-ind (xs acc fields rentries sum)
   (declare (xargs :measure (len xs)))
   (if (consp xs)
       (let ((o (car xs)))
         (cond ((and (natp o) (<= 48 o) (<= o 57))
                (fn-otjs-scan-jparse-ind (cdr xs) (+ (* 10 (nfix acc)) (- o 48))
                                         fields rentries sum))
               ((and (equal o 32) acc)
                (fn-otjs-scan-jparse-ind (cdr xs) nil (cons acc fields) rentries sum))
               ((and (equal o 10) acc)
                (fn-otjs-scan-jparse-ind
                 (cdr xs) nil nil
                 (cons (fn-otm-revonto fields (list acc)) rentries)
                 (fn-otjs-sum-add sum (fn-otm-revonto fields (list acc)))))
               (t (list acc fields rentries sum))))
     (list acc fields rentries sum))))

(local
 (defthm fn-otjs-scan-is-jparse
   (implies (equal sum (fn-otjs-sum-of (fn-otm-revonto rentries nil)))
            (let ((r (fn-otjs-scan xs acc fields sum)))
              (mv-let (status entries) (fn-otm-jparse xs acc fields rentries)
                (and (equal (fn-otjs-sum-of entries) (mv-nth 3 r))
                     (equal status
                            (cond ((mv-nth 0 r) :malformed)
                                  ((or (mv-nth 1 r) (mv-nth 2 r)) :torn)
                                  (t :whole)))))))
   :hints (("Goal" :induct (fn-otjs-scan-jparse-ind xs acc fields rentries sum)
            :in-theory (disable fn-otjs-sum-of fn-otjs-sum-add)))))

(local
 (defthm fn-otjs-scan-append
   (equal (fn-otjs-scan (append a b) acc fields sum)
          (mv-let (stopp acc1 fields1 sum1) (fn-otjs-scan a acc fields sum)
            (if stopp
                (mv stopp acc1 fields1 sum1)
              (fn-otjs-scan b acc1 fields1 sum1))))
   :hints (("Goal" :induct (fn-otjs-scan a acc fields sum)
            :in-theory (disable fn-otjs-sum-add)))))

; The step is associative over the chunks: feeding A then B is feeding their
; concatenation.
(defthm fn-otjs-feed-of-append
  (equal (fn-otjs-feed (fn-otjs-feed st a) b)
         (fn-otjs-feed st (append a b)))
  :hints (("Goal" :in-theory (disable fn-otjs-scan))))

(defthm fn-otjs-feed-all-is-feed-of-concat
  (equal (fn-otjs-feed-all st chunks)
         (fn-otjs-feed st (fn-otjs-concat chunks)))
  :hints (("Goal" :induct (fn-otjs-feed-all st chunks)
            :in-theory (disable fn-otjs-feed))
          ("Subgoal *1/2" :use ((:instance fn-otjs-feed-of-append
                                           (a (car chunks))
                                           (b (fn-otjs-concat (cdr chunks)))))
           :in-theory (disable fn-otjs-feed fn-otjs-feed-of-append))))

(local
 (defthm fn-otjs-feed-init-is-jparse
   (let ((st (fn-otjs-feed (fn-otjs-init) octets)))
     (mv-let (status entries) (fn-otm-jparse octets nil nil nil)
       (and (equal (fn-otjs-nth 3 st) (fn-otjs-sum-of entries))
            (equal (fn-otjs-status st) status))))
   :hints (("Goal" :use ((:instance fn-otjs-scan-is-jparse
                                    (xs octets) (acc nil) (fields nil) (rentries nil)
                                    (sum (fn-otjs-sum-init))))
            :in-theory (disable fn-otjs-scan-is-jparse fn-otjs-scan fn-otm-jparse
                                fn-otjs-sum-of)))))

; The whole-file functions are the line and exit of jparse's status and the
; summary of its entries.
(local
 (defthm fn-otjs-journal-report-is-report-of
   (mv-let (status entries) (fn-otm-jparse octets nil nil nil)
     (and (equal (fn-otm-journal-report octets)
                 (fn-otjs-report-of status (fn-otjs-sum-of entries)))
          (equal (fn-otm-journal-exit octets)
                 (if (eq (fn-otjs-nth 2 (fn-otjs-sum-of entries)) :agrees) 0 1))))
   :hints (("Goal" :in-theory (e/d (fn-otm-journal-report fn-otm-journal-exit
                                    fn-otm-journal-read fn-otjs-report-of fn-otjs-sum-of)
                                   (fn-otjs-scan-is-jparse fn-otm-jparse fn-otm-replay
                                    (:e fn-otm-init) fn-otm-init
                                    fn-otm-verdict-text fn-osch-text fn-osch-kv))))))

(local
 (defthm fn-otjs-report-of-feed-is-the-journal-report
   (let ((st (fn-otjs-feed (fn-otjs-init) octets)))
     (and (equal (fn-otjs-report st) (fn-otm-journal-report octets))
          (equal (fn-otjs-exit st) (fn-otm-journal-exit octets))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-otjs-feed-init-is-jparse)
                  (:instance fn-otjs-journal-report-is-report-of))
            :in-theory (e/d (fn-otjs-report fn-otjs-exit)
                            (fn-otjs-feed-init-is-jparse fn-otjs-journal-report-is-report-of
                             fn-otjs-scan-is-jparse fn-otjs-feed fn-otjs-init (:e fn-otjs-init)
                             fn-otjs-report-of fn-otjs-sum-of fn-otjs-status
                             fn-otm-journal-report fn-otm-journal-exit fn-otm-jparse))))))

; KEYSTONE.  Whatever the chunking, the fed state's report and exit are the
; whole file's: fn-otm-journal-report and fn-otm-journal-exit over the
; concatenation of the chunks.
(defthm fn-otjs-report-of-the-chunks-is-the-journal-report
  (let ((st (fn-otjs-feed-all (fn-otjs-init) chunks)))
    (and (equal (fn-otjs-report st)
                (fn-otm-journal-report (fn-otjs-concat chunks)))
         (equal (fn-otjs-exit st)
                (fn-otm-journal-exit (fn-otjs-concat chunks)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-otjs-report-of-feed-is-the-journal-report
                            (octets (fn-otjs-concat chunks))))
           :in-theory (e/d (fn-otjs-feed-all-is-feed-of-concat)
                           (fn-otjs-report-of-feed-is-the-journal-report
                            fn-otjs-feed-all fn-otjs-concat fn-otjs-feed fn-otjs-init
                            (:e fn-otjs-init) fn-otjs-report fn-otjs-exit
                            fn-otm-journal-report fn-otm-journal-exit)))))

; The host reads the report after its last chunk without the fold's final
; empty feed: that feed changes neither the line nor the exit.
(defthm fn-otjs-feed-nil-keeps-the-report
  (and (equal (fn-otjs-report (fn-otjs-feed st nil)) (fn-otjs-report st))
       (equal (fn-otjs-exit (fn-otjs-feed st nil)) (fn-otjs-exit st)))
  :hints (("Goal" :in-theory (disable fn-otjs-report-of))))

(verify-guards fn-otjs-sum-of)

(in-theory (disable fn-otjs-scan fn-otjs-feed fn-otjs-report fn-otjs-report-of fn-otjs-exit
                    fn-otjs-sum-add fn-otjs-sum-of))
