; fn: the record log's open as a stream of entries (lane log-kernel-memory,
; 2026-09-27; D27, D35/F8 reopen under 256 MB).
;
; The open used to read a whole segment into one string (SBCL: four octets
; per character) and decode it with fn-lg-decode, which answers every record
; of the segment as an octet list at once (16 octets of conses per record
; octet): about 5.3 GB for the 10k x 32 KiB fixture before the replay began.
; The stream reads one entry at a time.  At POS the host reads
; (fn-lgw-header-len ST EXTENT) octets, ACL2 answers the entry's length from
; them (fn-lgw-entry-len, NIL: the scan stops there), the host reads that
; many octets at POS, and ACL2 decides the entry (fn-lgw-step): its record
; (handed to the replay and then dropped), the next state -- the offset past
; the entry's padding, the chain's trailer, the count, the next txid -- and,
; at the stop, whether the entry there validates under another predecessor
; (a splice or a stale segment: fn-lgs-chain-broken-p).  The kernel at the
; stop is (fn-lgw-kernel ST).  The host decides nothing: every offset, length
; and stop comes from ACL2.
;
; KEYSTONE fn-lgw-run-is-the-open: the run of these calls over windows of the
; segment string S -- each window is S's octets at [POS, POS + K), what the
; host's pread answers (A-HOST's read of a regular file, the same assumption
; the whole-segment read made) -- emits exactly fn-lgc-open's records, in
; order, and ends in a state whose kernel is fn-lgc-open's concrete kernel
; and whose chain-broken verdict is fn-lgs-chain-broken-string-p's.  So
; fn-lgc-open-refines and fn-lgc-run-refines-the-kernel (PRF-276), and the
; relation's establishment over the logical twin, hold of the kernel the
; stream builds.
;
; Host: host/native/io.lisp fnn-log-stream-segment calls fn-lgw-start,
; fn-lgw-header-len, fn-lgw-entry-len, fn-lgw-step, fn-lgw-stop,
; fn-lgw-broken and fn-lgw-kernel; fnn-log-recover, fnn-log-open-read-only
; and fnn-log-scan-segments go through it.

(in-package "ACL2")
(include-book "store-log-kernel-concrete")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The stream's state: (:lgw POS PREV COUNT NEXT STOP BROKEN)
;   POS     the offset of the next entry (at the stop: the frontier)
;   PREV    the chain's last trailer (the genesis before any entry)
;   COUNT   the entries read
;   NEXT    one past the largest txid read, at least the floor
;   STOP    the scan has stopped
;   BROKEN  at the stop, an entry validates under another predecessor

(defun fn-lgw-make (pos prev count next stop broken)
  (declare (xargs :guard t))
  (list :lgw pos prev count next stop broken))

(defun fn-lgw-pos (st) (declare (xargs :guard (true-listp st))) (nfix (nth 1 st)))
(defun fn-lgw-prev (st) (declare (xargs :guard (true-listp st))) (nth 2 st))
(defun fn-lgw-count (st) (declare (xargs :guard (true-listp st))) (nfix (nth 3 st)))
(defun fn-lgw-next (st) (declare (xargs :guard (true-listp st))) (nfix (nth 4 st)))
(defun fn-lgw-stop (st) (declare (xargs :guard (true-listp st))) (nth 5 st))
(defun fn-lgw-broken (st) (declare (xargs :guard (true-listp st))) (nth 6 st))

(defthm fn-lgw-fields-of-make
  (let ((st (fn-lgw-make pos prev count next stop broken)))
    (and (equal (fn-lgw-pos st) (nfix pos))
         (equal (fn-lgw-prev st) prev)
         (equal (fn-lgw-count st) (nfix count))
         (equal (fn-lgw-next st) (nfix next))
         (equal (fn-lgw-stop st) stop)
         (equal (fn-lgw-broken st) broken))))

(defthm fn-lgw-make-true-listp
  (true-listp (fn-lgw-make pos prev count next stop broken))
  :rule-classes :type-prescription)

(defthm fn-lgw-pos-natp (natp (fn-lgw-pos st)) :rule-classes :type-prescription)
(defthm fn-lgw-count-natp (natp (fn-lgw-count st)) :rule-classes :type-prescription)
(defthm fn-lgw-next-natp (natp (fn-lgw-next st)) :rule-classes :type-prescription)

(in-theory (disable fn-lgw-make fn-lgw-pos fn-lgw-prev fn-lgw-count fn-lgw-next
                    fn-lgw-stop fn-lgw-broken))

(defun fn-lgw-start (genesis floor)
  (declare (xargs :guard t))
  (fn-lgw-make 0 genesis 0 (nfix floor) nil nil))

; -----------------------------------------------------------------------------
; The host's calls.

; The octets the host reads at POS for the entry's header: the header's ten,
; or what the segment has left.
(defun fn-lgw-header-len (st extent)
  (declare (xargs :guard (true-listp st)))
  (min *fn-frame-header-octets* (nfix (- (nfix extent) (fn-lgw-pos st)))))

; The entry's length, from the header window H, when the segment holds all of
; it; NIL: the scan stops at POS.
(defun fn-lgw-entry-len (h st extent)
  (declare (xargs :guard (and (stringp h) (true-listp st))))
  (let ((n (fn-lgd-declared-at h 0)))
    (and n (<= n (nfix (- (nfix extent) (fn-lgw-pos st)))) n)))

; The next txid after one more record (fn-lgt-next-after's step).
(defun fn-lgw-next-after-one (record next)
  (declare (xargs :guard t))
  (max (1+ (nfix (fn-lgt-txid record))) (nfix next)))

; At the stop: the entry E there validates as a chained frame of this log
; under the predecessor it claims, which is not the chain's last trailer.
(defun fn-lgw-broken-slice-p (slice last max)
  (declare (xargs :guard t))
  (let ((claimed (ec-call (fn-lgs-claimed-prev slice max))))
    (and (ec-call (fn-lg-entry-okp slice claimed max))
         (not (equal claimed last))
         t)))

; One entry: E is the entry's window (the octets fn-lgw-entry-len named, read
; at POS), or NIL when fn-lgw-entry-len answered NIL.  Answers (mv TOOK
; RECORD ST'): TOOK when E is a chained entry under PREV, then RECORD is its
; record.
(defun fn-lgw-step (e st unit max extent)
  (declare (xargs :guard (true-listp st)))
  (let ((pos (fn-lgw-pos st)) (prev (fn-lgw-prev st))
        (count (fn-lgw-count st)) (next (fn-lgw-next st)))
    (cond ((fn-lgw-stop st) (mv nil nil st))
          ((not (stringp e)) (mv nil nil (fn-lgw-make pos prev count next t nil)))
          (t (let ((slice (fn-lgd-range e 0 (length e))))
               (if (not (ec-call (fn-lg-entry-okp slice prev max)))
                   (mv nil nil (fn-lgw-make pos prev count next t
                                            (fn-lgw-broken-slice-p slice prev max)))
                 (let* ((n (length e))
                        (step (+ n (fn-lg-pad-len n unit)))
                        (record (ec-call (fn-lg-slice-record slice max)))
                        (last (ec-call (fn-lg-trailer slice))))
                   (mv t record
                       (fn-lgw-make (+ pos step) last (1+ count)
                                    (fn-lgw-next-after-one record next)
                                    (not (< (+ pos step) (nfix extent))) nil)))))))))

; The kernel at the stop (fn-lgc-open's shape).
(defun fn-lgw-kernel (st)
  (declare (xargs :guard (true-listp st)))
  (fn-lgc-make (fn-lgw-count st) (fn-lgw-prev st) (fn-lgw-pos st) (fn-lgw-next st)
               nil nil (fn-lgw-count st) :ready))

; -----------------------------------------------------------------------------
; The host's loop over the segment string S: each window is (subseq S POS
; (+ POS K)), the octets the host's pread answers.

(defthm fn-lgw-step-pos-grows
  (implies (mv-nth 0 (fn-lgw-step e st unit max extent))
           (< (fn-lgw-pos st) (fn-lgw-pos (mv-nth 2 (fn-lgw-step e st unit max extent)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lg-slice-record fn-lg-trailer
                                      fn-lgd-range fn-lg-pad-len fn-lgw-broken-slice-p)
           :use ((:instance fn-lg-entry-okp-consp
                            (slice (fn-lgd-range e 0 (length e)))
                            (prev (fn-lgw-prev st)))))))

(defun fn-lgw-run (s st unit max)
  (declare (xargs :measure (nfix (- (length s) (fn-lgw-pos st)))
                  :hints (("Goal" :in-theory (disable fn-lgw-step fn-lgw-entry-len
                                                      fn-lgw-header-len)))))
  (let* ((extent (length s))
         (pos (fn-lgw-pos st))
         (n (fn-lgw-entry-len (subseq s pos (+ pos (fn-lgw-header-len st extent))) st extent))
         (e (and n (subseq s pos (+ pos n)))))
    (mv-let (took record st2) (fn-lgw-step e st unit max extent)
      (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) extent))
          (mv-let (records st3) (fn-lgw-run s st2 unit max)
            (mv (cons record records) st3))
        (mv (if took (list record) nil) st2)))))

; -----------------------------------------------------------------------------
; A window's octets are the segment's at [POS, POS + K).

(local (defthm fn-lgw-nthcdr-of-nil (equal (nthcdr n nil) nil)))
(local (defthm fn-lgw-codes-of-nthcdr
  (equal (fn-lgd-codes (nthcdr n x)) (nthcdr n (fn-lgd-codes x)))))
(local (defthm fn-lgw-codes-of-take
  (implies (<= (nfix k) (len x))
           (equal (fn-lgd-codes (take k x)) (fn-bs-take k (fn-lgd-codes x))))))
(local (defthm fn-lgw-character-listp-nthcdr
  (implies (character-listp x) (character-listp (nthcdr n x)))))
(local (defthm fn-lgw-character-listp-take
  (implies (and (character-listp x) (<= (nfix k) (len x))) (character-listp (take k x)))))
(local (defthm fn-lgw-len-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))
(local (defthm fn-lgw-len-codes (equal (len (fn-lgd-codes x)) (len x))))

(defthm fn-lgw-len-octets
  (implies (stringp s) (equal (len (fn-lgd-octets s)) (length s))))

(defthm fn-lgw-octets-of-window
  (implies (and (stringp s) (natp pos) (natp end) (<= pos end) (<= end (length s)))
           (equal (fn-lgd-octets (subseq s pos end))
                  (fn-bs-take (- end pos) (nthcdr pos (fn-lgd-octets s)))))
  :hints (("Goal" :do-not-induct t :in-theory (enable subseq subseq-list))))

(defthm fn-lgw-stringp-subseq
  (implies (stringp s) (stringp (subseq s i j)))
  :hints (("Goal" :in-theory (enable subseq))))

(local (defthm fn-lgw-len-take (equal (len (take n x)) (nfix n))))

(defthm fn-lgw-length-subseq
  (implies (and (stringp s) (natp i) (natp j) (<= i j) (<= j (length s)))
           (equal (length (subseq s i j)) (- j i)))
  :hints (("Goal" :do-not-induct t :in-theory (enable subseq subseq-list))))

(defthm fn-lgw-declared-at-0
  (implies (stringp w)
           (equal (fn-lgd-declared-at w 0) (fn-lg-declared-len (fn-lgd-octets w))))
  :hints (("Goal" :in-theory (disable fn-lgd-declared-at fn-lg-declared-len fn-lgd-octets)
           :use ((:instance fn-lgd-header-at (s w) (pos 0))))))
