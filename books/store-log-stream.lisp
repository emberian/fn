; fn: the record log's open as a stream of entries (lane log-open-stream,
; 2026-09-27; D27, D35/F8 reopen under 256 MB).
;
; The open used to read a whole segment into one string (SBCL: four octets
; per character) and decode it with fn-lg-decode, which answers every record
; of the segment as an octet list at once (16 octets of conses per record
; octet): a 9.2 GB peak on the 10k x 32 KiB fixture (rm2-format9's record).
; The stream reads one entry at a time.  At POS the host reads
; (fn-lgw-header-len ST EXTENT) octets, ACL2 answers the entry's length from
; them (fn-lgw-entry-len; NIL: nothing there is an entry), the host reads that
; many octets at POS (no read: NIL), and ACL2 decides the entry (fn-lgw-step):
; its record, handed to the replay and then dropped, and the next state -- the
; offset past the entry's padding, the chain's trailer, the count, the next
; txid, whether the scan stopped and, at the stop, whether an entry there
; validates under another predecessor (a splice or a stale segment,
; fn-lgs-chain-broken-p).  The kernel at the stop is (fn-lgw-kernel ST).  The
; host decides no offset, length or stop; the work of one step is bounded by
; one entry (the header's declared length, which the payload bound MAX
; limits for any entry the step accepts).
;
; KEYSTONE fn-lgw-run-is-the-open: over the segment's octets C (the host's
; reads are windows of C: A-HOST's read of a regular file, the assumption the
; whole-segment read made), the run of these calls from (fn-lgw-start GENESIS
; FLOOR) emits exactly the recovered kernel's committed records, in order, and
; ends in a state whose kernel is fn-lgc-of the recovered kernel
; (fn-lgt-recover, the kernel fn-lg-recover-program-establishes-the-relation
; names) and whose chain-broken verdict is fn-lgs-chain-broken-p's.  So
; fn-lgc-run-refines-the-kernel (PRF-276) and the relation's establishment
; hold of the kernel the stream builds.  Proof shape: one window's step is one
; step of fn-lg-scan (fn-lgw-step-is-a-scan-step), and the run composes them
; (fn-lgw-run-is-the-scan) with the step closed.
;
; Host: host/native/io.lisp fnn-log-stream-segment calls fn-lgw-start,
; fn-lgw-header-len, fn-lgw-entry-len, fn-lgw-step, fn-lgw-stop, fn-lgw-pos,
; fn-lgw-broken and fn-lgw-kernel; fnn-log-recover, fnn-log-open-read-only
; and fnn-log-scan-segments go through it.

(in-package "ACL2")
(include-book "store-log-kernel-concrete")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The stream's state: (:lgw POS PREV COUNT NEXT STOP BROKEN)

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

; The entry's length, from the header octets H, when the segment holds all of
; it; NIL: no entry starts at POS.
(defun fn-lgw-entry-len (h st extent)
  (declare (xargs :guard (true-listp st)))
  (let ((n (ec-call (fn-lg-declared-len h))))
    (and (natp n) (<= n (nfix (- (nfix extent) (fn-lgw-pos st)))) n)))

; The next txid after one more record (fn-lgt-next-after's step).
(defun fn-lgw-next-after-one (record next)
  (declare (xargs :guard t))
  (max (1+ (nfix (fn-lgt-txid record))) (nfix next)))

; At the stop: the octets E there validate as a chained frame of this log
; under the predecessor they claim, which is not the chain's last trailer.
(defun fn-lgw-broken-slice-p (e last max)
  (declare (xargs :guard t))
  (let ((claimed (ec-call (fn-lgs-claimed-prev e max))))
    (and (ec-call (fn-lg-entry-okp e claimed max))
         (not (equal claimed last))
         t)))

; One entry: E is the octets fn-lgw-entry-len named, read at POS, or NIL.
; Answers (mv TOOK RECORD ST').
(defun fn-lgw-step (e st unit max extent)
  (declare (xargs :guard (true-listp st)))
  (let ((pos (fn-lgw-pos st)) (prev (fn-lgw-prev st))
        (count (fn-lgw-count st)) (next (fn-lgw-next st)))
    (cond ((fn-lgw-stop st) (mv nil nil st))
          ((not (ec-call (fn-lg-entry-okp e prev max)))
           (mv nil nil (fn-lgw-make pos prev count next t
                                    (fn-lgw-broken-slice-p e prev max))))
          (t (let* ((n (len e))
                    (step (+ n (fn-lg-pad-len n unit)))
                    (record (ec-call (fn-lg-slice-record e max)))
                    (last (ec-call (fn-lg-trailer e))))
               (mv t record
                   (fn-lgw-make (+ pos step) last (1+ count)
                                (fn-lgw-next-after-one record next)
                                (not (< (+ pos step) (nfix extent))) nil)))))))

; The kernel at the stop (fn-lgc-open's shape).
(defun fn-lgw-kernel (st)
  (declare (xargs :guard (true-listp st)))
  (fn-lgc-make (fn-lgw-count st) (fn-lgw-prev st) (fn-lgw-pos st) (fn-lgw-next st)
               nil nil (fn-lgw-count st) :ready))

; -----------------------------------------------------------------------------
; The host's loop over the segment's octets C: the windows are what its reads
; answer.

(defun fn-lgw-window (c st)
  (declare (xargs :guard (true-listp st) :verify-guards nil))
  (let* ((pos (fn-lgw-pos st))
         (extent (len c))
         (n (fn-lgw-entry-len (fn-bs-take (fn-lgw-header-len st extent) (nthcdr pos c))
                              st extent)))
    (and n (fn-bs-take n (nthcdr pos c)))))

(defthm fn-lgw-entry-okp-len
  (implies (fn-lg-entry-okp e prev max) (< 0 (len e)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp)
           :use ((:instance fn-lg-entry-okp-consp (slice e))))))

(defthm fn-lgw-step-pos-grows
  (implies (mv-nth 0 (fn-lgw-step e st unit max extent))
           (< (fn-lgw-pos st) (fn-lgw-pos (mv-nth 2 (fn-lgw-step e st unit max extent)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lg-slice-record fn-lg-trailer
                                      fn-lg-pad-len fn-lgw-broken-slice-p fn-lgt-txid))))

(defun fn-lgw-run (c st unit max)
  (declare (xargs :measure (nfix (- (len c) (fn-lgw-pos st)))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-lgw-step fn-lgw-window)))))
  (mv-let (took record st2) (fn-lgw-step (fn-lgw-window c st) st unit max (len c))
    (if (and took (not (fn-lgw-stop st2)) (< (fn-lgw-pos st2) (len c)))
        (mv-let (records st3) (fn-lgw-run c st2 unit max)
          (mv (cons record records) st3))
      (mv (if took (list record) nil) st2))))

; -----------------------------------------------------------------------------
; One window is the scan's slice (the host's reads are windows of C).

(local
 (defthm fn-lgw-len-nthcdr
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))

(defthm fn-lgw-slice-is-take
  (implies (and (fn-lg-declared-len x) (<= (fn-lg-declared-len x) (len x)))
           (equal (fn-bs-take (fn-lg-declared-len x) x) (fn-lg-slice x)))
  :hints (("Goal" :in-theory (e/d (fn-lg-slice) (fn-lg-declared-len)))))

(defthm fn-lgw-slice-when-not-declared
  (implies (not (and (fn-lg-declared-len x) (<= (fn-lg-declared-len x) (len x))))
           (equal (fn-lg-slice x) nil))
  :hints (("Goal" :in-theory (e/d (fn-lg-slice) (fn-lg-declared-len)))))

(local
 (defthm fn-lgw-declared-natp
  (implies (fn-lg-declared-len x) (natp (fn-lg-declared-len x)))
  :hints (("Goal" :in-theory (disable fn-cbor-u32-from fn-bs-take)))))

(defthm fn-lgw-window-is-the-slice
  (implies (<= (fn-lgw-pos st) (len c))
           (equal (fn-lgw-window c st)
                  (fn-lg-slice (nthcdr (fn-lgw-pos st) c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-declared-len fn-lg-slice fn-lgd-declared-len-of-header)
           :use ((:instance fn-lgd-declared-len-of-header (x (nthcdr (fn-lgw-pos st) c)))))))


; -----------------------------------------------------------------------------
; One step is one step of the scan; the model's step lemmas.

(defthm fn-lgw-step-when-entry
  (implies (and (not (fn-lgw-stop st)) (fn-lg-entry-okp e (fn-lgw-prev st) max))
           (let* ((r (fn-lgw-step e st unit max extent))
                  (step (+ (len e) (fn-lg-pad-len (len e) unit))))
             (and (equal (mv-nth 0 r) t)
                  (equal (mv-nth 1 r) (fn-lg-slice-record e max))
                  (equal (fn-lgw-pos (mv-nth 2 r)) (+ (fn-lgw-pos st) step))
                  (equal (fn-lgw-prev (mv-nth 2 r)) (fn-lg-trailer e))
                  (equal (fn-lgw-count (mv-nth 2 r)) (+ 1 (fn-lgw-count st)))
                  (equal (fn-lgw-next (mv-nth 2 r))
                         (fn-lgw-next-after-one (fn-lg-slice-record e max) (fn-lgw-next st)))
                  (equal (fn-lgw-stop (mv-nth 2 r)) (not (< (+ (fn-lgw-pos st) step) (nfix extent))))
                  (equal (fn-lgw-broken (mv-nth 2 r)) nil))))
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lg-slice-record fn-lg-trailer
                                      fn-lg-pad-len fn-lgw-broken-slice-p fn-lgw-next-after-one))))

(defthm fn-lgw-step-when-no-entry
  (implies (and (not (fn-lgw-stop st)) (not (fn-lg-entry-okp e (fn-lgw-prev st) max)))
           (let ((r (fn-lgw-step e st unit max extent)))
             (and (equal (mv-nth 0 r) nil)
                  (equal (fn-lgw-pos (mv-nth 2 r)) (fn-lgw-pos st))
                  (equal (fn-lgw-prev (mv-nth 2 r)) (fn-lgw-prev st))
                  (equal (fn-lgw-count (mv-nth 2 r)) (fn-lgw-count st))
                  (equal (fn-lgw-next (mv-nth 2 r)) (fn-lgw-next st))
                  (equal (fn-lgw-broken (mv-nth 2 r))
                         (fn-lgw-broken-slice-p e (fn-lgw-prev st) max)))))
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lgw-broken-slice-p))))

(local
 (defthm fn-lgw-nthcdr-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x)))))

(defthm fn-lgw-chain-broken-when-first-fails
  (implies (not (fn-lg-entry-okp (fn-lg-slice x) prev max))
           (equal (fn-lgs-chain-broken-p x prev unit max)
                  (fn-lgw-broken-slice-p (fn-lg-slice x) prev max)))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max))
           :in-theory (disable fn-lg-entry-okp fn-lg-slice fn-lgs-claimed-prev))))

(defthm fn-lgw-chain-broken-of-step
  (implies (fn-lg-entry-okp (fn-lg-slice x) prev max)
           (equal (fn-lgs-chain-broken-p x prev unit max)
                  (let* ((slice (fn-lg-slice x))
                         (step (+ (len slice) (fn-lg-pad-len (len slice) unit))))
                    (fn-lgs-chain-broken-p (nthcdr step x) (fn-lg-trailer slice) unit max))))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max))
           :in-theory (disable fn-lg-entry-okp fn-lg-slice fn-lgs-claimed-prev fn-lg-scan
                               fn-lg-scan-last fn-lg-trailer fn-lg-pad-len fn-lg-slice-record))))

(defthm fn-lgw-chain-broken-of-atom
  (implies (atom x) (not (fn-lgs-chain-broken-p x prev unit max)))
  :hints (("Goal" :in-theory (enable fn-lg-slice fn-lg-declared-len))))

(defthm fn-lgw-scan-of-atom
  (implies (atom x) (equal (fn-lg-scan x prev unit max) (cons nil 0)))
  :hints (("Goal" :expand ((fn-lg-scan x prev unit max))
           :in-theory (enable fn-lg-slice fn-lg-declared-len))))

(defthm fn-lgw-scan-last-of-atom
  (implies (atom x) (equal (fn-lg-scan-last x prev unit max) prev))
  :hints (("Goal" :expand ((fn-lg-scan-last x prev unit max))
           :in-theory (enable fn-lg-slice fn-lg-declared-len))))

(defun fn-lgw-next-fold (records next)
  (declare (xargs :guard t))
  (if (consp records)
      (fn-lgw-next-fold (cdr records) (fn-lgw-next-after-one (car records) next))
    (nfix next)))

(local
 (defthm fn-lgw-next-after-of-max
  (implies (natp b)
           (equal (fn-lgt-next-after records (max b (nfix a)))
                  (max b (fn-lgt-next-after records a))))))

(defthm fn-lgw-next-fold-is-next-after
  (equal (fn-lgw-next-fold records floor) (fn-lgt-next-after records floor))
  :hints (("Goal" :induct (fn-lgw-next-fold records floor))
          ("Subgoal *1/1" :use ((:instance fn-lgw-next-after-of-max
                                           (records (cdr records))
                                           (b (1+ (nfix (fn-lgt-txid (car records)))))
                                           (a floor))))))

(defthm fn-lgw-step-took
  (implies (not (fn-lgw-stop st))
           (equal (car (fn-lgw-step e st unit max extent))
                  (if (fn-lg-entry-okp e (fn-lgw-prev st) max) t nil)))
  :hints (("Goal" :in-theory (disable fn-lg-entry-okp fn-lg-slice-record fn-lg-trailer
                                      fn-lg-pad-len fn-lgw-broken-slice-p fn-lgw-next-after-one))))

(defthm fn-lgw-broken-slice-p-of-nil
  (not (fn-lgw-broken-slice-p nil prev max))
  :hints (("Goal" :in-theory (enable fn-lg-entry-okp))))


; -----------------------------------------------------------------------------
; The run composes the steps (the step stays closed).

(defthm fn-lgw-run-is-the-scan
  (implies (and (not (fn-lgw-stop st)) (<= (fn-lgw-pos st) (len c)))
           (let* ((x (nthcdr (fn-lgw-pos st) c))
                  (scan (fn-lg-scan x (fn-lgw-prev st) unit max))
                  (run (fn-lgw-run c st unit max)))
             (and (equal (mv-nth 0 run) (car scan))
                  (equal (fn-lgw-pos (mv-nth 1 run)) (+ (fn-lgw-pos st) (cdr scan)))
                  (equal (fn-lgw-prev (mv-nth 1 run))
                         (fn-lg-scan-last x (fn-lgw-prev st) unit max))
                  (equal (fn-lgw-count (mv-nth 1 run)) (+ (fn-lgw-count st) (len (car scan))))
                  (equal (fn-lgw-next (mv-nth 1 run))
                         (fn-lgw-next-fold (car scan) (fn-lgw-next st)))
                  (equal (fn-lgw-broken (mv-nth 1 run))
                         (fn-lgs-chain-broken-p x (fn-lgw-prev st) unit max)))))
  :hints (("Goal" :induct (fn-lgw-run c st unit max)
           :expand ((fn-lgw-run c st unit max)
                    (fn-lg-scan (nthcdr (fn-lgw-pos st) c) (fn-lgw-prev st) unit max)
                    (fn-lg-scan-last (nthcdr (fn-lgw-pos st) c) (fn-lgw-prev st) unit max))
           :in-theory (disable fn-lgw-step fn-lgw-window fn-lg-entry-okp fn-lg-slice
                               fn-lgs-claimed-prev fn-lg-scan fn-lg-scan-last fn-lg-trailer
                               fn-lg-pad-len fn-lg-slice-record fn-lg-declared-len
                               fn-lgs-chain-broken-p fn-lgw-broken-slice-p fn-lgt-txid
                               fn-lgw-next-after-one fn-lgw-next-fold-is-next-after))))


; -----------------------------------------------------------------------------
; KEYSTONE: the run from the start is the open (the recovered kernel).

(defthm fn-lgw-next-after-of-nfix
  (equal (fn-lgt-next-after records (nfix floor)) (fn-lgt-next-after records floor)))

(defthm fn-lgw-next-after-of-non-natural
  (implies (not (natp floor))
           (equal (fn-lgt-next-after records floor) (fn-lgt-next-after records 0))))

(defthm fn-lgw-run-is-the-open
  (let* ((run (fn-lgw-run c (fn-lgw-start genesis floor) unit max))
         (ks (fn-lgt-recover c genesis unit max floor)))
    (and (equal (mv-nth 0 run) (fn-lgk-committed ks))
         (equal (fn-lgw-kernel (mv-nth 1 run)) (fn-lgc-of ks))
         (equal (fn-lgw-broken (mv-nth 1 run)) (fn-lgs-chain-broken-p c genesis unit max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgt-recover fn-lgk-recover fn-lgc-of)
                           (fn-lgw-run fn-lg-scan fn-lg-scan-last fn-lgs-chain-broken-p fn-lgc-make
                            fn-lgt-next-after fn-lgw-run-is-the-scan))
           :use ((:instance fn-lgw-run-is-the-scan (st (fn-lgw-start genesis floor)))))))

; The same kernel as the whole-segment open's: over a segment read as the
; string S (fn-lgc-open, the host's open before this book), the stream over S's
; octets answers fn-lgc-open's records and kernel.
(defthm fn-lgw-run-is-fn-lgc-open
  (let ((run (fn-lgw-run (fn-lgd-octets s) (fn-lgw-start genesis floor) unit max)))
    (and (equal (mv-nth 0 run) (mv-nth 0 (fn-lgc-open s genesis unit max floor)))
         (equal (fn-lgw-kernel (mv-nth 1 run)) (mv-nth 1 (fn-lgc-open s genesis unit max floor)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-lgw-run-is-the-open (c (fn-lgd-octets s)))
                 (:instance fn-lgc-open-refines)
                 (:instance fn-lg-open-kernel-is-the-recovered-kernel)))))

(in-theory (disable fn-lgw-step fn-lgw-window fn-lgw-run fn-lgw-kernel))
