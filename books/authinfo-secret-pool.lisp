; Concrete bounded AUTHINFO material. TX scratch must be exclusively owned;
; it is cleared by the caller before formatting or transmitting a reply.
(in-package "ACL2")
(include-book "authinfo-secret")
(include-book "pool-block")
(include-book "pool-copy")
(include-book "nntp-grammar")
(fn2-book-layer :e)

(defconst *fn2-authinfo-pass-max*
  (- *fn2-nntp-line-cap* (+ (length "AUTHINFO PASS ") 2)))

(defun fn2-authinfo-token-span-p (slot gen off len kind id ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (and (natp off) (posp len) (<= len *fn2-authinfo-pass-max*)
      (mv-let (bad ctl need)
          (fn2-gram-line-scan len off 0 #x80 #xbf nil nil slot gen kind id ogen fn2-pool)
        (and (not bad) (not ctl) (equal need 0)
             (equal (fn2-gram-skip len off (+ off len) nil slot gen kind id ogen fn2-pool)
                    (+ off len))))))

(defconst *fn2-authinfo-tag-size* (length *fn2-authinfo-tag-octets*))
(defconst *fn2-authinfo-prefix-size* (+ *fn2-authinfo-tag-size* *fn2-authinfo-salt-octets*))

(defun fn2-authinfo-stage-preimage (sslot sgen soff sk si sg rslot rgen roff len rk ri rg tslot tgen start kind id gen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (b* (((unless (and (natp soff) (natp roff) (natp start) (posp len) (<= len *fn2-authinfo-pass-max*)
                     (or (not (equal tslot sslot)) (<= (+ soff *fn2-authinfo-salt-octets*) start))
                     (not (equal tslot rslot))))
        (mv :bounds 0 fn2-pool))
       ((unless (equal (fn2-pool-fill-value tslot fn2-pool) start))
        (mv :bounds 0 fn2-pool))
       ((mv code fn2-pool) (fn2-pool-write tslot tgen start (+ 64 (length *fn2-authinfo-tag-text*)) kind id gen fn2-pool))
       ((unless (eq code :ok)) (mv :bounds 0 fn2-pool))
       ((mv code fn2-pool) (fn2-pool-append-text 0 *fn2-authinfo-tag-text* tslot tgen kind id gen fn2-pool))
       ((unless (eq code :ok)) (mv :bounds 0 fn2-pool))
       ((mv code fn2-pool) (fn2-rd-copy *fn2-authinfo-salt-octets* sslot sgen soff sk si sg
                                      tslot tgen (+ start *fn2-authinfo-tag-size*) kind id gen fn2-pool))
       ((unless (eq code :ok)) (mv :bounds 0 fn2-pool))
       ((mv code fn2-pool) (fn2-rd-copy len rslot rgen roff rk ri rg
                                      tslot tgen (+ start *fn2-authinfo-prefix-size*) kind id gen fn2-pool)))
    (mv (if (eq code :ok) :ok :bounds) (+ *fn2-authinfo-prefix-size* len) fn2-pool)))
(fn2-pool-preserves fn2-authinfo-stage-preimage
 (sslot sgen soff sk si sg rslot rgen roff len rk ri rg tslot tgen start kind id gen fn2-pool) :position 2 :rows nil)
(defthm fn2-authinfo-stage-preimage-natp
 (natp (mv-nth 1 (fn2-authinfo-stage-preimage
                  sslot sgen soff sk si sg rslot rgen roff len rk ri rg tslot tgen start kind id gen fn2-pool)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn2-authinfo-stage-preimage))))
(in-theory (disable fn2-authinfo-stage-preimage))

;; Visit all 32 digest octets, including on a mismatch. This is an ACL2
;; work statement; it does not claim a native constant-time side channel.
(defun fn2-authinfo-verifier-mismatch (i acc digest slot gen off kind id ogen fn2-digests fn2-pool)
  (declare (xargs :stobjs (fn2-digests fn2-pool)
                  :measure (nfix (- *fn2-authinfo-verifier-octets* (nfix i)))
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-digest-rowp digest fn2-digests)
                              (natp i) (natp off) (natp acc))))
  (if (>= (nfix i) *fn2-authinfo-verifier-octets*) (nfix acc)
    (mv-let (code byte) (fn2-pool-read slot gen (+ off i) kind id ogen fn2-pool)
      (let* ((expected (fn2-fc-word-byte (nfix (fn2-digest-word digest (floor (nfix i) 4) fn2-digests))
                                        (mod (nfix i) 4)))
             (diff (if (eq code :ok) (logxor (nfix byte) expected) 256)))
        (fn2-authinfo-verifier-mismatch (+ 1 i) (logior (nfix acc) (nfix diff))
                                       digest slot gen off kind id ogen fn2-digests fn2-pool)))))
(in-theory (disable fn2-authinfo-verifier-mismatch))
