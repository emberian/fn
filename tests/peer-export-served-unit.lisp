; The composed owner FNCT carrier, upload/transaction and raw export path.
; No model rows, predicted stable cuts or readiness flags are installed.
(in-package "ACL2")
(include-book "../books/cns")
(include-book "../books/owed-authority")
(include-book "../books/assembly-attach")

(defconst *fn2-pesu-profile*
  (put-assoc-equal :origin-lineage 101
   (put-assoc-equal :origin-domain 202
    (put-assoc-equal :origin-incarnation 303
     (put-assoc-equal :history-id 257
      (put-assoc-equal :history-incarnation 65537
       (put-assoc-equal :extent-slots 128
        (put-assoc-equal :groups '(("local.test" . 1)) *fn2-oa-profile*))))))))
(defconst *fn2-pesu-mid* "<export@example.invalid>")
(defun fn2-pesu-article (body)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets
   (list "From: export@example.invalid" "Subject: export" "Newsgroups: local.test"
         "Message-ID: <export@example.invalid>" "" body)))
(defun fn2-pesu-request (history incarnation cut resume max)
  (declare (xargs :verify-guards nil))
  (fnc-request :evidence-page
               (list (cons 'history history) (cons 'incarnation incarnation)
                     (cons 'cut cut) (cons 'resume resume) (cons 'max-items max))))
; One actual admitted owner control connection, keeping the adapter's device
; and previous clients. Frames arrive separately; no STOP changes the core.
(defun fn2-pesu-session (cap frames clients store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv ac fn2-core) (fn2-oa-admit cap fn2-core))
       ((unless (eq ac :ok)) (mv ac nil clients store fn2-core))
       (clients (append clients
                        (list (mv-let (bytes sizes) (fn2-oa-wire frames)
                                (list bytes sizes nil nil)))))
       ((mv status clients store fn2-core)
        (fn2-cw-loop 40000 0 (len clients) clients store fn2-core)))
    (mv status (car (nth cap (fn2-cw-results clients))) clients store fn2-core)))

; Independent wire reading: fixed-width big endian for the page envelope;
; schema IDs/name lengths are LEB128, digest is tag 1 followed by exactly 32 octets. No export
; decoder or identity-entry codec is used to judge what the server emitted.
(defun fn2-pesu-be (n xs)
  (declare (xargs :verify-guards nil))
  (fnc-be-value (take n xs) 0))
(defun fn2-pesu-entry (xs)
  (declare (xargs :verify-guards nil))
  (b* (((mv ns r0) (fnca-leb xs 0 0))
       ((mv nl r1) (fnca-leb r0 0 0))
       ((unless (and (natp ns) (natp nl) (<= (+ nl 35) (len r1)))) nil)
       (name (take nl r1)) (r2 (nthcdr nl r1))
       (profile (nth 0 r2)) (algorithm (nth 1 r2))
       (digest (take 33 (nthcdr 2 r2)))
       ((unless (equal (car digest) 1)) nil)
       ((mv lineage r3) (fnca-leb (nthcdr 35 r2) 0 0))
       ((mv domain r4) (fnca-leb r3 0 0))
       ((mv incarnation r5) (fnca-leb r4 0 0))
       ((mv occurrence r6) (fnca-leb r5 0 0))
       ((mv kind r7) (fnca-leb r6 0 0))
       ((mv issuer rest) (fnca-leb r7 0 0)))
    (and (natp lineage) (natp domain) (natp incarnation) (natp occurrence)
         (natp kind) (natp issuer) (null rest)
         (list ns name profile algorithm digest lineage domain incarnation occurrence kind issuer))))
(defun fn2-pesu-entries (count xs)
  (declare (xargs :verify-guards nil :measure (nfix count)))
  (if (zp count) (and (null xs) (list :ok nil nil))
    (b* (((unless (<= 2 (len xs))) nil)
         (n (fn2-pesu-be 2 xs))
         ((unless (and (< 0 n) (<= (+ 2 n) (len xs)))) nil)
         (raw (take n (nthcdr 2 xs)))
         (entry (fn2-pesu-entry raw))
         (more (fn2-pesu-entries (- count 1) (nthcdr (+ 2 n) xs))))
      (and entry more
           (list :ok (cons entry (nth 1 more)) (cons raw (nth 2 more)))))))
; (:page CUT STOP NEXT ENTRIES RAW-ENTRIES HISTORY INCARNATION), only an accepted kind28 frame.
(defun fn2-pesu-page (wire)
  (declare (xargs :verify-guards nil))
  (b* ((frame (fn2-fnct-open (fnc-frame-extent wire) 8192))
       ((unless (and (eq (car frame) :ok) (equal (nth 1 frame) 28))) nil)
       (p (nth 2 frame))
       ; class accepted, empty reason, four-octet result extent
       ((unless (and (<= 7 (len p)) (equal (take 3 p) '(0 0 0))
                     (equal (+ 7 (fn2-pesu-be 4 (nthcdr 3 p))) (len p)))) nil)
       (r (nthcdr 7 p))
       ((unless (and (<= 34 (len r)) (equal (take 3 r) '(1 1 0)))) nil)
       (history (fn2-pesu-be 8 (nthcdr 3 r)))
       (incarnation (fn2-pesu-be 8 (nthcdr 11 r)))
       (cut (fn2-pesu-be 8 (nthcdr 19 r))) (stop (nth 27 r))
       (nl (fn2-pesu-be 2 (nthcdr 28 r)))
       ((unless (and (member stop '(0 1)) (<= nl 400) (<= (+ 34 nl) (len r)))) nil)
       (next (take nl (nthcdr 30 r)))
       (count (fn2-pesu-be 2 (nthcdr (+ 30 nl) r)))
       (el (fn2-pesu-be 2 (nthcdr (+ 32 nl) r)))
       ((unless (and (<= el 4096) (equal (+ 34 nl el) (len r)))) nil)
       (entries (fn2-pesu-entries count (nthcdr (+ 34 nl) r))))
    (and entries (list :page cut stop next (nth 1 entries) (nth 2 entries) history incarnation))))
(defun fn2-pesu-after-frame (wire)
  (declare (xargs :verify-guards nil))
  (nthcdr (len (fnc-frame-extent wire)) wire))
(defun fn2-pesu-refused (wire)
  (declare (xargs :verify-guards nil))
  (eq (car (fnc-reply 'evidence-page wire)) :refused))

; Max-one pagination follows only the cut and exact raw NEXT returned by
; the actual server. Three requests suffice for two rows plus scan-end.
(defun fn2-pesu-scan (fuel cap history incarnation cut resume clients store fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv nil cap clients store fn2-core)
    (b* (((mv status wire clients store fn2-core)
          (fn2-pesu-session cap (list (fn2-pesu-request history incarnation cut resume 1)) clients store fn2-core))
         (page (fn2-pesu-page wire))
         ((unless (and (eq status :quiet) page (<= (len (nth 4 page)) 1)
                       (or (equal cut 0) (equal cut (nth 1 page)))
                       (equal (nth 6 page) 257) (equal (nth 7 page) 65537)
                       (or (equal history 0) (equal history (nth 6 page)))
                       (or (equal incarnation 0) (equal incarnation (nth 7 page)))
                       (or (atom (nth 5 page))
                           (equal (nth 3 page) (car (last (nth 5 page)))))))
          (mv nil (+ 1 cap) clients store fn2-core))
         ((when (equal (nth 2 page) 0))
          (mv (list page) (+ 1 cap) clients store fn2-core))
         ((unless (and (consp (nth 3 page)) (not (equal resume (nth 3 page)))))
          (mv nil (+ 1 cap) clients store fn2-core))
         ((mv rest nextcap clients store fn2-core)
          (fn2-pesu-scan (- fuel 1) (+ 1 cap) (nth 6 page) (nth 7 page) (nth 1 page) (nth 3 page) clients store fn2-core)))
      (mv (and rest (cons page rest)) nextcap clients store fn2-core))))
(defun fn2-pesu-scan-entries (pages)
  (declare (xargs :verify-guards nil))
  (if (atom pages) nil
    (append (nth 4 (car pages)) (fn2-pesu-scan-entries (cdr pages)))))
(defun fn2-pesu-original-p (rows firstpos conflictpos)
  (declare (xargs :verify-guards nil))
  (let* ((name (fnca-octets *fn2-pesu-mid*))
         (a (list 1 name 1 1 (cons 1 (fn-blake3 (fn2-pesu-article "first"))) 101 202 303 firstpos 0 2))
         (b (list 1 name 1 1 (cons 1 (fn-blake3 (fn2-pesu-article "conflict"))) 101 202 303 conflictpos 0 2)))
    (and (equal (len rows) 2) (no-duplicatesp-equal rows)
         (member-equal a rows) (member-equal b rows))))

; Replace only the observed lineage, preserving every other original byte.
(defun fn2-pesu-unknown-origin (raw)
  (declare (xargs :verify-guards nil))
  (b* (((mv & r0) (fnca-leb raw 0 0))
       ((mv namelen r1) (fnca-leb r0 0 0)))
    (update-nth (+ (- (len raw) (len r1)) (nfix namelen) 35) 99 raw)))

(defun fn2-pesu-run ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* ((fn2-core (fn2-init-executor *fn2-pesu-profile* :echo nil fn2-core))
           ((mv epoch-code fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv ps pop clients store fn2-core)
            (fn2-pesu-session 0
              (list (fnc-append 10 (fn2-pesu-article "first"))
                    (fnc-append 11 (fn2-pesu-article "first"))
                    (fnc-append 12 (fn2-pesu-article "conflict"))) nil nil fn2-core))
           (replies (fnc-replies '(append append append) pop))
           (firstpos (car (nth 2 (car replies))))
           ((mv pages cap clients store fn2-core)
            (fn2-pesu-scan 3 1 0 0 0 nil clients store fn2-core))
           ((unless (and pages (natp firstpos)))
            (mv (list :population-or-pagination ps replies pages) fn2-core))
           (history (nth 6 (car pages))) (incarnation (nth 7 (car pages)))
           (cut (nth 1 (car pages))) (token (nth 3 (car pages)))
           (rows (fn2-pesu-scan-entries pages))
           (unknown (fn2-pesu-unknown-origin token))
           ((mv fs fullwire clients store fn2-core)
            (fn2-pesu-session cap
              (list (fn2-pesu-request 0 0 0 nil 16)
                    (fn2-pesu-request history incarnation cut '(255) 1)
                    (fn2-pesu-request history incarnation cut unknown 16)
                    (fn2-pesu-request (+ 1 history) incarnation cut token 1)
                    (fn2-pesu-request history (+ 1 incarnation) cut token 1)) clients store fn2-core))
           (full (fn2-pesu-page fullwire))
           (negative (fn2-pesu-after-frame fullwire))
           (unknownwire (fn2-pesu-after-frame negative))
           (unknown-page (fn2-pesu-page unknownwire))
           (cross-history (fn2-pesu-after-frame unknownwire))
           (cross-incarnation (fn2-pesu-after-frame cross-history))
           ; Advance the real published cut by a new accepted article, then
           ; offer the previously issued cut/token. No cut flag is forged.
           ; This owner connection then creates and binds a real nonowner
           ; through authority frames before asking export again.
           ((mv ss stale & & fn2-core)
            (fn2-pesu-session (+ 1 cap)
              (list (fnc-append 13
                      (fn2-cw-crlf-octets
                       '("From: export@example.invalid" "Subject: later" "Newsgroups: local.test"
                         "Message-ID: <later@example.invalid>" "" "later")))
                    (fn2-pesu-request history incarnation cut token 1)
                    (fnca-frame 'principal-create (list (fnca-octets "export-nonowner")))
                    (fnca-frame 'principal-bind (list (fnca-octets "export-nonowner")))
                    (fn2-pesu-request 0 0 0 nil 1)) clients store fn2-core))
           ((mv auth-replies bound-rest)
            (fn2-oa-k30s 2 (fn2-pesu-after-frame (fn2-pesu-after-frame stale))))
           ((mv actual-code actualcut) (fn2-successor-published fn2-core))
           (bound-reply (fnc-reply 'evidence-page bound-rest)))
        (mv
         (if (and (eq epoch-code :ok) (eq ps :quiet) (eq fs :quiet) (eq ss :quiet)
                  (eq (car (nth 0 replies)) :accepted)
                  (eq (car (nth 1 replies)) :refused)
                  (eq (car (nth 2 replies)) :refused)
                  (< firstpos cut) (fn2-pesu-original-p rows firstpos cut)
                  full (equal (nth 6 full) 257) (equal (nth 7 full) 65537)
                  (equal (nth 2 full) 0) (equal (nth 1 full) cut)
                  (equal (nth 4 full) rows)
                  (fn2-pesu-refused negative)
                  (fn2-pesu-refused cross-history) (fn2-pesu-refused cross-incarnation)
                  unknown-page (equal (nth 6 unknown-page) history)
                  (equal (nth 7 unknown-page) incarnation) (equal (nth 1 unknown-page) cut)
                  (subsetp-equal (nth 4 unknown-page) rows)
                  (eq (car (fnc-reply 'append stale)) :accepted)
                  (fn2-pesu-refused (fn2-pesu-after-frame stale))
                  (eq actual-code :ok) (< cut actualcut)
                  (equal (nth 1 (nth 0 auth-replies)) :accepted)
                  (equal (nth 1 (nth 1 auth-replies)) :accepted)
                  (eq (nth 0 bound-reply) :refused) (equal (nth 1 bound-reply) "access")
                  (equal (fn2-core-stop-reason fn2-core) 0))
             t
           (list :served-export-failed replies pages full negative stale auth-replies
                 bound-reply (list actual-code actualcut) (fn2-core-stop-reason fn2-core)))
         fn2-core))
      result)))
(assert-event (equal (fn2-pesu-run) t))

; Two separate initialized nodes execute the same first append and export,
; each with its own adapter device. Local commit position alone cannot name
; an observation: the configured semantic origins must survive on the wire.
(defun fn2-pesu-node-receipt (profile)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (receipt fn2-core)
      (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
           ((mv epoch-code fn2-core)
            (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
              (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
           ((mv status wire & & fn2-core)
            (fn2-pesu-session 0
              (list (fnc-append 10 (fn2-pesu-article "first"))
                    (fn2-pesu-request 0 0 0 nil 16)) nil nil fn2-core))
           (reply (fnc-reply 'append wire))
           (page (fn2-pesu-page (fn2-pesu-after-frame wire))))
        (mv (and (eq epoch-code :ok) (eq status :quiet)
                 (eq (car reply) :accepted) page
                 (equal (nth 2 page) 0) (equal (len (nth 4 page)) 1)
                 (equal (fn2-core-stop-reason fn2-core) 0)
                 (list (car (nth 2 reply)) page)) fn2-core))
      receipt)))
(defconst *fn2-pesu-other-profile*
  (put-assoc-equal :origin-lineage 404
   (put-assoc-equal :origin-domain 505
    (put-assoc-equal :origin-incarnation 606
     (put-assoc-equal :history-id 258
      (put-assoc-equal :history-incarnation 65538 *fn2-pesu-profile*))))))
(defun fn2-pesu-two-nodes ()
  (declare (xargs :verify-guards nil))
  (b* ((a (fn2-pesu-node-receipt *fn2-pesu-profile*))
       (b (fn2-pesu-node-receipt *fn2-pesu-other-profile*))
       (pa (nth 1 a)) (pb (nth 1 b))
       (ra (car (nth 4 pa))) (rb (car (nth 4 pb)))
       (common (list 1 (fnca-octets *fn2-pesu-mid*) 1 1
                     (cons 1 (fn-blake3 (fn2-pesu-article "first"))))))
    (and a b (posp (car a)) (equal (car a) (car b))
         (equal (nth 6 pa) 257) (equal (nth 7 pa) 65537)
         (equal (nth 6 pb) 258) (equal (nth 7 pb) 65538)
         (equal (nth 1 pa) (car a)) (equal (nth 1 pb) (car b))
         (equal ra (append common (list 101 202 303 (car a) 0 2)))
         (equal rb (append common (list 404 505 606 (car b) 0 2)))
         (not (equal ra rb)))))
(assert-event (fn2-pesu-two-nodes))
