; FNCR located fields and resumable canonical group definitions. The frame
; buffer is retained under the actual issuer's custody across every yield.
(in-package "ACL2")
(include-book "consumer-remote-ingress")
(include-book "frame-buffer")
(include-book "frame-digest-buffer")

(defun fn-crb-byte (at end fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (if (and (natp at) (natp end) (< at end) (<= end (fn-octets-len fn-octets)))
     (fn-octets-get at fn-octets) 0))

; Up to eight bytes per integer, independent of the frame's allocation.
(defun fn-crb-uint (width at end fn-octets)
 (declare (xargs :stobjs fn-octets :guard (and (natp width) (<= width 8))
                  :measure (nfix width)))
 (if (zp width) 0
  (+ (* (expt 256 (1- width)) (fn-crb-byte at end fn-octets))
     (fn-crb-uint (1- width) (1+ (nfix at)) end fn-octets))))

(defun fn-crb-window (at end width max fn-octets)
 (declare (xargs :stobjs fn-octets :guard (and (natp width) (<= width 8))))
 (if (not (and (natp at) (natp end) (<= end (fn-octets-len fn-octets))
               (<= (+ at width) end))) '(:refused :fields)
  (let ((n (fn-crb-uint width at end fn-octets)))
   (if (or (< (nfix max) n) (< end (+ at width n))) '(:refused :fields)
    (list :window (+ at width) (+ at width n))))))

(defun fn-crb-copy-window (window fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let ((at (fn-cp-nth 1 window)) (end (fn-cp-nth 2 window)))
  (if (and (natp at) (natp end) (<= at end) (<= end (fn-octets-len fn-octets)))
      (fn-oct-slice-list at end fn-octets) nil)))

; Fixed6 cursor: tag, field index, offset, payload end, reverse values, G.
; The group blob is located and is never copied by a field tick.
(defun fn-crb-fields-state (index at end values g)
 (declare (xargs :guard t))
 (list :remote-fields index at end values g))

(defun fn-crb-open-with (digest g fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let ((opened (fn-frb-decode digest (fn-frame-specs-width (fn-cr-spec g)) fn-octets)))
  (if (and (fn-frame-result-okp opened)
           (equal (fn-frame-result-magic opened) *fn-cr-magic*)
           (equal (fn-frame-result-version opened) *fn-cr-version*)
           (equal (fn-frame-result-kind opened) 1))
      (list :yield (fn-crb-fields-state 0 10 (+ 10 (nfix (fn-frame-result-payload opened))) nil g))
    '(:refused :frame))))

(defun fn-crb-open (g fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (fn-crb-open-with
   (fn-frame-digest-range nil 0 (nfix (- (fn-octets-len fn-octets) 32)) fn-octets)
   g fn-octets))

(defun fn-crb-frame-reference (digest g octets)
 (declare (xargs :guard t))
 (let ((opened (fn-frame-decode octets digest (fn-frame-specs-width (fn-cr-spec g)))))
  (if (and (fn-frame-result-okp opened)
           (equal (fn-frame-result-magic opened) *fn-cr-magic*)
           (equal (fn-frame-result-version opened) *fn-cr-version*)
           (equal (fn-frame-result-kind opened) 1))
      (list :yield (fn-crb-fields-state 0 10 (+ 10 (len (fn-frame-result-payload opened))) nil g))
    '(:refused :frame))))

(defthm fn-crb-open-with-is-fncr-frame-reference
 (implies (fn-octets-p fn-octets)
  (equal (fn-crb-open-with digest g fn-octets)
         (fn-crb-frame-reference digest g fn-octets)))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-frb-decode-is-frame-decode
                                 (max-payload (fn-frame-specs-width (fn-cr-spec g))))
          :in-theory (e/d (fn-crb-open-with fn-crb-frame-reference fn-frb-of)
                          (fn-frame-decode fn-frb-decode fn-frame-result-magic
                           fn-frame-result-version fn-frame-result-kind
                           fn-frame-result-payload fn-frame-result-okp
                           fn-cr-spec fn-frame-specs-width fn-crb-fields-state)))))

; Only operation-specific fixed-width tail decisions. Group validity is the
; separately funded producer's result, never revalidated here.
(defun fn-crb-tailp (request)
 (declare (xargs :guard t))
 (let ((op (fn-cp-nth 1 request)) (cursor (fn-cp-nth 6 request))
       (seconds (fn-cp-nth 7 request)))
  (case op
   ((:register :rebase :poll :position :status :unregister)
    (and (null cursor) (equal seconds 0)))
   (:wait (and (null cursor) (fn-cwait-secondsp seconds)))
   (:ack (and (equal seconds 0)
              (fn-cbor-at-mostp cursor *fn-cp-max-token*)
              (eq (fn-cp-nth 0 (fn-cp-cursor-decode cursor)) :ok)
              (equal (fn-cp-nth 4 request)
                     (fn-cp-nth 3 (fn-cp-nth 1 (fn-cp-cursor-decode cursor))))))
   (otherwise nil))))

(defun fn-crb-fields-tick (s fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let ((index (fn-cp-nth 1 s)) (at (fn-cp-nth 2 s)) (end (fn-cp-nth 3 s))
       (values (fn-cp-nth 4 s)) (g (fn-cp-nth 5 s)))
  (cond
   ((not (and (natp index) (natp at) (natp end) (<= at end)
              (<= end (fn-octets-len fn-octets)))) '(:refused :fields))
   ((equal index 7)
    (if (not (and (equal at end) (fn-cbor-at-mostp values 7) (true-listp values))) '(:refused :fields)
     (let* ((v (revappend values nil))
            (r (list :remote-consumer (fn-cp-nth 0 v) (fn-cp-nth 1 v)
                      (fn-cp-nth 2 v) (fn-cp-nth 3 v) (fn-cp-nth 4 v)
                      (fn-cp-nth 5 v) (fn-cp-nth 6 v))))
      (if (and (fn-cre-envelopep r) (fn-crb-tailp r)) (list :located r) '(:refused :request)))))
   ((equal index 0)
    (let ((code (fn-crb-byte at end fn-octets)))
     (if (and (< at end) (posp code) (<= code 8))
         (list :yield (fn-crb-fields-state 1 (1+ at) end
                           (list (fn-cp-nth (1- code) *fn-cr-operations*)) g))
       '(:refused :fields))))
   ((equal index 6)
    (if (< end (+ at 8)) '(:refused :fields)
     (list :yield (fn-crb-fields-state 7 (+ at 8) end
                    (cons (fn-crb-uint 8 at end fn-octets) values) g))))
   ((<= index 5)
    (let* ((window (fn-crb-window at end (if (equal index 1) 2 4)
                  (case index (1 *fn-frame-max-text*) (2 *fn-ncl-max-secret*)
                   (3 *fn-cp-max-id*) (4 (+ 5 (* (+ 5 *fn-record-max-group-name*) (nfix g))))
                   (otherwise *fn-cp-max-token*)) fn-octets)))
     (if (not (eq (fn-cp-nth 0 window) :window)) window
      (let* ((value (if (equal index 4)
                         (list :remote-group-window (fn-cp-nth 1 window) (fn-cp-nth 2 window))
                       (fn-crb-copy-window window fn-octets)))
             (value (if (and (equal index 5) (equal value '(0))) nil value)))
       (if (and (equal index 1) (not (fn-frame-textp value))) '(:refused :fields)
        (list :yield (fn-crb-fields-state (1+ index) (fn-cp-nth 2 window) end (cons value values) g)))))))
   (t '(:refused :fields)))))

; One canonical CBOR head, before any group-name allocation or grammar scan.
(defun fn-crb-cbor-head (at end major max fn-octets)
 (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-crb-byte fn-crb-uint floor mod)))))
 (if (not (and (natp at) (natp end) (< at end) (<= end (fn-octets-len fn-octets))))
     '(:refused :query)
  (let* ((byte (nfix (fn-crb-byte at end fn-octets))) (additional (mod byte 32))
         (width (case additional (24 1) (25 2) (26 4) (otherwise 0)))
         (n (if (< additional 24) additional
                (nfix (fn-crb-uint width (1+ at) end fn-octets)))))
   (if (and (equal (floor byte 32) major) (<= additional 26)
            (<= (+ 1 at width) end) (<= n (nfix max))
            (fn-cbor-canonical-argumentp additional n))
       (list :head n (+ 1 at width)) '(:refused :query)))))

; Fixed8 group cursor, tied to the retained frame's actual caller source.
(defun fn-crb-groups-state (source request at end remaining prev rev)
 (declare (xargs :guard t))
 (list :remote-groups source request at end remaining prev rev))

(defun fn-crb-groups-begin (request source g fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let* ((window (fn-cp-nth 5 request)) (at (fn-cp-nth 1 window)) (end (fn-cp-nth 2 window))
        (op (fn-cp-nth 1 request)))
  (if (not (and (eq (fn-cp-nth 0 window) :remote-group-window)
                 (natp at) (natp end) (< at end) (<= end (fn-octets-len fn-octets))))
      '(:refused :query)
   (if (member-eq op '(:register :rebase))
       (let ((head (fn-crb-cbor-head at end 0 g fn-octets)))
        (if (and (eq (fn-cp-nth 0 head) :head) (posp (fn-cp-nth 1 head)))
            (list :yield (fn-crb-groups-state source request (fn-cp-nth 2 head) end
                               (fn-cp-nth 1 head) nil nil)) '(:refused :query)))
     (if (and (equal end (1+ at)) (equal (fn-crb-byte at end fn-octets) 0))
         (list :request (list :remote-consumer op (fn-cp-nth 2 request)
                     (fn-cp-nth 3 request) (fn-cp-nth 4 request) nil
                     (fn-cp-nth 6 request) (fn-cp-nth 7 request)))
       '(:refused :query))))))

; One at-most-256-octet group per tick; one spine cell per reversal tick.
; Canonical order simultaneously forbids duplicate definitions in linear
; total work. It is the stored remote query grammar, not a table-size cap.
(defun fn-crb-groups-tick (s current-source fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let ((source (fn-cp-nth 1 s)) (request (fn-cp-nth 2 s)) (at (fn-cp-nth 3 s))
       (end (fn-cp-nth 4 s)) (remaining (nfix (fn-cp-nth 5 s)))
       (prev (fn-cp-nth 6 s)) (rev (fn-cp-nth 7 s)))
  (cond
   ((not (equal source current-source)) '(:refused :frame-source-changed))
   ((not (and (natp at) (natp end) (<= at end) (<= end (fn-octets-len fn-octets))))
    '(:refused :query))
   ((zp remaining)
    (if (not (equal at end)) '(:refused :query)
     (list :groups-ready request rev source)))
   (t
    (let* ((head (fn-crb-cbor-head at end 2 *fn-record-max-group-name* fn-octets))
           (size (nfix (fn-cp-nth 1 head))) (next (nfix (fn-cp-nth 2 head))))
     (if (not (and (eq (fn-cp-nth 0 head) :head) (posp size) (<= (+ next size) end)))
         '(:refused :query)
      (let ((name (fn-crb-copy-window (list :window next (+ next size)) fn-octets)))
       (if (not (and (fn-record-group-name-octetsp name)
                      (or (null prev) (and (lexorder prev name) (not (equal prev name))))))
           '(:refused :query)
        (list :yield (fn-crb-groups-state source request (+ next size) end
                             (1- remaining) name (cons name rev)))))))))))

; Group reversal is deliberately a separate producer; no final wholequery
; REVAPPEND is hidden in a served completion step.
(defun fn-crb-reverse-tick (rev built)
 (declare (xargs :guard t))
 (if (consp rev) (list :yield (cdr rev) (cons (car rev) built))
  (list :groups built)))

(in-theory (disable fn-crb-byte fn-crb-uint fn-crb-window fn-crb-copy-window
 fn-crb-fields-state fn-crb-open-with fn-crb-open fn-crb-frame-reference fn-crb-tailp fn-crb-fields-tick fn-crb-cbor-head
 fn-crb-groups-state fn-crb-groups-begin fn-crb-groups-tick fn-crb-reverse-tick))
