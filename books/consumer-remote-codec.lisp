; Authenticated remote consumer protocol. CNS-011 / PKT-255.
; FNCR is a distinct request envelope: it never enters FNCT owner dispatch.
; The protected-channel fact is observed by the native TLS adapter. Neither
; the frame trailer nor this grammar proves TLS or authenticates an account.
(in-package "ACL2")
(include-book "consumer-wait-codec")

(defconst *fn-cr-magic* '(70 78 67 82)) ; FNCR
(defconst *fn-cr-version* 1)
(defconst *fn-cr-operations*
  '(:register :rebase :poll :wait :position :status :ack :unregister))

; G is the separately admitted consumer-query group count. Group definitions
; have their own blob; the 64-octet cursor query ID is never their encoding.
(defun fn-cr-spec (g)
  (declare (xargs :guard t))
  (list (cons :enum *fn-cr-operations*)
        :text (cons :blob *fn-ncl-max-secret*)
        (cons :blob *fn-cp-max-id*)
        (cons :blob (+ 5 (* (+ 5 *fn-record-max-group-name*) (nfix g))))
        (cons :blob *fn-cp-max-token*) :nat))

(defun fn-cr-read-bound (g)
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* (fn-frame-specs-width (fn-cr-spec g))))

(defun fn-cr-groupsp (groups g)
  (declare (xargs :guard t))
  (and (true-listp groups) (consp groups) (<= (len groups) (nfix g))
       (fn-record-groupsp (fn-nctrl-group-strings groups))
       (equal (fn-nctrl-group-octets (fn-nctrl-group-strings groups)) groups)))

; Fixed tuple, including empty unused fields. Strict unused fields remove
; alternate interpretations; neither principal nor query/view version is
; accepted from the request. Those belong to committed authority context.
(defun fn-cr-requestp (request g)
  (declare (xargs :guard t))
  (let ((op (fn-cp-nth 1 request))
        (login (fn-cp-nth 2 request))
        (secret (fn-cp-nth 3 request))
        (consumer (fn-cp-nth 4 request))
        (groups (fn-cp-nth 5 request))
        (cursor (fn-cp-nth 6 request))
        (seconds (fn-cp-nth 7 request)))
    (and (true-listp request) (equal (len request) 8)
         (eq (car request) :remote-consumer)
         (fn-frame-textp login)
         (fn-cbor-octet-listp login) (fn-ncl-secretp secret)
         (fn-cp-idp consumer)
         (case op
           ((:register :rebase)
            (and (fn-cr-groupsp groups g) (null cursor) (equal seconds 0)))
           ((:poll :position :status :unregister)
            (and (null groups) (null cursor) (equal seconds 0)))
           (:wait (and (null groups) (null cursor) (fn-cwait-secondsp seconds)))
           (:ack
            (and (null groups) (equal seconds 0)
                 (eq (car (fn-cp-cursor-decode cursor)) :ok)
                 (equal consumer
                        (fn-cp-nth 3 (fn-cp-nth 1
                                      (fn-cp-cursor-decode cursor))))))
           (otherwise nil)))))

(defun fn-cr-seal (payload)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-frame-max-payload*))) :bad
    (let ((protected (fn-frame-protected *fn-cr-magic* *fn-cr-version*
                                         1 payload)))
      (append protected (fn-frame-trailer protected)))))

(defun fn-cr-request-encode (request g)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-cr-requestp
                                                           fn-cr-spec)))))
  (if (not (fn-cr-requestp request g)) :bad
    (let* ((groups (fn-cp-nth 5 request))
           (values (list (fn-cp-nth 1 request) (fn-cp-nth 2 request)
                         (fn-cp-nth 3 request) (fn-cp-nth 4 request)
                         (if groups (fn-nctrl-groups-encode groups) (list 0))
                         (or (fn-cp-nth 6 request) (list 0))
                         (fn-cp-nth 7 request)))
           (spec (fn-cr-spec g)))
      (if (not (and (fn-frame-spec-listp spec)
                    (fn-frame-values-okp spec values))) :bad
        (fn-cr-seal (fn-frame-fields-octets spec values))))))

; This count check precedes parsing any group name. The enclosing frame
; preflight funds bytes before digest/field parsing or list allocation.
(defun fn-cr-groups-decode (bytes g)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp bytes)) (fn-record-parse-error :groups)
    (let ((counted (fn-record-read-uint bytes)))
      (if (and (fn-record-parse-okp counted)
               (posp (fn-record-parse-value counted))
               (<= (fn-record-parse-value counted) (nfix g)))
          (fn-nctrl-groups-decode bytes)
        (fn-record-parse-error :groups)))))

(defun fn-cr-request-payload-decode (payload g)
  (declare (xargs :guard t :guard-hints (("Goal" :in-theory (disable fn-cr-spec)))))
  (if (not (and (fn-cbor-octet-listp payload)
                (fn-frame-spec-listp (fn-cr-spec g)))) (list :refused :fields)
    (let ((parsed (fn-frame-fields-parse (fn-cr-spec g) payload)))
      (if (not (fn-frame-parse-okp parsed)) (list :refused :fields)
        (let* ((v (fn-frame-parse-value parsed))
               (groups-bytes (fn-cp-nth 4 v))
               (groups (and (not (equal groups-bytes (list 0)))
                            (fn-cr-groups-decode groups-bytes g)))
               (request (list :remote-consumer
                              (fn-cp-nth 0 v) (fn-cp-nth 1 v)
                              (fn-cp-nth 2 v) (fn-cp-nth 3 v)
                              (and groups (fn-record-parse-value groups))
                              (if (equal (fn-cp-nth 5 v) (list 0)) nil
                                (fn-cp-nth 5 v))
                              (fn-cp-nth 6 v))))
          (if (and (or (equal groups-bytes (list 0)) (fn-record-parse-okp groups))
                   (fn-cr-requestp request g))
              request
            (list :refused :request)))))))

(defun fn-cr-request-decode (octets protectedp g)
  (declare (xargs :guard t))
  (cond
   ((not (eq protectedp t)) (list :refused :protected-channel))
   ((not (and (fn-cbor-at-mostp octets (fn-cr-read-bound g))
              (fn-cbor-octet-listp octets))) (list :refused :size))
   (t
    (let ((opened (fn-frame-decode
                   octets (fn-frame-trailer (fn-frame-protected-prefix octets))
                   (fn-frame-specs-width (fn-cr-spec g)))))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-cr-magic*)
               (equal (fn-frame-result-version opened) *fn-cr-version*)
               (equal (fn-frame-result-kind opened) 1))
          (fn-cr-request-payload-decode (fn-frame-result-payload opened) g)
        (list :refused :frame))))))

; Definition lemmas are scaffolding, never the claimed authority theorem.
(defthm fn-cr-unprotected-request-refuses-by-definition
  (implies (not (eq protectedp t))
           (equal (fn-cr-request-decode octets protectedp g)
                  '(:refused :protected-channel)))
  :hints (("Goal" :in-theory '(fn-cr-request-decode))))

(defthm fn-cr-payload-admission-is-a-consumer-request
  (let ((answer (fn-cr-request-payload-decode payload g)))
    (implies (eq (car answer) :remote-consumer)
             (fn-cr-requestp answer g)))
  :hints (("Goal" :in-theory (e/d (fn-cr-request-payload-decode)
                                  (fn-cr-requestp fn-cr-spec
                                   fn-frame-fields-parse fn-cr-groups-decode
                                   fn-record-parse-value fn-frame-parse-value)))))

(defthm fn-cr-requestp-operation-by-definition
  (implies (fn-cr-requestp request g)
           (member-eq (fn-cp-nth 1 request) *fn-cr-operations*))
  :hints (("Goal" :in-theory '(fn-cr-requestp member-equal))))

(defthm fn-cr-decoded-request-is-protected-and-consumer-only
  (let ((answer (fn-cr-request-decode octets protectedp g)))
    (implies (eq (car answer) :remote-consumer)
             (and (equal protectedp t)
                  (fn-cr-requestp answer g)
                  (member-eq (fn-cp-nth 1 answer) *fn-cr-operations*))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-cr-requestp-operation-by-definition
                            (request (fn-cr-request-decode octets protectedp g))))
           :in-theory
           (union-theories
            '(fn-cr-request-decode fn-cr-payload-admission-is-a-consumer-request
              fn-cr-requestp-operation-by-definition)
            (theory 'minimal-theory)))))

(in-theory (disable fn-cr-spec fn-cr-read-bound fn-cr-groupsp
                    fn-cr-requestp fn-cr-request-encode fn-cr-groups-decode
                    fn-cr-request-payload-decode fn-cr-request-decode))
