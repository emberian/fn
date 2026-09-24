; A finite BP network-trust profile over the durable owner configuration.
; The first implemented boundary is IPv4 loopback.  Its `all-co-resident'
; originator declaration is literal: it does not distinguish local processes.
(in-package "ACL2")
(include-book "bp-native-app")
(include-book "bp-primary")
(include-book "peer-config")
(set-verify-guards-eagerness 0)

(defun fn-bpaj-boundary-rowp (rows name slot value number)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (or (equal (car rows) (fn-cfg-row-make name slot value number))
          (fn-bpaj-boundary-rowp (cdr rows) name slot value number))
    nil))

(defun fn-bpaj-boundary-slot-count (rows name slot)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (+ (if (and (equal (fn-cfg-row-a (car rows)) name)
                  (equal (fn-cfg-row-b (car rows)) slot)) 1 0)
         (fn-bpaj-boundary-slot-count (cdr rows) name slot))
    0))

(defun fn-bpaj-unique-boundary-rowp (rows name slot value number)
  (declare (xargs :guard t))
  (and (equal (fn-bpaj-boundary-slot-count rows name slot) 1)
       (fn-bpaj-boundary-rowp rows name slot value number)))

(defun fn-bpaj-loopback-peerp (name rows listener-port)
  (declare (xargs :guard t))
  (and (fn-cfg-labelp name)
       (let ((peer (fn-cfg-peer-find name rows)))
         (and peer (consp (fn-cfg-peer-transport peer))
              (equal (car (fn-cfg-peer-transport peer)) :bp)))
       (fn-record-uint32p listener-port)
       (natp listener-port)
       (<= listener-port 65535)
       (fn-bpaj-unique-boundary-rowp rows name "bp-trust" "network" 0)
       (fn-bpaj-unique-boundary-rowp rows name "bp-boundary-listener"
                                "127.0.0.1" listener-port)
       (fn-bpaj-unique-boundary-rowp rows name "bp-boundary-source"
                                "127.0.0.1" 0)
       (fn-bpaj-unique-boundary-rowp rows name "bp-boundary-translation" "none" 0)
       (fn-bpaj-unique-boundary-rowp rows name "bp-boundary-originators"
                                "all-co-resident" 0)))

(defun fn-bpaj-loopback-candidates (rows all listener-port)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (let* ((row (car rows))
             (name (fn-cfg-row-a row))
             (rest (fn-bpaj-loopback-candidates
                    (cdr rows) all listener-port)))
        (if (and (equal (fn-cfg-row-b row) "bp-trust")
                 (fn-bpaj-loopback-peerp name all listener-port)
                 (not (member-equal name rest)))
            (cons name rest)
          rest))
    nil))

(defun fn-bpaj-session-principal (cfg channel announced)
  (declare (xargs :guard t))
  (if (not (and (fn-cfgp cfg)
                (true-listp channel) (equal (len channel) 4)
                (equal (car channel) :tcp4)
                (equal (cadr channel) '(127 0 0 1))
                (equal (cadddr channel) '(127 0 0 1))
                (fn-record-uint32p (caddr channel))
                (fn-bpp-eidp announced)))
      (list :refused :channel)
    (let ((names (fn-bpaj-loopback-candidates
                  (fn-cfg-peers (fn-cfg-value cfg))
                  (fn-cfg-peers (fn-cfg-value cfg))
                  (caddr channel))))
      (if (and (consp names) (null (cdr names)))
          (if (fn-bpaj-unique-boundary-rowp
               (fn-cfg-peers (fn-cfg-value cfg)) (car names)
               "transport-bp" (fn-bpaj-eid-text announced) 0)
              (list :admitted (fn-record-string-octets (car names))
                    (fn-cfg-generation cfg))
            (list :refused :eid-mismatch))
        (list :refused (if names :ambiguous-peer :no-trust-profile))))))

(defun fn-bpaj-admitted-principal (answer)
  (declare (xargs :guard t))
  (if (equal (car answer) :admitted) (cadr answer) nil))

(defun fn-bpaj-current-peer-eidp-rows (rows all principal eid)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (let ((name (fn-cfg-row-a (car rows))))
        (or (and (equal (fn-cfg-row-b (car rows)) "bp-trust")
                 (fn-cfg-labelp name)
                 (let ((peer (fn-cfg-peer-find name all)))
                   (and peer
                        (equal (fn-cfg-peer-transport peer) (list :bp eid))))
                 (equal principal (fn-record-string-octets name))
                 (fn-bpaj-unique-boundary-rowp all name "bp-trust" "network" 0)
                 (fn-bpaj-unique-boundary-rowp all name "transport-bp" eid 0))
            (fn-bpaj-current-peer-eidp-rows (cdr rows) all principal eid)))
    nil))

; A receipt uses the durable peer name and generation stamped at reception.
; The peer name is deliberately independent of its configured BP endpoint ID.
(defun fn-bpaj-current-peer-eidp (cfg principal generation eid)
  (declare (xargs :guard t))
  (and (fn-cfgp cfg)
       (equal generation (fn-cfg-generation cfg))
       (fn-cfg-labelp eid)
       (consp principal)
       (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
         (fn-bpaj-current-peer-eidp-rows rows rows principal eid))))

;; D23 (planning/decisions.md, 2026-09-24): relay trust by carrier allowlist.
;; A boundary's enrollment may carry rows (NAME "bp-boundary-carries" EID 0):
;; the source EIDs that neighbour may carry.  A bundle whose source is the
;; neighbour's own enrolled EID is direct, exactly as before.  One whose
;; source is on the delivering neighbour's carried list is carried, and the
;; principal it is judged under is the AUTHOR's own direct enrollment at this
;; node (a unique boundary whose transport-bp is that source), never the
;; carrier's.  Anything else is refused with a reason.

; NAME is directly enrolled for EID: its own trust profile and transport.
(defun fn-bpaj-direct-enrolledp (all name eid)
  (declare (xargs :guard t))
  (and (fn-cfg-labelp name)
       (let ((peer (fn-cfg-peer-find name all)))
         (and peer
              (equal (fn-cfg-peer-transport peer) (list :bp eid))))
       (fn-bpaj-unique-boundary-rowp all name "bp-trust" "network" 0)
       (fn-bpaj-unique-boundary-rowp all name "transport-bp" eid 0)))

; The boundaries directly enrolled for EID, each once, in row order.
(defun fn-bpaj-enrolled-source-names (rows all eid)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (let ((name (fn-cfg-row-a (car rows)))
            (rest (fn-bpaj-enrolled-source-names (cdr rows) all eid)))
        (if (and (equal (fn-cfg-row-b (car rows)) "bp-trust")
                 (fn-bpaj-direct-enrolledp all name eid)
                 (not (member-equal name rest)))
            (cons name rest)
          rest))
    nil))

; PRINCIPAL is a current BP boundary whose enrollment lists SOURCE as carried.
(defun fn-bpaj-carrier-rows (rows all principal source)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (let ((name (fn-cfg-row-a (car rows))))
        (or (and (equal (fn-cfg-row-b (car rows)) "bp-trust")
                 (fn-cfg-labelp name)
                 (let ((peer (fn-cfg-peer-find name all)))
                   (and peer (consp (fn-cfg-peer-transport peer))
                        (equal (car (fn-cfg-peer-transport peer)) :bp)))
                 (equal principal (fn-record-string-octets name))
                 (fn-bpaj-unique-boundary-rowp all name "bp-trust" "network" 0)
                 (fn-bpaj-boundary-rowp all name "bp-boundary-carries" source 0))
            (fn-bpaj-carrier-rows (cdr rows) all principal source)))
    nil))

; THE D23 DECISION.  PRINCIPAL and GENERATION are the delivering neighbour's,
; stamped on the TCPCL ingress by `fn-bpaj-session-principal'; SOURCE is the
; bundle's source EID text.
;   (:direct P)      source is the neighbour's own enrolled EID;
;   (:carried P A)   source is on P's carried list and A (octets) is the
;                    unique boundary directly enrolled for source;
;   (:refused R)     R is :generation, :source-not-carried or
;                    :carried-source-unenrolled.
(defun fn-bpaj-carried-source-decision (cfg principal generation source)
  (declare (xargs :guard t))
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
    (cond ((fn-bpaj-current-peer-eidp cfg principal generation source)
           (list :direct principal))
          ((not (and (fn-cfgp cfg)
                     (equal generation (fn-cfg-generation cfg))))
           (list :refused :generation))
          ((not (fn-bpaj-carrier-rows rows rows principal source))
           (list :refused :source-not-carried))
          (t (let ((names (fn-bpaj-enrolled-source-names rows rows source)))
               (if (and (consp names) (null (cdr names))
                        (consp (fn-record-string-octets (car names))))
                   (list :carried principal
                         (fn-record-string-octets (car names)))
                 (list :refused :carried-source-unenrolled)))))))

(defun fn-bpaj-source-decision-trustedp (decision)
  (declare (xargs :guard t))
  (and (consp decision)
       (or (equal (car decision) :direct) (equal (car decision) :carried))))

; The principal the application judges the bundle under: the neighbour for a
; direct bundle, the author for a carried one.
(defun fn-bpaj-source-decision-principal (decision)
  (declare (xargs :guard t))
  (cond ((and (consp decision) (equal (car decision) :direct)
              (consp (cdr decision)))
         (cadr decision))
        ((and (consp decision) (equal (car decision) :carried)
              (consp (cdr decision)) (consp (cddr decision)))
         (caddr decision))
        (t nil)))

;; Any boundary at this node enrolled with transport-bp SOURCE.
(defun fn-bpaj-source-enrolled-anywherep (rows source)
  (declare (xargs :guard t :measure (acl2-count rows)))
  (if (consp rows)
      (or (and (equal (fn-cfg-row-b (car rows)) "transport-bp")
               (equal (fn-cfg-row-c (car rows)) source))
          (fn-bpaj-source-enrolled-anywherep (cdr rows) source))
    nil))

(local (defthm fn-bpaj-label-is-a-string
  (implies (fn-cfg-labelp x) (stringp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-cfg-labelp fn-record-ascii-stringp)))))

(local (defthm fn-bpaj-boundary-row-value-is-a-label
  (implies (and (fn-cfg-row-listp rows)
                (fn-bpaj-boundary-rowp rows name slot value n))
           (fn-cfg-labelp value))
  :hints (("Goal" :in-theory (e/d (fn-cfg-row-listp fn-cfg-rowp)
                                  (fn-cfg-labelp))))))

(local (defthm fn-bpaj-boundary-rowp-transport-is-anywhere
  (implies (fn-bpaj-boundary-rowp rows name "transport-bp" source n)
           (fn-bpaj-source-enrolled-anywherep rows source))))

(local (defthm fn-bpaj-current-peer-rows-need-a-transport-row
  (implies (fn-bpaj-current-peer-eidp-rows rows all principal source)
           (fn-bpaj-source-enrolled-anywherep all source))))

(local (defthm fn-bpaj-enrolled-names-need-a-transport-row
  (implies (consp (fn-bpaj-enrolled-source-names rows all source))
           (fn-bpaj-source-enrolled-anywherep all source))))

(local (defthm fn-bpaj-enrolled-name-is-a-current-peer
  (implies (member-equal name (fn-bpaj-enrolled-source-names rows all eid))
           (fn-bpaj-current-peer-eidp-rows rows all
                                           (fn-record-string-octets name) eid))
  :hints (("Goal" :induct (fn-bpaj-enrolled-source-names rows all eid)))))

(local (defthm fn-bpaj-octets-chars-of-string-octets-aux
  (implies (character-listp chars)
           (and (fn-cbor-octet-listp (fn-record-string-octets-aux chars))
                (equal (fn-record-octets-chars
                        (fn-record-string-octets-aux chars))
                       chars)))))

(local (defthm fn-bpaj-octets-string-of-string-octets
  (implies (stringp name)
           (equal (fn-record-octets-string (fn-record-string-octets name))
                  name))))

(local (defthm fn-bpaj-carrier-rows-need-a-carries-row
  (implies (fn-bpaj-carrier-rows rows all principal source)
           (fn-bpaj-boundary-rowp all (fn-record-octets-string principal)
                                  "bp-boundary-carries" source 0))
  :hints (("Goal" :in-theory (disable fn-bpaj-unique-boundary-rowp
                                      fn-cfg-peer-find)))))

(local (defthm fn-bpaj-current-peer-rows-need-own-transport-row
  (implies (fn-bpaj-current-peer-eidp-rows rows all principal source)
           (fn-bpaj-boundary-rowp all (fn-record-octets-string principal)
                                  "transport-bp" source 0))
  :hints (("Goal" :in-theory (disable fn-cfg-peer-find
                                      fn-bpaj-boundary-slot-count)))))

; A carried source is a configured label: the carries row is a row of a
; well-formed configuration.
(defthm fn-bpaj-carried-source-is-a-label
  (implies (and (fn-cfgp cfg)
                (fn-bpaj-carrier-rows (fn-cfg-peers (fn-cfg-value cfg))
                                      (fn-cfg-peers (fn-cfg-value cfg))
                                      principal source))
           (fn-cfg-labelp source))
  :hints (("Goal" :in-theory (e/d (fn-cfgp fn-cfg-valuep)
                                  (fn-cfg-labelp fn-bpaj-carrier-rows
                                   fn-bpaj-boundary-rowp
                                   fn-bpaj-carrier-rows-need-a-carries-row))
           :use ((:instance fn-bpaj-carrier-rows-need-a-carries-row
                            (rows (fn-cfg-peers (fn-cfg-value cfg)))
                            (all (fn-cfg-peers (fn-cfg-value cfg))))
                 (:instance fn-bpaj-boundary-row-value-is-a-label
                            (rows (fn-cfg-peers (fn-cfg-value cfg)))
                            (name (fn-record-octets-string principal))
                            (slot "bp-boundary-carries")
                            (value source) (n 0))))))

; KEYSTONE (D23, "exactly as a direct one").  A carried decision names an
; author whose own direct delivery of the same source, at the same
; configuration generation, is decided `:direct' under that author.  The
; carrier's principal does not appear in the result the application uses.
(defthm fn-bpaj-carried-decision-is-the-authors-direct-decision
  (let ((d (fn-bpaj-carried-source-decision cfg principal generation source)))
    (implies (equal (car d) :carried)
             (let ((author (fn-bpaj-source-decision-principal d)))
               (and (fn-bpaj-current-peer-eidp cfg author generation source)
                    (equal (fn-bpaj-carried-source-decision
                            cfg author generation source)
                           (list :direct author))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-bpaj-carrier-rows
                                   fn-bpaj-current-peer-eidp-rows
                                   fn-bpaj-enrolled-source-names))
           :use ((:instance fn-bpaj-carried-source-is-a-label)
                 (:instance fn-bpaj-enrolled-name-is-a-current-peer
                            (name (car (fn-bpaj-enrolled-source-names
                                        (fn-cfg-peers (fn-cfg-value cfg))
                                        (fn-cfg-peers (fn-cfg-value cfg))
                                        source)))
                            (rows (fn-cfg-peers (fn-cfg-value cfg)))
                            (all (fn-cfg-peers (fn-cfg-value cfg)))
                            (eid source))))))

; Refusal of a source the neighbour neither is nor carries, stated over the
; configuration rows: the neighbour's boundary has no transport-bp row and
; no carries row for SOURCE.
(defthm fn-bpaj-unlisted-source-is-not-trusted
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg)))
        (name (fn-record-octets-string principal)))
    (implies (and (not (fn-bpaj-boundary-rowp rows name "transport-bp"
                                               source 0))
                  (not (fn-bpaj-boundary-rowp rows name "bp-boundary-carries"
                                               source 0)))
             (not (fn-bpaj-source-decision-trustedp
                   (fn-bpaj-carried-source-decision
                    cfg principal generation source)))))
  :hints (("Goal" :in-theory (disable fn-bpaj-carrier-rows
                                      fn-bpaj-current-peer-eidp-rows
                                      fn-bpaj-enrolled-source-names
                                      fn-bpaj-boundary-rowp
                                      fn-record-octets-string
                                      fn-bpaj-carrier-rows-need-a-carries-row
                                      fn-bpaj-current-peer-rows-need-own-transport-row)
           :use ((:instance fn-bpaj-carrier-rows-need-a-carries-row
                            (rows (fn-cfg-peers (fn-cfg-value cfg)))
                            (all (fn-cfg-peers (fn-cfg-value cfg))))
                 (:instance fn-bpaj-current-peer-rows-need-own-transport-row
                            (rows (fn-cfg-peers (fn-cfg-value cfg)))
                            (all (fn-cfg-peers (fn-cfg-value cfg))))))))

; Refusal of a carried source this node has not enrolled: the neighbour is a
; current carrier of SOURCE, and no boundary here has transport-bp SOURCE.
(defthm fn-bpaj-carried-unenrolled-source-is-refused
  (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
    (implies (and (fn-cfgp cfg)
                  (equal generation (fn-cfg-generation cfg))
                  (fn-bpaj-carrier-rows rows rows principal source)
                  (not (fn-bpaj-source-enrolled-anywherep rows source)))
             (equal (fn-bpaj-carried-source-decision
                     cfg principal generation source)
                    (list :refused :carried-source-unenrolled))))
  :hints (("Goal" :in-theory (disable fn-bpaj-carrier-rows
                                      fn-bpaj-current-peer-eidp-rows
                                      fn-bpaj-enrolled-source-names
                                      fn-bpaj-source-enrolled-anywherep))))

(defthm fn-bpaj-no-trust-row-enters-no-candidate
  (implies (not (fn-bpaj-boundary-rowp all name "bp-trust" "network" 0))
           (not (member-equal
                 name (fn-bpaj-loopback-candidates rows all port))))
  :hints (("Goal" :induct (fn-bpaj-loopback-candidates
                            rows all port))))

(defthm fn-bpaj-announced-eid-never-selects-a-peer
  (implies (and (equal (car (fn-bpaj-session-principal cfg channel first-eid))
                       :admitted)
                (equal (car (fn-bpaj-session-principal cfg channel second-eid))
                       :admitted))
           (equal (cadr (fn-bpaj-session-principal cfg channel first-eid))
                  (cadr (fn-bpaj-session-principal cfg channel second-eid))))
  :hints (("Goal" :in-theory (enable fn-bpaj-session-principal)))
  :rule-classes nil)

(verify-guards fn-bpaj-boundary-rowp)
(verify-guards fn-bpaj-boundary-slot-count)
(verify-guards fn-bpaj-unique-boundary-rowp)
(verify-guards fn-bpaj-current-peer-eidp-rows)
(verify-guards fn-bpaj-current-peer-eidp)
(verify-guards fn-bpaj-direct-enrolledp)
(verify-guards fn-bpaj-enrolled-source-names)
(verify-guards fn-bpaj-carrier-rows)
(verify-guards fn-bpaj-source-enrolled-anywherep)
(verify-guards fn-bpaj-carried-source-decision)
(verify-guards fn-bpaj-source-decision-trustedp)
(verify-guards fn-bpaj-source-decision-principal)
(verify-guards fn-bpaj-loopback-peerp)
(verify-guards fn-bpaj-loopback-candidates)
(verify-guards fn-bpaj-eid-text)
(verify-guards fn-bpaj-session-principal)
