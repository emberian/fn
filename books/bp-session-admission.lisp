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
       (fn-record-uint32p listener-port)
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
