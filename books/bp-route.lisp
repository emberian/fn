; fn: the BP routing decision (specs/bp-node-machine.md section 4.6).
;
; RFC 9171 section 4.3 leaves "the choice of forwarding strategy" to the node
; and section 5.4 step 1 asks only that the node "determine whether or not
; forwarding is possible and, if so, ... which node(s) ... to forward the
; bundle to".  fn implements no routing protocol.  It decides: an operator's
; route table, held as configuration rows written through the assured
; reconfiguration path, names for each destination pattern the BP boundary
; a bundle may be offered to.  This book is that table, its parser, and the
; decision; books/bp-node-progress.lisp consults it at the one place a held
; bundle is offered (the :session event), and host/native/bp-node.lisp opens
; an outbound session only to the boundary it names.
;
; Everything here reads EID TEXT (the form `fn-bpaj-eid-text' renders and
; `fn-bp-eid-shapep' admits), so this book stays light: native-admin and
; the BP machine both include it.
(in-package "ACL2")
(include-book "config")
(include-book "bp-eid-shape")
(include-book "native-admin-shape")

(defconst *fn-bprt-default-priority* 100)

; ---------------------------------------------------------------------------
; Destination patterns.
;
; PATTERN is an EID text `fn-bp-eid-shapep' admits.  One wildcard form: a
; pattern whose final character is "*" (only a dtn demux can end so) is a
; PREFIX pattern and matches every EID whose text begins with the pattern
; less that "*"; any other pattern matches exactly the EID with that text.
;   dtn://receiver/      matches dtn://receiver/ only
;   dtn://receiver/*     matches dtn://receiver/, dtn://receiver/inbox, ...
;   dtn://*/             an exact pattern: node-name "*" is a literal
; There is no default route: a destination no pattern matches has no route.

(defun fn-bprt-prefix-charsp (p x)
  (declare (xargs :guard t))
  (if (atom p) t
    (and (consp x) (equal (car p) (car x))
         (fn-bprt-prefix-charsp (cdr p) (cdr x)))))

(defun fn-bprt-wildcard-charsp (cs)
  (declare (xargs :guard t))
  (if (atom cs) nil
    (if (atom (cdr cs)) (equal (car cs) #\*)
      (fn-bprt-wildcard-charsp (cdr cs)))))

(defun fn-bprt-strip-last (cs)
  (declare (xargs :guard t))
  (if (or (atom cs) (atom (cdr cs))) nil
    (cons (car cs) (fn-bprt-strip-last (cdr cs)))))

(defun fn-bprt-wildcardp (pattern)
  (declare (xargs :guard t))
  (and (stringp pattern)
       (fn-bprt-wildcard-charsp (coerce pattern 'list))))

(defun fn-bprt-patternp (pattern)
  (declare (xargs :guard t))
  (and (stringp pattern) (fn-bp-eid-shapep pattern)))

(defun fn-bprt-matchp (pattern dest)
  (declare (xargs :guard t))
  (and (stringp pattern) (stringp dest)
       (if (fn-bprt-wildcardp pattern)
           (fn-bprt-prefix-charsp (fn-bprt-strip-last (coerce pattern 'list))
                                  (coerce dest 'list))
         (equal pattern dest))))

; ---------------------------------------------------------------------------
; The route table.
;
; One route: (PRIORITY SPECIFICITY PATTERN BOUNDARY EID PORT).
;   PRIORITY     the operator's number; lower is preferred.
;   SPECIFICITY  0 for an exact pattern, 1 for a prefix pattern, so at equal
;                priority an exact route is preferred.
;   PATTERN      as above.
;   BOUNDARY     the name of a current BP boundary (`bp-boundary add').
;   EID          that boundary's enrolled transport-bp EID text: the node ID
;                an outbound session to it must announce.
;   PORT         the boundary's contact port (`bp-boundary add ... contact
;                PORT'), on the loopback profile's 127.0.0.1, or 0 when the
;                boundary has no contact row (routable, never contacted).
; The list order of a route is its rank: routes compare by `lexorder', a
; total order, so the preferred route is the same whatever the table order.

(defun fn-bprt-nth (n x)
  (declare (xargs :guard (natp n)))
  (if (atom x) nil
    (if (zp n) (car x) (fn-bprt-nth (1- n) (cdr x)))))

(defun fn-bprt-route-priority (r) (declare (xargs :guard t)) (fn-bprt-nth 0 r))
(defun fn-bprt-route-pattern (r) (declare (xargs :guard t)) (fn-bprt-nth 2 r))
(defun fn-bprt-route-boundary (r) (declare (xargs :guard t)) (fn-bprt-nth 3 r))
(defun fn-bprt-route-eid (r) (declare (xargs :guard t)) (fn-bprt-nth 4 r))
(defun fn-bprt-route-port (r) (declare (xargs :guard t)) (fn-bprt-nth 5 r))

(defun fn-bprt-route (priority pattern boundary eid port)
  (declare (xargs :guard t))
  (list priority (if (fn-bprt-wildcardp pattern) 1 0) pattern boundary eid port))

(defun fn-bprt-routep (r)
  (declare (xargs :guard t))
  (and (true-listp r) (equal (len r) 6)
       (fn-record-uint32p (nth 0 r))
       (equal (nth 1 r) (if (fn-bprt-wildcardp (nth 2 r)) 1 0))
       (fn-bprt-patternp (nth 2 r))
       (fn-cfg-labelp (nth 3 r)) (not (equal (nth 3 r) ""))
       (fn-bprt-patternp (nth 4 r))
       (natp (nth 5 r)) (<= (nth 5 r) 65535)))

(defun fn-bprt-tablep (table)
  (declare (xargs :guard t))
  (if (atom table) (null table)
    (and (fn-bprt-routep (car table)) (fn-bprt-tablep (cdr table)))))

; ---------------------------------------------------------------------------
; The decision.

; The routes whose pattern matches DEST, in table order.
(defun fn-bprt-matching (dest table)
  (declare (xargs :guard t))
  (if (atom table) nil
    (if (fn-bprt-matchp (fn-bprt-route-pattern (car table)) dest)
        (cons (car table) (fn-bprt-matching dest (cdr table)))
      (fn-bprt-matching dest (cdr table)))))

; The routes whose boundary is one of LIVE.
(defun fn-bprt-live-routes (routes live)
  (declare (xargs :guard t))
  (if (atom routes) nil
    (if (member-equal (fn-bprt-route-boundary (car routes)) (fix-true-list live))
        (cons (car routes) (fn-bprt-live-routes (cdr routes) live))
      (fn-bprt-live-routes (cdr routes) live))))

; The least route under `lexorder', or nil for no route.
(defun fn-bprt-least (routes)
  (declare (xargs :guard t))
  (if (atom routes) nil
    (if (atom (cdr routes)) (car routes)
      (let ((rest (fn-bprt-least (cdr routes))))
        (if (lexorder (car routes) rest) (car routes) rest)))))

; The preferred live route for DEST.
(defun fn-bprt-hop-route (dest table live)
  (declare (xargs :guard t))
  (fn-bprt-least (fn-bprt-live-routes (fn-bprt-matching dest table) live)))

; KEY DECISION.  DEST is the bundle's destination EID text, TABLE the route
; table, LIVE the boundary names with a live session.  The answer is the
; boundary the bundle is offered to, or
;   :no-route     no route's pattern matches DEST: the bundle stays held and
;                 is reported; its obligation is kept, never dropped;
;   :no-live-hop  routes match, but none names a boundary in LIVE: held for a
;                 later contact.
(defun fn-bprt-next-hop (dest table live)
  (declare (xargs :guard t))
  (let ((matching (fn-bprt-matching dest table)))
    (if (atom matching) :no-route
      (let ((hop (fn-bprt-hop-route dest table live)))
        (if (consp (fn-bprt-live-routes matching live))
            (fn-bprt-route-boundary hop)
          :no-live-hop)))))

; The boundaries of the table that have a contact port.
(defun fn-bprt-contactable (table)
  (declare (xargs :guard t))
  (if (atom table) nil
    (let ((rest (fn-bprt-contactable (cdr table))))
      (if (and (natp (fn-bprt-route-port (car table)))
               (< 0 (fn-bprt-route-port (car table))))
          (cons (fn-bprt-route-boundary (car table)) rest)
        rest))))

; The host's outbound question: for a held bundle to DEST, which boundary
; does `bp-node serve' contact, at which port, and which node ID must that
; contact announce?  The decision over the boundaries that have a contact:
; (:hop BOUNDARY EID PORT), or (:no-route) / (:no-live-hop).
(defun fn-bprt-outbound-choice (dest table)
  (declare (xargs :guard t))
  (let* ((live (fn-bprt-contactable table))
         (hop (fn-bprt-next-hop dest table live)))
    (if (or (equal hop :no-route) (equal hop :no-live-hop))
        (list hop)
      (let ((route (fn-bprt-hop-route dest table live)))
        (list :hop hop (fn-bprt-route-eid route) (fn-bprt-route-port route))))))

; The session gate the :session event consults.  VIA is (:via HOP ANNOUNCED
; TABLE): the boundary the host's outbound session reached, the node ID
; octets the contact announced in its SESS_INIT (RFC 9174 4.6), and the
; table.  A held bundle to DEST may be offered on this session only if the
; decision over the live set (HOP) names HOP, and the contact announced the
; EID that route's boundary is enrolled under.  Anything else: not offered.
(defun fn-bprt-viap (via)
  (declare (xargs :guard t))
  (and (true-listp via) (equal (len via) 4)
       (equal (nth 0 via) :via)
       (fn-cfg-labelp (nth 1 via)) (not (equal (nth 1 via) ""))
       (true-listp (nth 2 via))
       (fn-bprt-tablep (nth 3 via))))

(defun fn-bprt-offer-decision (dest via)
  (declare (xargs :guard t))
  (let* ((hop (fn-bprt-nth 1 via))
         (announced (fn-bprt-nth 2 via))
         (table (fn-bprt-nth 3 via))
         (decision (fn-bprt-next-hop dest table (list hop))))
    (cond ((not (and (stringp hop) (equal decision hop)))
           (if (equal decision :no-route) :no-route :no-live-hop))
          ((not (and (stringp (fn-bprt-route-eid
                               (fn-bprt-hop-route dest table (list hop))))
                     (equal (fn-record-string-octets
                             (fn-bprt-route-eid
                              (fn-bprt-hop-route dest table (list hop))))
                            announced)))
           :announced-mismatch)
          (t :offer))))

; What the decision answers.  A boundary answer is the boundary of a route
; in the table whose pattern matches DEST and whose boundary is live.
(encapsulate ()
(local (defthm least-member
  (implies (consp routes) (member-equal (fn-bprt-least routes) routes))))
(local (defthm live-routes-subset-a
  (implies (member-equal r (fn-bprt-live-routes routes live))
           (member-equal r routes))
  :hints (("Goal" :in-theory (disable fn-bprt-route-boundary)))))
(local (defthm live-routes-subset-b
  (implies (member-equal r (fn-bprt-live-routes routes live))
           (member-equal (fn-bprt-route-boundary r) (fix-true-list live)))
  :hints (("Goal" :in-theory (disable fn-bprt-route-boundary)))))
(local (defthm matching-subset-a
  (implies (member-equal r (fn-bprt-matching dest table))
           (member-equal r table))
  :hints (("Goal" :in-theory (disable fn-bprt-matchp fn-bprt-route-pattern)))))
(local (defthm matching-subset-b
  (implies (member-equal r (fn-bprt-matching dest table))
           (fn-bprt-matchp (fn-bprt-route-pattern r) dest))
  :hints (("Goal" :in-theory (disable fn-bprt-matchp fn-bprt-route-pattern)))))
; KEYSTONE.
(defthm fn-bprt-next-hop-names-a-live-matching-route
  (let ((hop (fn-bprt-next-hop dest table live))
        (route (fn-bprt-hop-route dest table live)))
    (implies (not (member-equal hop '(:no-route :no-live-hop)))
             (and (member-equal route table)
                  (fn-bprt-matchp (fn-bprt-route-pattern route) dest)
                  (member-equal hop (fix-true-list live))
                  (equal hop (fn-bprt-route-boundary route)))))
  :hints (("Goal" :in-theory (disable fn-bprt-matchp fn-bprt-route-pattern
                                      fn-bprt-route-boundary fn-bprt-least
                                      least-member live-routes-subset-a live-routes-subset-b
                                      matching-subset-a matching-subset-b)
           :use ((:instance least-member
                  (routes (fn-bprt-live-routes (fn-bprt-matching dest table) live)))
                 (:instance live-routes-subset-a
                  (r (fn-bprt-hop-route dest table live))
                  (routes (fn-bprt-matching dest table)))
                 (:instance live-routes-subset-b
                  (r (fn-bprt-hop-route dest table live))
                  (routes (fn-bprt-matching dest table)))
                 (:instance matching-subset-a (r (fn-bprt-hop-route dest table live)))
                 (:instance matching-subset-b (r (fn-bprt-hop-route dest table live)))))))
)

(encapsulate ()
(local (defthm least-member-2
  (implies (consp routes) (member-equal (fn-bprt-least routes) routes))))
(local (defthm least-is-least
  (implies (member-equal x routes) (lexorder (fn-bprt-least routes) x))))
(local (defthm lexorder-antisym
  (implies (and (lexorder x y) (lexorder y x)) (equal x y))
  :rule-classes nil))
(local (defthm member-of-subset
  (implies (and (member-equal x a) (subsetp-equal a b)) (member-equal x b))))
(local (defthm subset-nil-atom
  (implies (and (subsetp-equal b a) (atom a) (consp b)) nil)
  :rule-classes nil))
(local (defthm least-of-atom
  (implies (atom a) (equal (fn-bprt-least a) nil))))
(local (defthm least-of-set-equal
  (implies (and (subsetp-equal a b) (subsetp-equal b a))
           (equal (fn-bprt-least a) (fn-bprt-least b)))
  :hints (("Goal" :cases ((consp a)) :do-not-induct t
           :in-theory (disable fn-bprt-least least-is-least least-member-2 member-of-subset)
           :use ((:instance least-member-2 (routes a))
                 (:instance least-member-2 (routes b))
                 (:instance member-of-subset (x (fn-bprt-least a)) (a a) (b b))
                 (:instance member-of-subset (x (fn-bprt-least b)) (a b) (b a))
                 (:instance least-is-least (x (fn-bprt-least a)) (routes b))
                 (:instance least-is-least (x (fn-bprt-least b)) (routes a))
                 (:instance lexorder-antisym (x (fn-bprt-least a)) (y (fn-bprt-least b)))
                 (:instance subset-nil-atom (a a) (b b))
                 (:instance subset-nil-atom (a b) (b a)))))))
(local (defthm member-live-routes
  (iff (member-equal r (fn-bprt-live-routes routes live))
       (and (member-equal r routes)
            (member-equal (fn-bprt-route-boundary r) (fix-true-list live))))
  :hints (("Goal" :in-theory (disable fn-bprt-route-boundary)))))
(local (defthm live-routes-subset-mono
  (implies (subsetp-equal a b)
           (subsetp-equal (fn-bprt-live-routes a live) (fn-bprt-live-routes b live)))
  :hints (("Goal" :in-theory (disable fn-bprt-route-boundary)))))
(local (defthm consp-of-set-equal
  (implies (and (subsetp-equal a b) (consp a)) (consp b))
  :hints (("Goal" :in-theory (disable member-of-subset)
           :use ((:instance member-of-subset (x (car a))))))))
; KEYSTONE.  The decision is deterministic in the table: two tables whose
; routes matching DEST are the same set (in any order, with any repetition,
; whatever they hold for other destinations) give DEST the same answer.
(defthm fn-bprt-next-hop-deterministic-in-the-table
  (implies (and (subsetp-equal (fn-bprt-matching dest t1) (fn-bprt-matching dest t2))
                (subsetp-equal (fn-bprt-matching dest t2) (fn-bprt-matching dest t1)))
           (equal (fn-bprt-next-hop dest t1 live) (fn-bprt-next-hop dest t2 live)))
  :hints (("Goal" :in-theory (disable fn-bprt-least fn-bprt-matching fn-bprt-live-routes
                                      least-of-set-equal live-routes-subset-mono
                                      consp-of-set-equal fn-bprt-route-boundary)
           :use ((:instance least-of-set-equal
                  (a (fn-bprt-live-routes (fn-bprt-matching dest t1) live))
                  (b (fn-bprt-live-routes (fn-bprt-matching dest t2) live)))
                 (:instance live-routes-subset-mono
                  (a (fn-bprt-matching dest t1)) (b (fn-bprt-matching dest t2)))
                 (:instance live-routes-subset-mono
                  (a (fn-bprt-matching dest t2)) (b (fn-bprt-matching dest t1)))
                 (:instance consp-of-set-equal
                  (a (fn-bprt-matching dest t1)) (b (fn-bprt-matching dest t2)))
                 (:instance consp-of-set-equal
                  (a (fn-bprt-matching dest t2)) (b (fn-bprt-matching dest t1)))
                 (:instance consp-of-set-equal
                  (a (fn-bprt-live-routes (fn-bprt-matching dest t1) live))
                  (b (fn-bprt-live-routes (fn-bprt-matching dest t2) live)))
                 (:instance consp-of-set-equal
                  (a (fn-bprt-live-routes (fn-bprt-matching dest t2) live))
                  (b (fn-bprt-live-routes (fn-bprt-matching dest t1) live)))))))
)

; An :offer names the routed hop for DEST over the live set (HOP), and the
; contact announced the EID that route's boundary is enrolled under.
(defthm fn-bprt-offer-means-routed-hop-and-announced-eid
  (implies (equal (fn-bprt-offer-decision dest via) :offer)
           (and (equal (fn-bprt-next-hop dest (fn-bprt-nth 3 via)
                                         (list (fn-bprt-nth 1 via)))
                       (fn-bprt-nth 1 via))
                (equal (fn-record-string-octets
                        (fn-bprt-route-eid
                         (fn-bprt-hop-route dest (fn-bprt-nth 3 via)
                                            (list (fn-bprt-nth 1 via)))))
                       (fn-bprt-nth 2 via))))
  :hints (("Goal" :in-theory (union-theories '(fn-bprt-offer-decision)
                                             (theory 'minimal-theory)))))

(defthm fn-bprt-offer-names-a-string-hop
  (implies (equal (fn-bprt-offer-decision dest via) :offer)
           (stringp (fn-bprt-nth 1 via)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-bprt-offer-decision)
                                             (theory 'minimal-theory)))))

; With no route matching DEST the gate answers :no-route, whatever the hop.
(defthm fn-bprt-offer-decision-without-a-matching-route
  (implies (not (consp (fn-bprt-matching dest (fn-bprt-nth 3 via))))
           (equal (fn-bprt-offer-decision dest via) :no-route))
  :hints (("Goal" :in-theory (union-theories '(fn-bprt-offer-decision fn-bprt-next-hop)
                                             (theory 'minimal-theory)))))

(in-theory (disable fn-bprt-offer-decision))

; ---------------------------------------------------------------------------
; The table from the configuration.
;
; `bp-route add PATTERN BOUNDARY [PRIORITY]' writes one peer-table group
; named "bp-route PATTERN BOUNDARY" (PATTERN holds no space, so the name is
; injective) of two adjacent rows:
;   (NAME "bp-route-destination" PATTERN PRIORITY)
;   (NAME "bp-route-next-hop"    BOUNDARY 0)
; The group has no path-identity row, so it is no NNTP peer
; (`fn-cfg-peer-names') and no BP boundary.  `bp-route remove PATTERN
; BOUNDARY' removes the group.  A route whose BOUNDARY is not a current BP
; boundary (one "bp-trust" "network" row and one "transport-bp" row) enters
; no table: it routes nothing.

(defun fn-bprt-slot-values (rows name slot)
  (declare (xargs :guard t))
  (if (atom rows) nil
    (if (and (equal (fn-cfg-row-a (car rows)) name)
             (equal (fn-cfg-row-b (car rows)) slot))
        (cons (car rows) (fn-bprt-slot-values (cdr rows) name slot))
      (fn-bprt-slot-values (cdr rows) name slot))))

(defun fn-bprt-boundary-eid (rows boundary)
  (declare (xargs :guard t))
  (let ((trust (fn-bprt-slot-values rows boundary "bp-trust"))
        (eid (fn-bprt-slot-values rows boundary "transport-bp")))
    (and (consp trust) (null (cdr trust))
         (equal (fn-cfg-row-c (car trust)) "network")
         (consp eid) (null (cdr eid))
         (fn-bprt-patternp (fn-cfg-row-c (car eid)))
         (not (fn-bprt-wildcardp (fn-cfg-row-c (car eid))))
         (fn-cfg-row-c (car eid)))))

(defun fn-bprt-boundary-port (rows boundary)
  (declare (xargs :guard t))
  (let ((contact (fn-bprt-slot-values rows boundary "bp-boundary-contact")))
    (if (and (consp contact) (null (cdr contact))
             (equal (fn-cfg-row-c (car contact)) "127.0.0.1")
             (natp (fn-cfg-row-n (car contact)))
             (<= 1 (fn-cfg-row-n (car contact)))
             (<= (fn-cfg-row-n (car contact)) 65535))
        (fn-cfg-row-n (car contact))
      0)))

(defun fn-bprt-rows-table (rows all)
  (declare (xargs :guard t))
  (if (or (atom rows) (atom (cdr rows))) nil
    (let ((d (car rows)) (h (cadr rows)))
      (if (and (equal (fn-cfg-row-b d) "bp-route-destination")
               (equal (fn-cfg-row-b h) "bp-route-next-hop")
               (equal (fn-cfg-row-a d) (fn-cfg-row-a h)))
          (let* ((boundary (fn-cfg-row-c h))
                 (eid (fn-bprt-boundary-eid all boundary))
                 (route (fn-bprt-route (fn-cfg-row-n d) (fn-cfg-row-c d)
                                       boundary eid
                                       (fn-bprt-boundary-port all boundary))))
            (if (and eid (fn-bprt-routep route))
                (cons route (fn-bprt-rows-table (cddr rows) all))
              (fn-bprt-rows-table (cddr rows) all)))
        (fn-bprt-rows-table (cdr rows) all)))))

; The route table of a configuration: what the host passes back to the
; :session event, and reads its outbound choice from.
(defun fn-bprt-table (cfg)
  (declare (xargs :guard t))
  (if (fn-cfgp cfg)
      (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
        (fn-bprt-rows-table rows rows))
    nil))

; ---------------------------------------------------------------------------
; The operator verb.

(defun fn-bprt-group-name (pattern boundary)
  (declare (xargs :guard t))
  (if (and (stringp pattern) (stringp boundary))
      (string-append "bp-route " (string-append pattern (string-append " " boundary)))
    ""))

(defun fn-bprt-route-rows (pattern boundary priority)
  (declare (xargs :guard t))
  (let ((name (fn-bprt-group-name pattern boundary)))
    (list (fn-cfg-row-make name "bp-route-destination" pattern priority)
          (fn-cfg-row-make name "bp-route-next-hop" boundary 0))))

; `bp-route add PATTERN BOUNDARY [PRIORITY]' and `bp-route remove PATTERN
; BOUNDARY'.  WORDS are the argv words, "bp-route" first.
(defun fn-bprt-admin-plan (words)
  (declare (xargs :guard t))
  (let* ((words (fix-true-list words))
         (pattern (nth 2 words))
         (boundary (nth 3 words))
         (name (fn-bprt-group-name pattern boundary))
         (named (and (fn-bprt-patternp pattern)
                     (fn-cfg-labelp boundary)
                     (stringp boundary) (not (equal boundary ""))
                     (fn-cfg-labelp name))))
    (cond
     ((and named (equal (nth 1 words) "add")
           (or (equal (len words) 4)
               (and (equal (len words) 5)
                    (fn-native-admin-decimalp (nth 4 words))
                    (fn-record-uint32p (fn-native-admin-decimal-value
                                        (coerce (nth 4 words) 'list))))))
      (fn-native-admin-result
       :accepted nil :set-bp-route (fn-record-string-octets name) 0 nil
       (fn-bprt-route-rows pattern boundary
                           (if (equal (len words) 5)
                               (fn-native-admin-decimal-value
                                (coerce (nth 4 words) 'list))
                             *fn-bprt-default-priority*))))
     ((and named (equal (nth 1 words) "remove") (equal (len words) 4))
      ; Its own kind: the offline executor's `:remove-peer' refuses a name
      ; that denotes no typed peer (host/store-node-host.lisp
      ; fn-store-cfg-remove-peer), and a route group is none.
      (fn-native-admin-result
       :accepted nil :remove-bp-route (fn-record-string-octets name) 0 nil nil))
     (t (fn-native-admin-result :refused :bp-route nil nil 0 nil nil)))))

(defthm fn-bprt-admin-plan-kind
  (member-equal (fn-native-admin-result-kind (fn-bprt-admin-plan words))
                '(:set-bp-route :remove-bp-route nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-result fn-native-admin-result-kind)
                                  (fn-bprt-route-rows fn-bprt-group-name)))))

; The plan's kind is never a group, boundary, policy or capacity kind, as
; rewrite rules so that fn-native-admin-plan's theorems close the bp-route
; arm without a case split.
(defthm fn-bprt-admin-plan-kind-is-no-other-kind
  (and (not (equal (fn-native-admin-result-kind (fn-bprt-admin-plan words))
                   :create-group))
       (not (equal (fn-native-admin-result-kind (fn-bprt-admin-plan words))
                   :remove-group))
       (not (equal (fn-native-admin-result-kind (fn-bprt-admin-plan words))
                   :set-bp-boundary)))
  :hints (("Goal" :use fn-bprt-admin-plan-kind
                  :in-theory (disable fn-bprt-admin-plan))))

(defthm fn-bprt-admin-plan-caddr-is-no-other-kind
  (and (not (equal (caddr (fn-bprt-admin-plan words)) :create-group))
       (not (equal (caddr (fn-bprt-admin-plan words)) :remove-group))
       (not (equal (caddr (fn-bprt-admin-plan words)) :set-bp-boundary)))
  :hints (("Goal" :use fn-bprt-admin-plan-kind-is-no-other-kind
                  :in-theory (disable fn-bprt-admin-plan
                                      fn-bprt-admin-plan-kind-is-no-other-kind))))

(in-theory (disable fn-bprt-admin-plan))
