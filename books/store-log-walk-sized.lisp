; Same actual parse decision supplies full-log txids and snapshot row carries.
(in-package "ACL2")

(include-book "store-log-walk-once")

(include-book "store-recover-stream-sized")

(defun fn-lgbs-event-decode (octets)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((legacy (ec-call (fn-record-decode-exact octets)))
        (txid (if (fn-record-parse-okp legacy)
                   (ec-call (fn-record-txid (fn-record-parse-value legacy))) nil)))
  (if (fn-record-result-okp legacy) (mv legacy nil txid t)
   (let ((retention (ec-call (fn-store-retention-event-decode-exact octets))))
    (if (equal (fn-ag-car retention) :ok) (mv retention nil txid nil)
     (let ((verdict (ec-call (fn-stxe-decode-exact octets))))
      (if (fn-stmt-okp verdict) (mv verdict nil txid nil)
       (mv-let (snapshot carry) (fn-stxks-decode octets)
        (if (fn-stmt-okp snapshot) (mv snapshot carry txid nil)
         (let ((accepted (ec-call (fn-stxa-decode-exact octets))))
          (if (fn-stmt-okp accepted) (mv accepted nil txid nil)
           (let ((consumer (ec-call (fn-cpe-decode-exact octets))))
            (if (fn-stmt-okp consumer) (mv consumer nil txid nil)
             (mv (ec-call (fn-th-topic-event-decode-exact octets)) nil txid nil))))))))))))))

(verify-guards fn-lgbs-event-decode)

(defun fn-lgbs-decode-one (r)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (decoded carry txid legacy-accepted) (fn-lgbs-event-decode r)
  (if legacy-accepted
   (mv (ec-call (fn-record-result-record decoded)) txid nil)
  (if (and (consp decoded) (eq (car decoded) :ok) (consp (cdr decoded))
           (ec-call (fn-rcon-wire-event-p (cadr decoded))))
   (mv (cadr decoded) txid carry)
   (mv :bad txid nil)))))

(verify-guards fn-lgbs-decode-one)

(defun fn-lgbs-decode-loop (rs next acc carries badp)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp rs)
  (mv-let (event txid carry) (fn-lgbs-decode-one (car rs))
   (fn-lgbs-decode-loop (cdr rs) (max (1+ (nfix txid)) (nfix next))
                        (cons event acc) (cons carry carries)
                        (or badp (eq event :bad))))
  (mv (if (or badp (not (null rs))) :bad (fn-ag-rev-onto acc nil))
      (nfix next)
      (if (or badp (not (null rs))) nil (fn-ag-rev-onto carries nil)))))

(verify-guards fn-lgbs-decode-loop)

(defun fn-lgb-decode-next-sized (rs next)
 (declare (xargs :guard t))
 (fn-lgbs-decode-loop rs next nil nil nil))

(defthm fn-lgbs-event-preserves-paired-decode-and-txid
 (and (equal (mv-nth 0 (fn-lgbs-event-decode octets))
             (mv-nth 0 (fn-srss-event-decode octets)))
      (equal (mv-nth 1 (fn-lgbs-event-decode octets))
             (mv-nth 1 (fn-srss-event-decode octets)))
      (equal (mv-nth 2 (fn-lgbs-event-decode octets)) (fn-lgt-txid octets)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (e/d (fn-lgbs-event-decode fn-srss-event-decode fn-lgt-txid)
   (fn-record-parse-okp fn-record-parse-value fn-record-txid
    fn-record-result-okp fn-store-retention-event-decode-exact fn-stxe-decode-exact
    fn-stxks-decode fn-stxa-decode-exact fn-cpe-decode-exact
    fn-th-topic-event-decode-exact fn-stmt-okp)))))

(defthm fn-lgbs-one-preserves-original-event-and-txid
 (and (equal (mv-nth 0 (fn-lgbs-decode-one r)) (mv-nth 0 (fn-lgb-decode-one r)))
      (equal (mv-nth 1 (fn-lgbs-decode-one r)) (mv-nth 1 (fn-lgb-decode-one r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-srss-event-first-result-is-actual-dispatch (octets r)))
  :in-theory (e/d (fn-lgbs-decode-one fn-lgbs-event-decode fn-lgb-decode-one
                   fn-srss-event-decode)
   (fn-record-parse-okp fn-record-parse-value fn-record-txid
    fn-record-result-okp fn-record-result-record fn-store-event-decode-exact
    fn-store-retention-event-decode-exact fn-stxe-decode-exact fn-stxks-decode
    fn-stxa-decode-exact fn-cpe-decode-exact fn-th-topic-event-decode-exact
    fn-stmt-okp fn-rcon-wire-event-p)))))

(local (defthm fn-lgb-legacy-is-a-wire-event
   (implies (fn-record-result-okp (fn-record-decode-exact r))
            (and (consp (fn-record-decode-exact r))
                 (equal (car (fn-record-decode-exact r)) :ok)
                 (consp (cdr (fn-record-decode-exact r)))
                 (fn-rcon-wire-event-p (car (cdr (fn-record-decode-exact r))))
                 (fn-wire-event-p (car (cdr (fn-record-decode-exact r))))
                 (equal (fn-record-result-record (fn-record-decode-exact r))
                        (car (cdr (fn-record-decode-exact r))))))
   :hints (("Goal" :in-theory (e/d (fn-rcon-wire-event-p-is-wire-event-p fn-wire-event-p
                                    fn-record-result-record fn-record-result-okp fn-cbor-ag-car)
                                   (fn-rcon-wire-event-p fn-record-p
                                    fn-record-decode-exact-yields-a-record))
            :use ((:instance fn-record-decode-exact-yields-a-record (octets r)))))))

(local (defthm fn-lgbs-one-original-rewrite
 (and (equal (mv-nth 0 (fn-lgbs-decode-one r)) (mv-nth 0 (fn-lgb-decode-one r)))
      (equal (mv-nth 1 (fn-lgbs-decode-one r)) (mv-nth 1 (fn-lgb-decode-one r))))
 :hints (("Goal" :use fn-lgbs-one-preserves-original-event-and-txid))))

(defthm fn-lgbs-loop-preserves-original-complete-result
 (and (equal (mv-nth 0 (fn-lgbs-decode-loop rs next acc carries badp))
             (mv-nth 0 (fn-lgb-decode-next-exec-loop rs next acc badp)))
      (equal (mv-nth 1 (fn-lgbs-decode-loop rs next acc carries badp))
             (mv-nth 1 (fn-lgb-decode-next-exec-loop rs next acc badp))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lgbs-decode-loop rs next acc carries badp)
 :in-theory (e/d (fn-lgbs-decode-loop fn-lgb-decode-next-exec-loop)
 (fn-lgbs-decode-one fn-lgb-decode-one fn-ag-rev-onto)))))

(defthm fn-lgbs-loop-next-is-actual-fold
 (equal (mv-nth 1 (fn-lgbs-decode-loop rs next acc carries badp))
        (fn-lgw-next-fold rs next))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lgbs-decode-loop rs next acc carries badp)
 :in-theory (e/d (fn-lgbs-decode-loop fn-lgw-next-fold fn-lgw-next-after-one
                   fn-lgb-decode-one fn-lgt-txid)
 (fn-lgbs-decode-one fn-record-result-okp fn-record-parse-okp fn-record-txid
  fn-record-parse-value fn-store-event-decode-exact fn-rcon-wire-event-p)))))

(local (defthm fn-lgbs-one-paired-dispatch
 (let ((d (mv-nth 0 (fn-srss-event-decode r))))
 (and (equal (mv-nth 0 (fn-lgbs-decode-one r))
             (if (and (consp d) (eq (car d) :ok) (consp (cdr d))
                      (fn-rcon-wire-event-p (cadr d))) (cadr d) :bad))
      (implies (not (equal (mv-nth 0 (fn-lgbs-decode-one r)) :bad))
       (equal (mv-nth 2 (fn-lgbs-decode-one r))
              (mv-nth 1 (fn-srss-event-decode r))))))
 :hints (("Goal" :cases ((fn-record-result-okp (fn-record-decode-exact r)))
 :in-theory (union-theories
 '(fn-lgbs-decode-one fn-lgbs-event-decode fn-srss-event-decode
   fn-lgb-legacy-is-a-wire-event fn-ag-car fn-ag-cdr fn-cbor-ag-car
   mv-nth car-cons cdr-cons)
 (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

(local (defthm fn-lgbs-bad-stays-bad
 (implies badp
 (and (equal (mv-nth 0 (fn-lgbs-decode-loop rs next acc carries badp)) :bad)
      (equal (mv-nth 2 (fn-lgbs-decode-loop rs next acc carries badp)) nil)))
 :hints (("Goal" :induct (fn-lgbs-decode-loop rs next acc carries badp)
 :in-theory (union-theories '(fn-lgbs-decode-loop mv-nth car-cons cdr-cons) (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))))

(local (defthm fn-lgbs-wire-never-bad
 (implies (fn-rcon-wire-event-p x) (not (equal x :bad)))
 :hints (("Goal" :cases ((equal x :bad))))))

(defthm fn-lgbs-loop-preserves-paired-events-and-carries
 (and (equal (mv-nth 0 (fn-lgbs-decode-loop rs next acc carries nil))
             (mv-nth 0 (fn-srss-decode-loop rs acc carries)))
      (equal (mv-nth 2 (fn-lgbs-decode-loop rs next acc carries nil))
             (mv-nth 1 (fn-srss-decode-loop rs acc carries))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lgbs-decode-loop rs next acc carries nil)
 :in-theory (union-theories '(fn-lgbs-decode-loop fn-srss-decode-loop fn-lgbs-one-paired-dispatch fn-lgbs-bad-stays-bad fn-lgbs-wire-never-bad (:type-prescription fn-lgbs-decode-loop) (:type-prescription fn-srss-decode-loop) (:type-prescription fn-srss-event-decode) mv-nth car-cons cdr-cons) (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))))

(defthm fn-lgb-decode-next-sized-preserves-complete-original-result
 (and (equal (mv-nth 0 (fn-lgb-decode-next-sized rs next))
             (mv-nth 0 (fn-lgb-decode-next rs next)))
      (equal (mv-nth 1 (fn-lgb-decode-next-sized rs next))
             (mv-nth 1 (fn-lgb-decode-next rs next))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lgbs-loop-preserves-paired-events-and-carries
                        (acc nil) (carries nil))
                       (:instance fn-lgbs-loop-next-is-actual-fold
                        (acc nil) (carries nil) (badp nil))
                       (:instance fn-srss-first-result-is-actual-chunk-decode
                        (octet-records rs)))
 :in-theory (union-theories '(fn-lgb-decode-next-sized fn-lgb-decode-next fn-srss-decode
 mv-nth car-cons cdr-cons)
 (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))))

(defthm fn-lgb-decode-next-sized-carries-are-actual-snapshot-rows
 (implies (not (equal (mv-nth 0 (fn-lgb-decode-next-sized rs next)) :bad))
  (fn-srss-carries-correspondsp
   (mv-nth 0 (fn-lgb-decode-next-sized rs next))
   (mv-nth 2 (fn-lgb-decode-next-sized rs next))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lgbs-loop-preserves-paired-events-and-carries
                       (acc nil) (carries nil))
                       (:instance fn-srss-success-carries-correspond-to-actual-rows
                        (octet-records rs)))
 :in-theory (union-theories '(fn-lgb-decode-next-sized fn-srss-decode mv-nth car-cons cdr-cons)
 (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))))

(defthm fn-lgb-decode-next-sized-carries-are-aligned
 (and (true-listp (mv-nth 2 (fn-lgb-decode-next-sized rs next)))
      (equal (len (mv-nth 2 (fn-lgb-decode-next-sized rs next)))
             (len (mv-nth 0 (fn-lgb-decode-next-sized rs next)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-lgbs-loop-preserves-paired-events-and-carries
                       (acc nil) (carries nil))
                       (:instance fn-srss-has-aligned-snapshot-carries (octet-records rs)))
 :in-theory (union-theories '(fn-lgb-decode-next-sized fn-srss-decode mv-nth car-cons cdr-cons)
 (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))))
