(in-package "ACL2")
(include-book "../../books/memory-run-cost")
; Partial visits contain the constrained FN-COST-UNACCOUNTED tariff. Verify
; its logical result type without pretending it has an executable tariff.
(defthm m22-derived-bp-store-visits-are-natural
 (natp (fn-mo-serve-bp-store-need-visits resident profile cold output peer workers cache-limit root bp-terms core nursery)))
