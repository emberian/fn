# Separate human client submission contract

WEB-001: The optional local web-client outbox must durably bind one exact
composed article, Message-ID and NNTP target to a submission identifier before
its first network attempt. A second request, concurrent handler, or restart
must never automatically send that identifier again. Accepted, refused and
uncertain NNTP responses remain distinct; an in-flight record after restart is
uncertain, and later ARTICLE observations do not rewrite the response. The
outbox is private, single-instance and bounded without automatic deletion.
Any ambiguous local persistence failure fences new attempts. The default
in-memory mode remains available. This is a client evidence contract, not a
server acceptance or retention guarantee. The operator behavior and current
filesystem assumptions are in [the client guide](../docs/human-web-client.md).
