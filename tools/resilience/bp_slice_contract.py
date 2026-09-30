"""Observation obligations for the real SCN1046 fixture.

This judges raw client replies, served bytes and operator outputs together.
It never derives a content identity or treats a diagnostic durable line as a
POST promise. Source/image qualification remains the runner's separate gate.
"""
import re


class MissingObservation(ValueError):
    pass


def octets(record, field):
    value = record.get(field)
    if not isinstance(value, dict) or set(value) != {"octets_hex"}:
        raise MissingObservation(field + ": missing lossless octets")
    try:
        return bytes.fromhex(value["octets_hex"])
    except (TypeError, ValueError) as error:
        raise MissingObservation(field + ": invalid octets") from error


def status(record, field):
    """Read the native command's single reported pin result, never guess it."""
    values = re.findall(rb"(?:^|\s)pinned=(yes|no)(?=\s|$)", octets(record, field))
    if len(values) != 1:
        raise MissingObservation(field + ": absent or ambiguous pin status")
    return values[0] == b"yes"


def work_ids(record, disposition):
    pattern = (rb"^BP transport work=([^\s]+)[^\r\n]*\bstatus=" +
               disposition + rb"(?=\s|$)")
    return set(re.findall(pattern, octets(record, "stdout"), re.M))


def observed_ids(values):
    if not isinstance(values, list):
        raise MissingObservation("receipt work identities missing")
    return {octets({"work": value}, "work") for value in values}


def obligations(events):
    """Return the first violated named observation rule; missing data refuses.

    Input is the adapter's ordered event map, with original bytes preserved.
    The producer supplies the real POST reply separately from fixture readback.
    """
    fixture = events["fixture"]
    posts = events["post-observed"]
    if len(posts) != 2 or posts[0].get("message_id") == posts[1].get("message_id"):
        raise MissingObservation("two distinct actual POST observations required")
    matching = [r for r in posts if r.get("message_id") == fixture.get("msgid")]
    if len(matching) != 1:
        raise MissingObservation("matching POST identity missing")
    post = matching[0]
    for event in ("fixture", "application-replay", "receipt-contact-uncertain",
                  "receipt-contact-resumed", "checkpoint-complete-readback",
                  "retirement-frozen-report"):
        code = events[event].get("exit_code")
        if type(code) is not int:
            raise MissingObservation(event + ": exit status missing")
        if code != 0:
            return "operation-completed", "operation failed at " + event
    for observed_post in posts:
        prompt, reply = octets(observed_post, "prompt"), octets(observed_post, "reply")
        octets(observed_post, "submitted_octets")
        if not prompt.startswith(b"340 ") or not reply.startswith(b"240 "):
            return "post-accepted", "a recorded client POST did not succeed"
    # The core supplies stored source bytes after POST; submitted NNTP bytes
    # can differ by legitimate serving/storage fields and are never normalized
    # by this checker into a guessed stored article.
    octets(post, "submitted_octets")
    accepted = octets(fixture, "accepted_octets")
    if not status(fixture, "status"):
        return "obligation-held", "matching debt was absent before receipt delivery"
    for event in ("decision-cut-readback", "checkpoint-complete-readback"):
        if octets(events[event], "octets") != accepted:
            return "accepted-bytes-preserved", "served article changed at " + event
    resumed = events["receipt-contact-resumed"]
    attempted = resumed.get("attempted_work")
    forwarded = resumed.get("forwarded_work")
    attempted_ids, forwarded_ids = observed_ids(attempted), observed_ids(forwarded)
    actual_attempted = work_ids(events["receipt-contact-uncertain"], b"attempted")
    actual_forwarded = work_ids(resumed, b"forwarded")
    if attempted_ids != actual_attempted or forwarded_ids != actual_forwarded:
        raise MissingObservation("receipt work fields differ from raw process output")
    if not attempted_ids or not attempted_ids <= forwarded_ids:
        return "receipt-reoffered", "an uncertain receipt job was not forwarded on healing"
    settlement = events["receipt-obligation-settlement"]
    if status(settlement, "matching") or not status(settlement, "unrelated"):
        return "matching-obligation-only", "receipt released the wrong outstanding debt"
    retirement = events["retirement-frozen-report"]
    report = octets(retirement, "report")
    lines = report.splitlines()
    if not any(b"obligation id=forward-unrelated kind=forward" in line for line in lines):
        return "retirement-debt-preserved", "retirement lost unrelated BP debt"
    if any(b"obligation id=forward-bp-node kind=forward" in line for line in lines):
        return "retirement-settlement-preserved", "retirement resurrected the settled debt"
    if report not in octets(retirement, "stdout"):
        return "retirement-report-frozen", "returned report differs from retained report bytes"
    return None


def fault_observations(events):
    """A configured selector is insufficient; require observed kill/hold/sever."""
    decision = events["decision-cut-readback"].get("fault")
    checkpoint = events["checkpoint-stage-cut"].get("fault")
    outbox = events["outbox-process-death"]
    for name, row, selector, value, marker in (
        ("application", decision, "FN_BP_APP_TEST_PAUSE_AFTER_DECISION", "1", b"BP APP DECISION DURABLE"),
        ("outbox", outbox, "FN_BP_NODE_TEST_PAUSE_AFTER_OUTBOX", "1", b"BP NODE OUTBOX DURABLE"),
        ("checkpoint", checkpoint, "FN_BP_ROTATION_TEST_STOP", "stage", b"BP journal rotation stopped at=stage")):
        if not isinstance(row, dict) or type(row.get("exit_code")) is not int:
            raise MissingObservation(name + ": observed process death missing")
        if row.get("selector") != selector or row.get("value") != value:
            raise MissingObservation(name + ": exact held selector missing")
        if row["exit_code"] != -9 or marker not in octets(row, "held_stdout"):
            return "intended-process-death-observed", "kill or held point was not observed at " + name
    relay = events["receipt-contact-uncertain"].get("relay_faults")
    if not isinstance(relay, list) or not relay:
        raise MissingObservation("receipt: actual relay sever observation missing")
    if not any(isinstance(row, dict) and row.get("event") == "byte-limit-severed"
               and type(row.get("forwarded")) is int and row["forwarded"] == 80
               and type(row.get("limit")) is int and row["limit"] == 80
               and row.get("send_succeeded") is True for row in relay):
        return "intended-contact-cut-observed", "configured receipt cut was not confirmed by actual send/sever"
    return None
