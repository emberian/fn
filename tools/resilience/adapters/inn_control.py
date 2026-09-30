"""Retain exact INN control subjects; no physical receipt from summary verdicts.

This is an external test observer, not an ACL2 admission/identity decision.
The peering owner's parser must supply literal transfer/block completeness.
"""
import base64
import re
from ..journal import Journal


def subject(octets):
    if not isinstance(octets, bytes) or b"\r\n\r\n" not in octets:
        return None
    fields = []
    for line in octets.split(b"\r\n\r\n", 1)[0].split(b"\r\n"):
        if line.startswith((b" ", b"\t")):
            if not fields:
                return None
            fields[-1] += b" " + line.strip()
        else:
            if b":" not in line:
                return None
            fields.append(line)
    values = [line.split(b":", 1)[1].strip() for line in fields
              if line.split(b":", 1)[0].lower() == b"message-id"]
    return values[0] if len(values) == 1 else None


def observe(scenario_id, expected, exchange, served):
    """Return retained journal and subject disposition, never a pillar verdict.

    `exchange` is the actual parser result, `served` full readback octets.
    Missing raw bytes/completeness is unavailable, not a clean observation.
    """
    if not isinstance(expected, str) or not re.fullmatch(r"<[^<>\s]+@[^<>\s]+>", expected):
        raise ValueError("exact expected Message-ID required")
    if exchange is not None and not isinstance(exchange, dict):
        raise ValueError("actual exchange object required")
    expected_bytes = expected.encode("ascii")
    journal = Journal(scenario_id)
    arrived = exchange.get("article") if isinstance(exchange, dict) else None
    raw = lambda value: base64.b64encode(value).decode("ascii") if isinstance(value, bytes) else None
    journal.environment("inn-control-raw-subject", expected=expected, arrived_octets=raw(arrived),
                        served_octets=raw(served), exchange={k: v for k, v in (exchange or {}).items()
                                                            if k != "article"})
    if not isinstance(exchange, dict) or exchange.get("block_complete") is not True or exchange.get("transfer_complete") is not True:
        result = dict(status="unavailable", cause="inn-control-transfer-completeness-unobserved")
    elif isinstance(exchange.get("result"), str) and exchange["result"][:3] in ("437", "439"):
        result = dict(status="refused", cause="inn-control-transfer-refused")
    elif not isinstance(exchange.get("result"), str) or exchange["result"][:3] not in ("235", "239"):
        result = dict(status="unavailable", cause="inn-control-transfer-outcome-unobserved")
    elif exchange["result"].startswith("239") and exchange["result"].split()[1:2] != [expected]:
        result = dict(status="violation", cause="inn-control-reply-subject-mismatch")
    elif not isinstance(arrived, bytes) or not isinstance(served, bytes):
        result = dict(status="unavailable", cause="inn-control-raw-octets-unobserved")
    elif subject(arrived) != expected_bytes or subject(served) != expected_bytes:
        result = dict(status="violation", cause="inn-control-arrival-or-readback-subject-mismatch")
    else:
        result = dict(status="observed", cause=None)
    journal.environment("inn-control-subject-disposition", **result,
                        scope="external subject observation; no native/INN completion or group-authority claim")
    return journal, result
