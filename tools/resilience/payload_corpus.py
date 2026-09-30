"""Exact payload boundaries supplied by a source/profile coordinate.

Fixture bytes are test inputs, never a host codec/checksum/admission decision.
Sizes count the complete supplied payload, not merely its body. Experimental
preparation budgets refuse a campaign before writes; they do not truncate it.
"""
import hashlib
import re


def cases(boundaries):
    """Keep below/at/above every caller-supplied literal boundary, losslessly."""
    result = []
    for row in boundaries:
        if (not isinstance(row, dict) or type(row.get("octets")) is not int
                or row["octets"] < 0 or not isinstance(row.get("name"), str)
                or not row["name"] or not isinstance(row.get("source"), str)
                or not re.fullmatch(r"[0-9a-f]{40}", row["source"])
                or row.get("unit") != "complete-payload-octets"):
            raise ValueError("literal complete-payload boundary and immutable source required")
        for delta in (-1, 0, 1):
            size = row["octets"] + delta
            if size >= 0:
                result.append(dict(boundary=row["name"], source=row["source"],
                                   octets=size, boundary_octets=row["octets"], relation={-1: "below", 0: "at", 1: "above"}[delta]))
    return result


def preflight(posts, budget):
    """Budget fixture preparation separately from product admission/funding."""
    selected = [op for op in posts if "boundary_payload" in op.args]
    if not selected:
        return
    if type(budget) is not int or budget < 0:
        raise ValueError("explicit experimental payload preparation octet budget required")
    total = 0
    for op in selected:
        row = op.args["boundary_payload"]
        if (not isinstance(row, dict) or type(row.get("octets")) is not int
                or row["octets"] < 0 or type(row.get("boundary_octets")) is not int
                or row["boundary_octets"] < 0 or row.get("relation") not in ("below", "at", "above")
                or not isinstance(row.get("boundary"), str) or not row["boundary"]
                or not isinstance(row.get("source"), str)
                or not re.fullmatch(r"[0-9a-f]{40}", row["source"])):
            raise ValueError("invalid retained boundary payload descriptor")
        delta = {"below": -1, "at": 0, "above": 1}[row["relation"]]
        if row["octets"] != row["boundary_octets"] + delta:
            raise ValueError("boundary relation disagrees with literal payload size")
        total += row["octets"]
    if total > budget:
        raise ValueError("experimental payload preparation budget exceeded; no payload truncated")


def write(path, row, prefix=b"", suffix=b""):
    """Stream ASCII fixture filler, retaining exact complete-input size/digest."""
    size = row["octets"]
    fill = size - len(prefix) - len(suffix)
    if fill < 0:
        raise ValueError("boundary payload smaller than literal fixture envelope")
    digest = hashlib.sha256()
    with path.open("xb") as stream:
        def emit(chunk):
            stream.write(chunk)
            digest.update(chunk)
        emit(prefix)
        # An I/O chunk size, not a stored-data or natural-width ceiling.
        chunk = b"x" * 8192
        while fill:
            amount = min(fill, len(chunk))
            emit(chunk[:amount])
            fill -= amount
        emit(suffix)
    return dict(**row, sha256=digest.hexdigest(), prepared_octets=size,
                admission="unobserved", byte_scope="complete supplied payload")
