"""Production injection fixtures for BP tests, before FNWF/BP owns Store."""

from tests.native_harness import EXIT, Node


def post_articles(case, image, store, articles):
    """Inject pairs, capture ARTICLE, and return the core's stored source bytes.

    The caller supplies the matching DEFAULT production image. The tracked
    owner has exited before any returned bytes can be used by the BP fixture.
    """
    store = store.resolve()
    producer = Node(case, image, root=store.parent / (store.name + "-producer"))
    producer.store_path = store
    producer.write_config()
    producer.operator("policy", "set", "path-identity", "sender.bp.gate.invalid",
                      expect=EXIT.OK)
    message_ids = []
    try:
        producer.start()
        for message_id, payload in articles:
            producer.post(message_id, payload, expect=EXIT.OK)
            with producer.session() as client:
                article = client.article(message_id)
            case.assertIsNotNone(article, "producer owner must serve its durable post")
            (producer.root / ("article-{}.nntp".format(len(message_ids)))).write_bytes(article)
            message_ids.append(message_id)
    finally:
        if producer.process is not None:
            producer.stop()
    # ARTICLE includes the serving node's Xref. Ask the core for the stored
    # record used by FNWF identity derivation instead of trimming it in Python.
    return {message_id: producer.store("inspect", message_id, expect=EXIT.OK).stdout
            for message_id in message_ids}
