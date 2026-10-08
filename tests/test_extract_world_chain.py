"""tools/extract/world.py's chain of links: the include order is the image's (lane n-tls-chain)."""
import re
import sys
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "extract"))
import world  # noqa: E402

# The include lines of books/image-world.lisp as the single umbrella had them
# (dev cf1754735), before it became a chain.
FIXTURE = [line for line in (ROOT / "tests" / "fixtures" / "world_chain"
                             / "image-world-order.txt").read_text().splitlines() if line]


def chain_order(name):
    """The umbrella's include lines as its files give them: the chain walked
    from the thin umbrella down to the first link, then each link's own lines."""
    def own(book):
        return re.findall(r'^\(include-book "([^"]+)"\)$',
                          (ROOT / "books" / (book + ".lisp")).read_text(), re.M)
    lines = own(name)
    if len(lines) != 1 or not re.fullmatch(re.escape(name) + r"-part-\d+", lines[0]):
        return lines                      # no chain: the umbrella holds them
    order, link = [], lines[0]
    while link:
        mine = own(link)
        previous = [m for m in mine[:1] if re.fullmatch(re.escape(name) + r"-part-\d+", m)]
        order = mine[len(previous):] + order
        link = previous[0] if previous else None
    return order


class SplitTests(unittest.TestCase):
    def test_the_slices_of_todays_umbrella_concatenate_to_it_exactly(self):
        slices = world.split_links(FIXTURE)
        self.assertGreater(len(slices), 1)
        self.assertEqual([b for one in slices for b in one], FIXTURE)

    def test_each_slice_fits_the_measured_budget(self):
        costs = world.slot_costs()
        for one in world.split_links(FIXTURE):
            self.assertLessEqual(sum(costs.get(b, world.UNMEASURED_COST) for b in one),
                                 world.LINK_INCLUDE_BUDGET)

    def test_the_budget_leaves_a_link_under_its_fraction_of_the_limit(self):
        worst = (world.LINK_INCLUDE_BUDGET + world.SLOT_BASE + world.CERTIFY_MARGIN
                 + world.PREV_LINK_COST)
        self.assertLessEqual(worst, world.LINK_FRACTION * world.SLOT_LIMIT)

    def test_an_unmeasured_book_costs_more_than_any_measured_one(self):
        self.assertGreater(world.UNMEASURED_COST, max(world.slot_costs().values()))
        slices = world.split_links(["new-%d" % i for i in range(200)])
        self.assertGreater(len(slices), 1)

    def test_a_small_umbrella_is_one_slice(self):
        self.assertEqual(world.split_links(FIXTURE[:10]), [FIXTURE[:10]])


class OrderTests(unittest.TestCase):
    def test_every_generated_chain_has_the_umbrella_order(self):
        for build, umbrella in world.UMBRELLAS.items():
            books, _ = world.world_books(build)
            want = [world.relative_to_books(b) for b in world.books_last(books)]
            self.assertEqual(chain_order(umbrella.split("/")[-1]), want, umbrella)

    def test_the_generator_refuses_a_split_that_reorders(self):
        build, umbrella = next(iter(world.UMBRELLAS.items()))
        real = world.split_links

        def reordered(books, *a, **k):
            slices = real(books, *a, **k)
            return slices[::-1] if len(slices) > 1 else [list(reversed(slices[0]))]
        with mock.patch.object(world, "split_links", reordered):
            with self.assertRaises(AssertionError):
                world.render_umbrella(build, umbrella)

    def test_the_fixture_is_the_default_umbrella_order_at_cf1754735_up_to_later_books(self):
        want = chain_order("image-world")
        self.assertGreater(len(set(FIXTURE) & set(want)), 0.95 * len(FIXTURE))


if __name__ == "__main__":
    unittest.main()
