"""Selected world names can be public without importing the aggregate world."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).parents[1]/'meta/emit'))
from emit_embed import world_bodies


class PublicWorldBodies(unittest.TestCase):
    def layout(self, suffix=''):
        return dict(mod_of={'F':'A'+suffix, 'G':'B'+suffix, 'H':'C'+suffix},
                    mods=['A'+suffix, 'B'+suffix, 'C'+suffix],
                    D={'F':{'G'}, 'G':set(), 'H':set()}, reach={}, native_callees=set(), columns={})

    def source(self, spec):
        return ('module\n-- BEGIN world bodies (emit_embed.py): '+spec+
                '\n-- END world bodies\n@[expose] public section\nexample := «F»\nend\n')

    def test_public_selected_dependency_closure_and_refresh(self):
        result = world_bodies(self.source('public; scan'), self.layout(), 'World')
        for module in ['A','B']:
            self.assertIn('public import World.'+module+'\n', result)
            self.assertIn('import all World.'+module+'\n', result)
        self.assertNotIn('World.C', result)
        refreshed = world_bodies(result, self.layout('2'), 'World')
        self.assertNotIn('World.A\n', refreshed)
        self.assertIn('public import World.A2\n', refreshed)
        self.assertEqual(refreshed, world_bodies(refreshed, self.layout('2'), 'World'))

    def test_private_default_is_unchanged(self):
        result = world_bodies(self.source('scan'), self.layout(), 'World')
        self.assertNotIn('public import', result)
        self.assertIn('import all World.A\n', result)
        self.assertIn('import all World.B\n', result)

    def test_unknown_public_clause_is_rejected(self):
        with self.assertRaises(SystemExit):
            world_bodies(self.source('public typo; scan'), self.layout(), 'World')


if __name__ == '__main__':
    unittest.main()
