"""Failure-mode tests for the source/receipt verification infrastructure."""
import tempfile
import unittest
import json
import hashlib
import zipfile
from pathlib import Path

import verify


class SourceAuditTests(unittest.TestCase):
    def test_comments_and_strings_do_not_hide_real_escape(self):
        code = verify.lean_code('/- sorry /- admit -/ -/\n"axiom"\ntheorem x : True := by sorry')
        self.assertEqual(code.count("\n"), 2)
        self.assertEqual(verify.FORBIDDEN.search(code)[0], "sorry")

    def test_nested_comments_and_escaped_strings(self):
        code = verify.lean_code('/- outer /- sorry -/ -/\n#eval "escaped \\\"axiom\\\""\n-- admit\nexample : True := True.intro')
        self.assertIsNone(verify.FORBIDDEN.search(code))

    def test_unterminated_comment_fails(self):
        with self.assertRaises(ValueError):
            verify.lean_code('/- never closed')

    def test_transitive_physics_import_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Fefferman").mkdir()
            (root / "LayerA_Mathematics.lean").write_text('import Fefferman.Bridge\n')
            (root / "Fefferman/Bridge.lean").write_text('import Fefferman.PhysicsGravity\n')
            (root / "Fefferman/PhysicsGravity.lean").write_text('import Init\n')
            with self.assertRaisesRegex(ValueError, "depends on physics"):
                verify.check_sources(verify.sources(root))

    def test_custom_axiom_fails_even_unused(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "LayerA_Mathematics.lean").write_text('axiom unused : False\n')
            with self.assertRaisesRegex(ValueError, "Proof escape"):
                verify.check_sources(verify.sources(root))

    def test_source_hash_is_order_independent_and_change_sensitive(self):
        self.assertEqual(verify.json_hash({"b": 1, "a": 2}), verify.json_hash({"a": 2, "b": 1}))
        self.assertNotEqual(verify.json_hash({"a": 2}), verify.json_hash({"a": 3}))


class ProvenanceTests(unittest.TestCase):
    def fixture(self, root):
        content = b'import Init\n'
        (root / 'LayerA_Mathematics.lean').write_bytes(content)
        (root / 'provenance/archives').mkdir(parents=True)
        archive = root / 'provenance/archives/base.zip'
        with zipfile.ZipFile(archive, 'w') as z:
            z.writestr('base/LayerA_Mathematics.lean', content)
        (root / 'provenance/sources.json').write_text(json.dumps({'sources': [{
            'identity': 'base', 'archive': 'provenance/archives/base.zip', 'sha256': verify.sha256(archive)}]}))
        (root / 'provenance/active_source_origins.json').write_text(json.dumps({'LayerA_Mathematics.lean': {
            'sha256': hashlib.sha256(content).hexdigest(),
            'origins': [{'archive': 'provenance/archives/base.zip', 'member': 'base/LayerA_Mathematics.lean'}]}}))
        (root / 'provenance/rocq_origins.json').write_text('{}')
        return verify.sources(root)

    def test_exact_historical_source_passes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            modules = self.fixture(root)
            self.assertIn('provenance/archives/base.zip', verify.verify_provenance(modules, root))

    def test_modified_active_source_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            modules = self.fixture(root)
            (root / 'LayerA_Mathematics.lean').write_text('import Init\n-- changed\n')
            with self.assertRaisesRegex(ValueError, 'Active source integrity mismatch'):
                verify.verify_provenance(modules, root)

    def test_modified_archive_fails(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            modules = self.fixture(root)
            with (root / 'provenance/archives/base.zip').open('ab') as f:
                f.write(b'changed')
            with self.assertRaisesRegex(ValueError, 'Historical archive integrity mismatch'):
                verify.verify_provenance(modules, root)

    def test_source_manifest_cannot_relabel_a_changed_origin(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            modules = self.fixture(root)
            source = root / 'LayerA_Mathematics.lean'
            source.write_text('import Init\n-- changed\n')
            manifest = root / 'provenance/active_source_origins.json'
            data = json.loads(manifest.read_text())
            data['LayerA_Mathematics.lean']['sha256'] = verify.sha256(source)
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'differs from its historical archive'):
                verify.verify_provenance(modules, root)

    def test_path_escape_fails(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(ValueError, 'escapes repository'):
                verify.repository_path(Path(d), '../outside')


if __name__ == "__main__":
    unittest.main()
