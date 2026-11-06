import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from update_theorem_links import LeanIndexer, MarkdownLinkAuditor


class TestMarkdownLinkAuditor(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "Praxeology").mkdir()
        (self.root / "spec").mkdir()
        self.source = self.root / "Praxeology" / "Sample.lean"
        self.source.write_text("theorem present : True := by trivial\n", encoding="utf-8")
        self.doc = self.root / "spec" / "sample.md"

    def tearDown(self):
        self.temp.cleanup()

    def auditor(self, add_missing=False):
        indexer = LeanIndexer(self.root)
        indexer.index()
        return MarkdownLinkAuditor(indexer, self.root, add_missing=add_missing)

    def test_updates_line_anchor_using_full_relative_path(self):
        self.doc.write_text("[present](../Praxeology/Sample.lean#L99)\n", encoding="utf-8")
        issues = self.auditor().audit_file(self.doc)
        self.assertEqual(len(issues), 1)
        self.assertIn("../Praxeology/Sample.lean#L1", issues[0].new_link)
        self.assertIn("Line shift", issues[0].reason)

    def test_checks_file_only_links(self):
        self.doc.write_text("[Sample.lean](../Praxeology/Sample.lean)\n", encoding="utf-8")
        self.assertEqual(self.auditor().audit_file(self.doc), [])

    def test_reports_missing_lean_file(self):
        self.doc.write_text("[missing](../Praxeology/Missing.lean)\n", encoding="utf-8")
        issues = self.auditor().audit_file(self.doc)
        self.assertEqual(len(issues), 1)
        self.assertIn("ERROR: Lean file does not exist", issues[0].reason)
        self.assertEqual(issues[0].new_link, "")

    def test_reports_unknown_explicit_declaration(self):
        self.doc.write_text("[ghost](../Praxeology/Sample.lean#L1)\n", encoding="utf-8")
        issues = self.auditor().audit_file(self.doc)
        self.assertEqual(len(issues), 1)
        self.assertIn("ERROR: declaration ghost", issues[0].reason)

    def test_reports_ambiguous_declaration_in_wrong_target_file(self):
        other = self.root / "Praxeology" / "Other.lean"
        other.write_text("theorem duplicated : True := by trivial\n", encoding="utf-8")
        self.source.write_text("theorem duplicated : True := by trivial\n", encoding="utf-8")
        self.doc.write_text("[duplicated](../Praxeology/Absent.lean#L1)\n", encoding="utf-8")
        issues = self.auditor().audit_file(self.doc)
        self.assertEqual(len(issues), 1)
        self.assertIn("ERROR: ambiguous declaration duplicated", issues[0].reason)


if __name__ == "__main__":
    unittest.main()
