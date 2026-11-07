import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from update_natural_language_links import (
    NaturalLanguageIndexer,
    ReferenceAuditor,
    compute_relative_link,
    github_slug,
    normalize_text,
    spans_overlap,
)


class TestUpdateNaturalLanguageLinks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "natural_language").mkdir()
        (self.root / "critiques").mkdir()

        # Sample natural_language chapter
        self.nl_chapter = self.root / "natural_language" / "03_preference_purpose_and_opportunity_cost.md"
        self.nl_chapter.write_text(
            "# Chapter 3: Preference and Purpose\n\n"
            "### Definition 3.8 (Purposeful Choice Relative to a Relation)\n"
            "An agent acts purposefully...\n\n"
            "### Definition 3.9 (Undominated Purposeful Choice)\n"
            "An undominated choice...\n\n"
            "### Theorem 3.10 (Active Choice Separates Future Branches)\n"
            "Active choices separate...\n",
            encoding="utf-8",
        )

        self.critique_doc = self.root / "critiques" / "sample_critique.md"

        self.indexer = NaturalLanguageIndexer(self.root)
        self.indexer.index()
        self.auditor = ReferenceAuditor(self.indexer, self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_indexer(self):
        self.assertEqual(len(self.indexer.all_items), 3)
        d = self.indexer.find_by_number("3.8")
        self.assertIsNotNone(d)
        self.assertEqual(d.item_type, "Definition")
        self.assertEqual(d.title, "Purposeful Choice Relative to a Relation")
        self.assertEqual(d.anchor_slug, "definition-38-purposeful-choice-relative-to-a-relation")

    def test_github_slug(self):
        self.assertEqual(
            github_slug("### Definition 1.1 (Human Action)"),
            "definition-11-human-action",
        )
        self.assertEqual(
            github_slug("### Theorem 7.16 (Unified Positive Time Preference via Saving Dominance)"),
            "theorem-716-unified-positive-time-preference-via-saving-dominance",
        )
        self.assertEqual(
            github_slug("### Proposition 9.14g (The Cantillon Distribution Theorem)"),
            "proposition-914g-the-cantillon-distribution-theorem",
        )

    def test_compute_relative_link(self):
        decl = self.indexer.find_by_number("3.8")
        # From critiques/
        link_slug = compute_relative_link(self.critique_doc, decl, anchor_style="slug")
        self.assertEqual(
            link_slug,
            "../natural_language/03_preference_purpose_and_opportunity_cost.md#definition-38-purposeful-choice-relative-to-a-relation",
        )
        link_line = compute_relative_link(self.critique_doc, decl, anchor_style="line")
        self.assertEqual(
            link_line,
            "../natural_language/03_preference_purpose_and_opportunity_cost.md#L3",
        )
        # From within same natural_language file
        same_link = compute_relative_link(self.nl_chapter, decl, anchor_style="slug")
        self.assertEqual(
            same_link,
            "#definition-38-purposeful-choice-relative-to-a-relation",
        )

    def test_spans_overlap(self):
        self.assertTrue(spans_overlap((0, 26), (11, 30)))
        self.assertTrue(spans_overlap((11, 26), (11, 30)))
        self.assertFalse(spans_overlap((32, 55), (11, 30)))

    def test_linkify_and_unlink_roundtrip(self):
        original_text = (
            "In human action (Chapter 3, Definitions 3.8–3.9), purposeful choice is required.\n"
            "Furthermore, Theorem 3.10 (Active Choice Separates Future Branches) demonstrates branching.\n"
            "Code block should not be modified:\n"
            "```lean\n"
            "def test := Theorem 3.10\n"
            "```\n"
            "Inline code `Definition 3.8` must remain unlinked.\n"
        )
        self.critique_doc.write_text(original_text, encoding="utf-8")

        added = self.auditor.linkify_file(self.critique_doc, anchor_style="slug")
        self.assertEqual(added, 3)  # 2 for range (3.8, 3.9) + 1 for 3.10

        linkified = self.critique_doc.read_text(encoding="utf-8")
        self.assertIn("[Definitions 3.8](../natural_language/03_preference_purpose_and_opportunity_cost.md#definition-38-purposeful-choice-relative-to-a-relation)–[3.9](../natural_language/03_preference_purpose_and_opportunity_cost.md#definition-39-undominated-purposeful-choice)", linkified)
        self.assertIn("[Theorem 3.10 (Active Choice Separates Future Branches)](../natural_language/03_preference_purpose_and_opportunity_cost.md#theorem-310-active-choice-separates-future-branches)", linkified)
        self.assertIn("`Definition 3.8`", linkified)
        self.assertIn("def test := Theorem 3.10", linkified)

        # Audit should find 0 link issues in linkified file
        issues = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(issues, [])

        # Unlink should restore exact original text
        unlinked = self.auditor.unlink_file(self.critique_doc)
        self.assertEqual(unlinked, 3)
        self.assertEqual(self.critique_doc.read_text(encoding="utf-8"), original_text)

    def test_audit_detects_broken_link_and_slug(self):
        self.critique_doc.write_text(
            "[Definition 3.8](../natural_language/03_preference_purpose_and_opportunity_cost.md#definition-wrong-slug)\n"
            "[Definition 3.8](../natural_language/03_preference_purpose_and_opportunity_cost.md#L999)\n",
            encoding="utf-8",
        )
        issues = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(len(issues), 2)
        types = {i.issue_type for i in issues}
        self.assertIn("broken_slug", types)
        self.assertIn("broken_link", types)

        # Auto-fix should repair both
        fixed = self.auditor.fix_file(self.critique_doc, issues)
        self.assertEqual(fixed, 2)
        re_audited = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(re_audited, [])


if __name__ == "__main__":
    unittest.main()
