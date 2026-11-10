import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

from relink_natural_language import (
    NaturalLanguageIndexer,
    ReferenceAuditor,
    compute_relative_link,
    github_slug,
    normalize_text,
)


class TestRelinkNaturalLanguage(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "natural_language").mkdir()
        (self.root / "critiques").mkdir()

        # Sample natural_language chapters
        self.chap8 = self.root / "natural_language" / "08_social_interaction_property_and_exchange.md"
        self.chap8.write_text(
            "# Chapter 8: Social Interaction, Property, and Exchange\n\n"
            "### Theorem 8.22 (Pairwise Mutual Exclusivity of Bilateral Interaction Predicates)\n"
            "The bilateral interaction predicates are mutually exclusive.\n\n"
            "### Theorem 8.27 (The Double Inequality of Voluntary Exchange Theorem)\n"
            "Under voluntary exchange, both parties gain.\n\n"
            "### Proposition 8.28 (Purposefulness on a Binary Trade Menu)\n"
            "Trade is purposeful.\n",
            encoding="utf-8",
        )

        self.chap10 = self.root / "natural_language" / "10_entrepreneurship_credit_and_investment.md"
        self.chap10.write_text(
            "# Chapter 10: Entrepreneurship, Credit, and Investment\n\n"
            "### Theorem 10.5 (Credit Expansion Yields Interest Spread)\n"
            "Note expansion creates divergence.\n",
            encoding="utf-8",
        )

        self.critique_doc = self.root / "critiques" / "sample_critique.md"

        self.indexer = NaturalLanguageIndexer(self.root)
        self.indexer.index()
        self.auditor = ReferenceAuditor(self.indexer, self.root)

    def tearDown(self):
        self.temp.cleanup()

    def test_chapter_indexing_and_slugs(self):
        self.assertIn(8, self.indexer.chapters_by_num)
        self.assertIn(10, self.indexer.chapters_by_num)
        self.assertEqual(
            self.indexer.chapters_by_num[8].anchor_slug,
            "chapter-8-social-interaction-property-and-exchange",
        )
        self.assertEqual(
            self.indexer.chapters_by_num[10].anchor_slug,
            "chapter-10-entrepreneurship-credit-and-investment",
        )

    def test_relink_outdated_number_and_slug(self):
        # Old citation: Theorem 8.24 with old slug
        self.critique_doc.write_text(
            "As proven in [Theorem 8.24](../natural_language/08_social_interaction_property_and_exchange.md#theorem-824-the-double-inequality-of-voluntary-exchange-theorem), exchange occurs.\n",
            encoding="utf-8",
        )
        issues = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(len(issues), 1)
        self.assertEqual(issues[0].issue_type, "outdated_link")
        self.assertIn("Theorem 8.27", issues[0].suggested_value)

        fixed = self.auditor.fix_file(self.critique_doc, issues)
        self.assertEqual(fixed, 1)
        re_audited = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(re_audited, [])
        self.assertIn(
            "[Theorem 8.27](../natural_language/08_social_interaction_property_and_exchange.md#theorem-827-the-double-inequality-of-voluntary-exchange-theorem)",
            self.critique_doc.read_text(encoding="utf-8"),
        )

    def test_relink_legacy_alias(self):
        # Citation targeting old trichotomy title
        self.critique_doc.write_text(
            "Mutual exclusivity is established in [Theorem 8.20](../natural_language/08_social_interaction_property_and_exchange.md#the-three-interaction-categories-partition-theorem).\n",
            encoding="utf-8",
        )
        issues = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(len(issues), 1)
        self.assertIn("Theorem 8.22", issues[0].suggested_value)

        self.auditor.fix_file(self.critique_doc, issues)
        self.assertEqual(self.auditor.audit_file(self.critique_doc), [])
        self.assertIn(
            "[Theorem 8.22](../natural_language/08_social_interaction_property_and_exchange.md#theorem-822-pairwise-mutual-exclusivity-of-bilateral-interaction-predicates)",
            self.critique_doc.read_text(encoding="utf-8"),
        )

    def test_relink_outdated_chapter_slug(self):
        # Outdated chapter heading slug
        self.critique_doc.write_text(
            "See [Chapter 10](../natural_language/10_entrepreneurship_credit_and_investment.md#chapter-10-entrepreneurship-credit-and-capital-markets) for details.\n",
            encoding="utf-8",
        )
        issues = self.auditor.audit_file(self.critique_doc)
        self.assertEqual(len(issues), 1)
        self.assertEqual(issues[0].issue_type, "broken_slug")

        self.auditor.fix_file(self.critique_doc, issues)
        self.assertEqual(self.auditor.audit_file(self.critique_doc), [])
        self.assertIn(
            "[Chapter 10](../natural_language/10_entrepreneurship_credit_and_investment.md#chapter-10-entrepreneurship-credit-and-investment)",
            self.critique_doc.read_text(encoding="utf-8"),
        )


if __name__ == "__main__":
    unittest.main()
