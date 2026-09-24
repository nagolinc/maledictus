import PersistentCollectionsProofs.AxiomAudit

namespace PersistentCollections.AxiomAudit.Regression

theorem proofWithPlaceholder : True := by
  sorry

run_cmd PersistentCollections.AxiomAudit.assertExactAxioms ``PersistentCollections.AxiomAudit.Regression.proofWithPlaceholder PersistentCollections.AxiomAudit.uniqueAxioms

end PersistentCollections.AxiomAudit.Regression
