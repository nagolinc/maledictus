import PersistentCollectionsProofs.AxiomAudit

namespace PersistentCollections.AxiomAudit.Regression

axiom untrustedAssumption : True

theorem proofWithProjectAxiom : True := untrustedAssumption

run_cmd PersistentCollections.AxiomAudit.assertExactAxioms ``PersistentCollections.AxiomAudit.Regression.proofWithProjectAxiom PersistentCollections.AxiomAudit.uniqueAxioms

end PersistentCollections.AxiomAudit.Regression
