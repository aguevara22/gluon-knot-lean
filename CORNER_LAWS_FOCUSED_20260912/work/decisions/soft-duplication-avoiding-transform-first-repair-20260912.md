# Avoiding transform first-run proof repair

Root first21543 failed only in tripleLift_neg: unfolding left a negated function application on the right, so split_ifs did not specialize the conditional underneath its lambda. After funext, an explicit change now exposes pointwise negation before the same unfolding/case proof. All7 public signatures and every other proof are unchanged. Exact first-failed body/prototype/log and identical first drafts are preserved. No premise or mathematical conclusion changes.
