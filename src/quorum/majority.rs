// Copyright 2020 TiKV Project Authors. Licensed under Apache-2.0.

use super::{AckedIndexer, Index, VoteResult};
use crate::{DefaultHashBuilder, HashSet};

use std::collections::hash_set::Iter;
use std::fmt::Formatter;
use std::ops::{Deref, DerefMut};
use std::cmp;
#[cfg(not(feature = "aeneas"))]
use std::mem::MaybeUninit;
#[cfg(not(feature = "aeneas"))]
use std::slice;

/// A set of IDs that uses majority quorums to make decisions.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Configuration {
    voters: HashSet<u64>,
}

impl std::fmt::Display for Configuration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({})",
            self.voters
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(" ")
        )
    }
}

impl Configuration {
    /// Creates a new configuration using the given IDs.
    pub fn new(voters: HashSet<u64>) -> Configuration {
        Configuration { voters }
    }

    /// Creates an empty configuration with given capacity.
    pub fn with_capacity(cap: usize) -> Configuration {
        Configuration {
            voters: HashSet::with_capacity_and_hasher(cap, DefaultHashBuilder::default()),
        }
    }

    /// Returns an iterator over voters.
    pub fn ids(&self) -> Iter<'_, u64> {
        self.voters.iter()
    }

    /// Returns the MajorityConfig as a sorted slice.
    pub fn slice(&self) -> Vec<u64> {
        let mut voters = self.raw_slice();
        voters.sort_unstable();
        voters
    }

    /// Returns the MajorityConfig as a slice.
    pub fn raw_slice(&self) -> Vec<u64> {
        self.voters.iter().cloned().collect()
    }

    /// Computes the committed index from those supplied via the
    /// provided AckedIndexer (for the active config).
    ///
    /// The bool flag indicates whether the index is computed by group commit algorithm
    /// successfully.
    ///
    /// Eg. If the matched indexes are `[2,2,2,4,5]`, it will return `2`.
    /// If the matched indexes and groups are `[(1, 1), (2, 2), (3, 2)]`, it will return `1`.
    ///
    /// When compiled with `--features aeneas` the unsafe stack-array optimisation is
    /// replaced by a straightforward `Vec` allocation so that Aeneas (the Rust→Lean
    /// translation tool) can process this function.  The two implementations are
    /// semantically identical; the only difference is memory allocation strategy.
    #[cfg(not(feature = "aeneas"))]
    pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool) {
        if self.voters.is_empty() {
            // This plays well with joint quorums which, when one half is the zero
            // MajorityConfig, should behave like the other half.
            return (u64::MAX, true);
        }

        let mut stack_arr: [MaybeUninit<Index>; 7] = unsafe { MaybeUninit::uninit().assume_init() };
        let mut heap_arr;
        let matched = if self.voters.len() <= 7 {
            for (i, v) in self.voters.iter().enumerate() {
                stack_arr[i] = MaybeUninit::new(l.acked_index(*v).unwrap_or_default());
            }
            unsafe {
                slice::from_raw_parts_mut(stack_arr.as_mut_ptr() as *mut _, self.voters.len())
            }
        } else {
            let mut buf = Vec::with_capacity(self.voters.len());
            for v in &self.voters {
                buf.push(l.acked_index(*v).unwrap_or_default());
            }
            heap_arr = Some(buf);
            heap_arr.as_mut().unwrap().as_mut_slice()
        };
        // Reverse sort.
        matched.sort_by(|a, b| b.index.cmp(&a.index));

        let quorum = crate::majority(matched.len());
        let quorum_index = matched[quorum - 1];
        if !use_group_commit {
            return (quorum_index.index, false);
        }
        let (quorum_commit_index, mut checked_group_id) =
            (quorum_index.index, quorum_index.group_id);
        let mut single_group = true;
        for m in matched.iter() {
            if m.group_id == 0 {
                single_group = false;
                continue;
            }
            if checked_group_id == 0 {
                checked_group_id = m.group_id;
                continue;
            }
            if checked_group_id == m.group_id {
                continue;
            }
            return (cmp::min(m.index, quorum_commit_index), true);
        }
        if single_group {
            (quorum_commit_index, false)
        } else {
            (matched.last().unwrap().index, false)
        }
    }

    /// Safe alternative to the above, enabled by `--features aeneas`.
    ///
    /// Semantically identical to the `#[cfg(not(feature = "aeneas"))]` version above.
    /// Uses a plain `Vec` allocation instead of the `MaybeUninit` stack-array
    /// optimisation so that Aeneas can translate this function to Lean without
    /// encountering any `unsafe` blocks.
    #[cfg(feature = "aeneas")]
    pub fn committed_index(&self, use_group_commit: bool, l: &impl AckedIndexer) -> (u64, bool) {
        if self.voters.is_empty() {
            return (u64::MAX, true);
        }

        // Collect acked indices into a Vec — no unsafe code.
        let mut matched: Vec<Index> = self
            .voters
            .iter()
            .map(|v| l.acked_index(*v).unwrap_or_default())
            .collect();
        // Reverse sort.
        matched.sort_by(|a, b| b.index.cmp(&a.index));

        let quorum = crate::majority(matched.len());
        let quorum_index = matched[quorum - 1];
        if !use_group_commit {
            return (quorum_index.index, false);
        }
        let (quorum_commit_index, mut checked_group_id) =
            (quorum_index.index, quorum_index.group_id);
        let mut single_group = true;
        for m in matched.iter() {
            if m.group_id == 0 {
                single_group = false;
                continue;
            }
            if checked_group_id == 0 {
                checked_group_id = m.group_id;
                continue;
            }
            if checked_group_id == m.group_id {
                continue;
            }
            return (cmp::min(m.index, quorum_commit_index), true);
        }
        if single_group {
            (quorum_commit_index, false)
        } else {
            (matched.last().unwrap().index, false)
        }
    }

    /// Takes a mapping of voters to yes/no (true/false) votes and returns
    /// a result indicating whether the vote is pending (i.e. neither a quorum of
    /// yes/no has been reached), won (a quorum of yes has been reached), or lost (a
    /// quorum of no has been reached).
    pub fn vote_result(&self, check: impl Fn(u64) -> Option<bool>) -> VoteResult {
        if self.voters.is_empty() {
            // By convention, the elections on an empty config win. This comes in
            // handy with joint quorums because it'll make a half-populated joint
            // quorum behave like a majority quorum.
            return VoteResult::Won;
        }

        let (mut yes, mut missing) = (0, 0);
        for v in &self.voters {
            match check(*v) {
                Some(true) => yes += 1,
                None => missing += 1,
                _ => (),
            }
        }
        let q = crate::majority(self.voters.len());
        if yes >= q {
            VoteResult::Won
        } else if yes + missing >= q {
            VoteResult::Pending
        } else {
            VoteResult::Lost
        }
    }

    /// Describe returns a (multi-line) representation of the commit indexes for the
    /// given lookuper.
    /// Including `Index`,`Id` and the number of smaller index (represented as the bar)
    ///
    /// Print `?` if `Index` is not exist.
    ///
    /// e.g.
    /// ```txt
    ///             idx
    /// x>          100 (id=1)
    /// xx>         101 (id=2)
    /// >            99 (id=3)
    /// 100
    /// ```
    #[cfg(test)]
    pub(crate) fn describe(&self, l: &impl AckedIndexer) -> String {
        use std::fmt::Write;

        let n = self.voters.len();
        if n == 0 {
            return "<empty majority quorum>".to_string();
        }

        struct Tup {
            id: u64,
            idx: Option<Index>,
            // length of bar displayed for this Tup
            bar: usize,
        }

        // Below, populate .bar so that the i-th largest commit index has bar i (we
        // plot this as sort of a progress bar). The actual code is a bit more
        // complicated and also makes sure that equal index => equal bar.

        let mut info = Vec::with_capacity(n);

        for &id in &self.voters {
            let idx = l.acked_index(id);
            info.push(Tup { id, idx, bar: 0 })
        }

        info.sort_by(|a, b| {
            (a.idx.unwrap_or_default().index, a.id).cmp(&(b.idx.unwrap_or_default().index, b.id))
        });

        for i in 0..n {
            if i > 0
                && info[i - 1].idx.unwrap_or_default().index < info[i].idx.unwrap_or_default().index
            {
                info[i].bar = i;
            }
        }

        info.sort_by(|a, b| a.id.cmp(&b.id));

        let mut buf = String::new();
        buf.push_str(" ".repeat(n).as_str());
        buf.push_str("    idx\n");

        for tup in info {
            match tup.idx {
                Some(idx) => {
                    buf.push_str("x".repeat(tup.bar).as_str());
                    buf.push('>');
                    buf.push_str(" ".repeat(n - tup.bar).as_str());
                    writeln!(buf, " {:>5}    (id={})", format!("{}", idx), tup.id)
                        .expect("Error occurred while trying to write in String");
                }
                None => {
                    buf.push('?');
                    buf.push_str(" ".repeat(n).as_str());
                    writeln!(
                        buf,
                        " {:>5}    (id={})",
                        format!("{}", Index::default()),
                        tup.id
                    )
                    .expect("Error occurred while trying to write in String");
                }
            }
        }
        buf
    }
}

impl Deref for Configuration {
    type Target = HashSet<u64>;

    #[inline]
    fn deref(&self) -> &HashSet<u64> {
        &self.voters
    }
}

impl DerefMut for Configuration {
    #[inline]
    fn deref_mut(&mut self) -> &mut HashSet<u64> {
        &mut self.voters
    }
}

// ---------------------------------------------------------------------------
// Task 8 Route B — committed_index correspondence test
//
// These 8 cases mirror FVSquad/CommittedIndexCorrespondence.lean exactly.
// Each case specifies a voter set and an acked-index map, and the expected
// committed index returned by `committed_index(false, &acker)`.
//
// The Lean model `committedIndex voters acked` sorts acked values descending and
// returns the element at position `majority(|voters|) - 1`.  The Rust function
// `Configuration::committed_index(false, l)` does exactly the same for
// `use_group_commit = false`.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum::{AckIndexer, Index};
    use crate::{HashMap, HashSet};

    // Build an AckIndexer from a list of (voter_id, acked_index) pairs.
    // Missing entries are absent from the map; `unwrap_or_default()` in Rust
    // gives Index { index: 0, group_id: 0 }, mirroring the Lean default of 0.
    fn make_acker(pairs: &[(u64, u64)]) -> AckIndexer {
        let mut m = AckIndexer::default();
        for &(id, idx) in pairs {
            m.insert(
                id,
                Index {
                    index: idx,
                    group_id: 0,
                },
            );
        }
        m
    }

    #[test]
    fn test_committed_index_correspondence() {
        // (voters, acked_pairs, expected)
        // Mirrors formal-verification/tests/committed_index/cases.json exactly.
        let cases: &[(&[u64], &[(u64, u64)], u64)] = &[
            // Case 1: single voter, acked=5 → 5
            // sorted=[5], majority(1)=1, result=sorted[0]=5
            (&[1], &[(1, 5)], 5),
            // Case 2: two voters, acked={1→5, 2→3} → 3
            // sorted=[5,3], majority(2)=2, result=sorted[1]=3
            (&[1, 2], &[(1, 5), (2, 3)], 3),
            // Case 3: three voters, acked={1→2, 2→4, 3→6} → 4
            // sorted=[6,4,2], majority(3)=2, result=sorted[1]=4
            (&[1, 2, 3], &[(1, 2), (2, 4), (3, 6)], 4),
            // Case 4: three voters, all acked=2 → 2
            (&[1, 2, 3], &[(1, 2), (2, 2), (3, 2)], 2),
            // Case 5: three voters, all acked=0 → 0
            (&[1, 2, 3], &[(1, 0), (2, 0), (3, 0)], 0),
            // Case 6: five voters, acked={1→1,…,5→5} → 3
            // sorted=[5,4,3,2,1], majority(5)=3, result=sorted[2]=3
            (&[1, 2, 3, 4, 5], &[(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)], 3),
            // Case 7: two voters, voter 2 missing → defaults to 0 → result=0
            // sorted=[10,0], majority(2)=2, result=sorted[1]=0
            (&[1, 2], &[(1, 10)], 0),
            // Case 8: three voters, all acked=10 → 10
            (&[1, 2, 3], &[(1, 10), (2, 10), (3, 10)], 10),
        ];

        for (i, &(voter_ids, acked_pairs, expected)) in cases.iter().enumerate() {
            let voters: HashSet<u64> = voter_ids.iter().copied().collect();
            let cfg = Configuration::new(voters);
            let acker = make_acker(acked_pairs);
            let (result, _) = cfg.committed_index(false, &acker);
            assert_eq!(
                result,
                expected,
                "case {}: committed_index voters={voter_ids:?} acked={acked_pairs:?} \
                 = {result}, want {expected}",
                i + 1
            );
        }
    }

    // ---------------------------------------------------------------------------
    // Task 8 Route B — vote_result correspondence test
    //
    // These 12 cases mirror FVSquad/VoteResultCorrespondence.lean exactly.
    // Each case specifies voters, yes-voters, no-voters, and the expected VoteResult.
    // Voters absent from both lists contribute None (missing) to the check function.
    // ---------------------------------------------------------------------------
    #[test]
    fn test_vote_result_correspondence() {
        use crate::quorum::VoteResult;
        // (voters, yes_ids, no_ids, expected)
        // Mirrors formal-verification/tests/vote_result/cases.json exactly.
        let cases: &[(&[u64], &[u64], &[u64], VoteResult)] = &[
            // Case 1: empty voters → Won (convention)
            (&[], &[], &[], VoteResult::Won),
            // Case 2: single voter yes → Won
            (&[1], &[1], &[], VoteResult::Won),
            // Case 3: single voter no → Lost
            (&[1], &[], &[1], VoteResult::Lost),
            // Case 4: single voter missing → Pending (yes=0 < q=1; yes+missing=1 ≥ 1)
            (&[1], &[], &[], VoteResult::Pending),
            // Case 5: 3 voters, 2 yes, 1 no → Won (yes=2 ≥ majority(3)=2)
            (&[1, 2, 3], &[1, 2], &[3], VoteResult::Won),
            // Case 6: 3 voters, 1 yes, 1 no, 1 missing → Pending (1+1=2 ≥ 2)
            (&[1, 2, 3], &[1], &[2], VoteResult::Pending),
            // Case 7: 3 voters, 0 yes, 1 missing, 2 no → Lost (0+1=1 < 2)
            (&[1, 2, 3], &[], &[1, 2], VoteResult::Lost),
            // Case 8: 3 voters, all yes → Won
            (&[1, 2, 3], &[1, 2, 3], &[], VoteResult::Won),
            // Case 9: 3 voters, all no → Lost
            (&[1, 2, 3], &[], &[1, 2, 3], VoteResult::Lost),
            // Case 10: 5 voters, 3 yes → Won (yes=3=majority(5)=3)
            (&[1, 2, 3, 4, 5], &[1, 2, 3], &[4, 5], VoteResult::Won),
            // Case 11: 5 voters, 2 yes, 1 missing, 2 no → Pending (2+1=3 ≥ 3)
            (&[1, 2, 3, 4, 5], &[1, 2], &[4, 5], VoteResult::Pending),
            // Case 12: 5 voters, 2 yes, 3 no → Lost (2+0=2 < 3)
            (&[1, 2, 3, 4, 5], &[1, 2], &[3, 4, 5], VoteResult::Lost),
        ];

        for (i, &(voter_ids, yes_ids, no_ids, expected)) in cases.iter().enumerate() {
            let voters: HashSet<u64> = voter_ids.iter().copied().collect();
            let cfg = Configuration::new(voters);
            let result = cfg.vote_result(|id| {
                if yes_ids.iter().any(|&y| y == id) {
                    Some(true)
                } else if no_ids.iter().any(|&n| n == id) {
                    Some(false)
                } else {
                    None
                }
            });
            assert_eq!(
                result,
                expected,
                "case {}: vote_result voters={voter_ids:?} yes={yes_ids:?} no={no_ids:?} \
                 = {result:?}, want {expected:?}",
                i + 1
            );
        }
    }

    // ---------------------------------------------------------------------------
    // Task 8 Route B — has_quorum correspondence test
    //
    // These 12 cases mirror FVSquad/HasQuorumCorrespondence.lean exactly.
    // `has_quorum` is modelled as `vote_result(check) == Won` where
    // check(id) = Some(true) if id ∈ set, else None.
    // ---------------------------------------------------------------------------
    #[test]
    fn test_has_quorum_correspondence() {
        // (voters, set_ids, expected)
        // Mirrors formal-verification/tests/has_quorum/cases.json exactly.
        let cases: &[(&[u64], &[u64], bool)] = &[
            // Case 1: empty voters → true
            (&[], &[], true),
            // Case 2: single voter in set → true
            (&[1], &[1], true),
            // Case 3: single voter not in set → false
            (&[1], &[], false),
            // Case 4: 3 voters, 2 in set → true (2 ≥ majority(3)=2)
            (&[1, 2, 3], &[1, 2], true),
            // Case 5: 3 voters, 1 in set → false (1 < 2)
            (&[1, 2, 3], &[1], false),
            // Case 6: 3 voters, all in set → true
            (&[1, 2, 3], &[1, 2, 3], true),
            // Case 7: 3 voters, none in set → false
            (&[1, 2, 3], &[], false),
            // Case 8: 5 voters, 3 in set → true (3=majority(5)=3)
            (&[1, 2, 3, 4, 5], &[1, 2, 3], true),
            // Case 9: 5 voters, 2 in set → false (2 < 3)
            (&[1, 2, 3, 4, 5], &[1, 2], false),
            // Case 10: 5 voters, 4 in set → true
            (&[1, 2, 3, 4, 5], &[1, 2, 3, 4], true),
            // Case 11: 5 voters, non-consecutive 4 in set → true
            (&[1, 2, 3, 4, 5], &[1, 2, 4, 5], true),
            // Case 12: 5 voters, 1 in set → false (1 < 3)
            (&[1, 2, 3, 4, 5], &[5], false),
        ];

        for (i, &(voter_ids, set_ids, expected)) in cases.iter().enumerate() {
            let voters: HashSet<u64> = voter_ids.iter().copied().collect();
            let cfg = Configuration::new(voters);
            let set: HashSet<u64> = set_ids.iter().copied().collect();
            let result = cfg.vote_result(|id| set.get(&id).map(|_| true)) == crate::quorum::VoteResult::Won;
            assert_eq!(
                result,
                expected,
                "case {}: has_quorum voters={voter_ids:?} set={set_ids:?} \
                 = {result}, want {expected}",
                i + 1
            );
        }
    }
}
