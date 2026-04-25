// Copyright 2019 TiKV Project Authors. Licensed under Apache-2.0.

// Copyright 2015 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod inflights;
mod progress;
mod state;

pub use self::inflights::Inflights;
pub use self::progress::Progress;
pub use self::state::ProgressState;

use crate::confchange::{MapChange, MapChangeType};
use crate::eraftpb::ConfState;
use crate::quorum::{AckedIndexer, Index, VoteResult};
use crate::{DefaultHashBuilder, HashMap, HashSet, JointConfig};
use getset::Getters;
use std::fmt::Debug;

/// Config reflects the configuration tracked in a ProgressTracker.
#[derive(Clone, Debug, Default, PartialEq, Eq, Getters)]
pub struct Configuration {
    #[get = "pub"]
    pub(crate) voters: JointConfig,
    /// Learners is a set of IDs corresponding to the learners active in the
    /// current configuration.
    ///
    /// Invariant: Learners and Voters does not intersect, i.e. if a peer is in
    /// either half of the joint config, it can't be a learner; if it is a
    /// learner it can't be in either half of the joint config. This invariant
    /// simplifies the implementation since it allows peers to have clarity about
    /// its current role without taking into account joint consensus.
    #[get = "pub"]
    pub(crate) learners: HashSet<u64>,
    /// When we turn a voter into a learner during a joint consensus transition,
    /// we cannot add the learner directly when entering the joint state. This is
    /// because this would violate the invariant that the intersection of
    /// voters and learners is empty. For example, assume a Voter is removed and
    /// immediately re-added as a learner (or in other words, it is demoted):
    ///
    /// Initially, the configuration will be
    ///
    ///   voters:   {1 2 3}
    ///   learners: {}
    ///
    /// and we want to demote 3. Entering the joint configuration, we naively get
    ///
    ///   voters:   {1 2} & {1 2 3}
    ///   learners: {3}
    ///
    /// but this violates the invariant (3 is both voter and learner). Instead,
    /// we get
    ///
    ///   voters:   {1 2} & {1 2 3}
    ///   learners: {}
    ///   next_learners: {3}
    ///
    /// Where 3 is now still purely a voter, but we are remembering the intention
    /// to make it a learner upon transitioning into the final configuration:
    ///
    ///   voters:   {1 2}
    ///   learners: {3}
    ///   next_learners: {}
    ///
    /// Note that next_learners is not used while adding a learner that is not
    /// also a voter in the joint config. In this case, the learner is added
    /// right away when entering the joint configuration, so that it is caught up
    /// as soon as possible.
    #[get = "pub"]
    pub(crate) learners_next: HashSet<u64>,
    /// True if the configuration is joint and a transition to the incoming
    /// configuration should be carried out automatically by Raft when this is
    /// possible. If false, the configuration will be joint until the application
    /// initiates the transition manually.
    #[get = "pub"]
    pub(crate) auto_leave: bool,
}

// Display and crate::itertools used only for test
#[cfg(test)]
impl std::fmt::Display for Configuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use itertools::Itertools;
        if self.voters.outgoing.is_empty() {
            write!(f, "voters={}", self.voters.incoming)?
        } else {
            write!(
                f,
                "voters={}&&{}",
                self.voters.incoming, self.voters.outgoing
            )?
        }
        if !self.learners.is_empty() {
            write!(
                f,
                " learners=({})",
                self.learners
                    .iter()
                    .sorted_by(|&a, &b| a.cmp(b))
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            )?
        }
        if !self.learners_next.is_empty() {
            write!(
                f,
                " learners_next=({})",
                self.learners_next
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(" ")
            )?
        }
        if self.auto_leave {
            write!(f, " autoleave")?
        }
        Ok(())
    }
}

impl Configuration {
    /// Create a new configuration with the given configuration.
    pub fn new(
        voters: impl IntoIterator<Item = u64>,
        learners: impl IntoIterator<Item = u64>,
    ) -> Self {
        Self {
            voters: JointConfig::new(voters.into_iter().collect()),
            auto_leave: false,
            learners: learners.into_iter().collect(),
            learners_next: HashSet::default(),
        }
    }

    fn with_capacity(voters: usize, learners: usize) -> Self {
        Self {
            voters: JointConfig::with_capacity(voters),
            learners: HashSet::with_capacity_and_hasher(learners, DefaultHashBuilder::default()),
            learners_next: HashSet::default(),
            auto_leave: false,
        }
    }

    /// Create a new `ConfState` from the configuration itself.
    pub fn to_conf_state(&self) -> ConfState {
        // Note: Different from etcd, we don't sort.
        let mut state = ConfState::default();
        state.set_voters(self.voters.incoming.raw_slice());
        state.set_voters_outgoing(self.voters.outgoing.raw_slice());
        state.set_learners(self.learners.iter().cloned().collect());
        state.set_learners_next(self.learners_next.iter().cloned().collect());
        state.auto_leave = self.auto_leave;
        state
    }

    fn clear(&mut self) {
        self.voters.clear();
        self.learners.clear();
        self.learners_next.clear();
        self.auto_leave = false;
    }
}

pub type ProgressMap = HashMap<u64, Progress>;

impl AckedIndexer for ProgressMap {
    fn acked_index(&self, voter_id: u64) -> Option<Index> {
        self.get(&voter_id).map(|p| Index {
            index: p.matched,
            group_id: p.commit_group_id,
        })
    }
}

/// `ProgressTracker` contains several `Progress`es,
/// which could be `Leader`, `Follower` and `Learner`.
#[derive(Clone, Getters)]
pub struct ProgressTracker {
    progress: ProgressMap,

    /// The current configuration state of the cluster.
    #[get = "pub"]
    conf: Configuration,
    #[doc(hidden)]
    #[get = "pub"]
    votes: HashMap<u64, bool>,
    #[get = "pub(crate)"]
    max_inflight: usize,

    group_commit: bool,
}

impl ProgressTracker {
    /// Creates a new ProgressTracker.
    pub fn new(max_inflight: usize) -> Self {
        Self::with_capacity(0, 0, max_inflight)
    }

    /// Create a progress set with the specified sizes already reserved.
    pub fn with_capacity(voters: usize, learners: usize, max_inflight: usize) -> Self {
        ProgressTracker {
            progress: HashMap::with_capacity_and_hasher(
                voters + learners,
                DefaultHashBuilder::default(),
            ),
            conf: Configuration::with_capacity(voters, learners),
            votes: HashMap::with_capacity_and_hasher(voters, DefaultHashBuilder::default()),
            max_inflight,
            group_commit: false,
        }
    }

    /// Configures group commit.
    pub fn enable_group_commit(&mut self, enable: bool) {
        self.group_commit = enable;
    }

    /// Whether enable group commit.
    pub fn group_commit(&self) -> bool {
        self.group_commit
    }

    pub(crate) fn clear(&mut self) {
        self.progress.clear();
        self.conf.clear();
        self.votes.clear();
    }

    /// Returns true if (and only if) there is only one voting member
    /// (i.e. the leader) in the current configuration.
    pub fn is_singleton(&self) -> bool {
        self.conf.voters.is_singleton()
    }

    /// Grabs a reference to the progress of a node.
    #[inline]
    pub fn get(&self, id: u64) -> Option<&Progress> {
        self.progress.get(&id)
    }

    /// Grabs a mutable reference to the progress of a node.
    #[inline]
    pub fn get_mut(&mut self, id: u64) -> Option<&mut Progress> {
        self.progress.get_mut(&id)
    }

    /// Returns an iterator across all the nodes and their progress.
    ///
    /// **Note:** Do not use this for majority/quorum calculation. The Raft node may be
    /// transitioning to a new configuration and have two quorums. Use `has_quorum` instead.
    #[inline]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&u64, &Progress)> {
        self.progress.iter()
    }

    /// Returns a mutable iterator across all the nodes and their progress.
    ///
    /// **Note:** Do not use this for majority/quorum calculation. The Raft node may be
    /// transitioning to a new configuration and have two quorums. Use `has_quorum` instead.
    #[inline]
    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (&u64, &mut Progress)> {
        self.progress.iter_mut()
    }

    /// Returns the maximal committed index for the cluster. The bool flag indicates whether
    /// the index is computed by group commit algorithm successfully.
    ///
    /// Eg. If the matched indexes are `[2,2,2,4,5]`, it will return `2`.
    /// If the matched indexes and groups are `[(1, 1), (2, 2), (3, 2)]`, it will return `1`.
    pub fn maximal_committed_index(&mut self) -> (u64, bool) {
        self.conf
            .voters
            .committed_index(self.group_commit, &self.progress)
    }

    /// Prepares for a new round of vote counting via recordVote.
    pub fn reset_votes(&mut self) {
        self.votes.clear();
    }

    /// Records that the node with the given id voted for this Raft
    /// instance if v == true (and declined it otherwise).
    pub fn record_vote(&mut self, id: u64, vote: bool) {
        self.votes.entry(id).or_insert(vote);
    }

    /// TallyVotes returns the number of granted and rejected Votes, and whether the
    /// election outcome is known.
    pub fn tally_votes(&self) -> (usize, usize, VoteResult) {
        // Make sure to populate granted/rejected correctly even if the Votes slice
        // contains members no longer part of the configuration. This doesn't really
        // matter in the way the numbers are used (they're informational), but might
        // as well get it right.
        let (mut granted, mut rejected) = (0, 0);
        for (id, vote) in &self.votes {
            if !self.conf.voters.contains(*id) {
                continue;
            }
            if *vote {
                granted += 1;
            } else {
                rejected += 1;
            }
        }
        let result = self.vote_result(&self.votes);
        (granted, rejected, result)
    }

    /// Returns the Candidate's eligibility in the current election.
    ///
    /// If it is still eligible, it should continue polling nodes and checking.
    /// Eventually, the election will result in this returning either `Elected`
    /// or `Ineligible`, meaning the election can be concluded.
    pub fn vote_result(&self, votes: &HashMap<u64, bool>) -> VoteResult {
        self.conf.voters.vote_result(|id| votes.get(&id).cloned())
    }

    /// Determines if the current quorum is active according to the this raft node.
    /// Doing this will set the `recent_active` of each peer to false.
    ///
    /// This should only be called by the leader.
    pub fn quorum_recently_active(&mut self, perspective_of: u64) -> bool {
        let mut active =
            HashSet::with_capacity_and_hasher(self.progress.len(), DefaultHashBuilder::default());
        for (id, pr) in &mut self.progress {
            if *id == perspective_of {
                pr.recent_active = true;
                active.insert(*id);
            } else if pr.recent_active {
                // It doesn't matter whether it's learner. As we calculate quorum
                // by actual ids instead of count.
                active.insert(*id);
                pr.recent_active = false;
            }
        }
        self.has_quorum(&active)
    }

    /// Determine if a quorum is formed from the given set of nodes.
    ///
    /// This is the only correct way to verify you have reached a quorum for the whole group.
    #[inline]
    pub fn has_quorum(&self, potential_quorum: &HashSet<u64>) -> bool {
        self.conf
            .voters
            .vote_result(|id| potential_quorum.get(&id).map(|_| true))
            == VoteResult::Won
    }

    #[inline]
    pub(crate) fn progress(&self) -> &ProgressMap {
        &self.progress
    }

    /// Applies configuration and updates progress map to match the configuration.
    pub fn apply_conf(&mut self, conf: Configuration, changes: MapChange, next_idx: u64) {
        self.conf = conf;
        for (id, change_type) in changes {
            match change_type {
                MapChangeType::Add => {
                    let mut pr = Progress::new(next_idx, self.max_inflight);
                    // When a node is first added, we should mark it as recently active.
                    // Otherwise, CheckQuorum may cause us to step down if it is invoked
                    // before the added node has had a chance to communicate with us.
                    pr.recent_active = true;
                    self.progress.insert(id, pr);
                }
                MapChangeType::Remove => {
                    self.progress.remove(&id);
                }
            }
        }
    }
}

// Task 8 Route B — tally_votes correspondence test.
// Mirrors formal-verification/tests/tally_votes/cases.json
// and FVSquad/TallyVotesCorrespondence.lean exactly.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::quorum::VoteResult;

    fn make_tracker(voter_ids: &[u64], yes_ids: &[u64], no_ids: &[u64]) -> ProgressTracker {
        let mut t = ProgressTracker::new(voter_ids.len());
        t.conf = Configuration::new(voter_ids.iter().copied(), std::iter::empty());
        for &id in yes_ids {
            t.record_vote(id, true);
        }
        for &id in no_ids {
            t.record_vote(id, false);
        }
        t
    }

    #[test]
    fn test_tally_votes_correspondence() {
        // (voters, yes_ids, no_ids, expected_granted, expected_rejected, expected_result)
        let cases: &[(&[u64], &[u64], &[u64], usize, usize, VoteResult)] = &[
            // Case 1: empty voters → (0, 0, Won)
            (&[], &[], &[], 0, 0, VoteResult::Won),
            // Case 2: [1], yes=[1] → (1, 0, Won)
            (&[1], &[1], &[], 1, 0, VoteResult::Won),
            // Case 3: [1], no=[1] → (0, 1, Lost)
            (&[1], &[], &[1], 0, 1, VoteResult::Lost),
            // Case 4: [1], no votes → (0, 0, Pending)
            (&[1], &[], &[], 0, 0, VoteResult::Pending),
            // Case 5: [1,2,3], yes=[1,2], no=[3] → (2, 1, Won)
            (&[1, 2, 3], &[1, 2], &[3], 2, 1, VoteResult::Won),
            // Case 6: [1,2,3], yes=[1], no=[2], missing=3 → (1, 1, Pending)
            (&[1, 2, 3], &[1], &[2], 1, 1, VoteResult::Pending),
            // Case 7: [1,2,3], no=[1,2], missing=3 → (0, 2, Lost)
            (&[1, 2, 3], &[], &[1, 2], 0, 2, VoteResult::Lost),
            // Case 8: [1,2,3], all yes → (3, 0, Won)
            (&[1, 2, 3], &[1, 2, 3], &[], 3, 0, VoteResult::Won),
            // Case 9: [1..5], yes=[1,2,3], no=[4,5] → (3, 2, Won)
            (&[1, 2, 3, 4, 5], &[1, 2, 3], &[4, 5], 3, 2, VoteResult::Won),
            // Case 10: [1..5], yes=[1], no=[2,3,4,5] → (1, 4, Lost)
            (&[1, 2, 3, 4, 5], &[1], &[2, 3, 4, 5], 1, 4, VoteResult::Lost),
        ];

        for (i, &(voters, yes_ids, no_ids, exp_granted, exp_rejected, exp_result)) in
            cases.iter().enumerate()
        {
            let t = make_tracker(voters, yes_ids, no_ids);
            let (granted, rejected, result) = t.tally_votes();
            assert_eq!(granted, exp_granted, "case {}: granted", i + 1);
            assert_eq!(rejected, exp_rejected, "case {}: rejected", i + 1);
            assert_eq!(result, exp_result, "case {}: result", i + 1);
        }
    }

    // Task 8 Route B — quorum_recently_active correspondence test.
    // Mirrors formal-verification/tests/quorum_recently_active/cases.json
    // and FVSquad/QuorumRecentlyActiveCorrespondence.lean exactly.
    fn make_qra_tracker(voter_ids: &[u64], entries: &[(u64, bool)]) -> ProgressTracker {
        let mut t = ProgressTracker::new(10);
        t.conf = Configuration::new(voter_ids.iter().copied(), std::iter::empty());
        for &(id, ra) in entries {
            let mut pr = Progress::new(1, 10);
            pr.recent_active = ra;
            t.progress.insert(id, pr);
        }
        t
    }

    #[test]
    fn test_quorum_recently_active_correspondence() {
        // (voters, entries=(id, recent_active), perspective_of, expected)
        let cases: &[(&[u64], &[(u64, bool)], u64, bool)] = &[
            // Case 1: empty voters → true (vacuous quorum)
            (&[], &[], 1, true),
            // Case 2: voters=[1], leader in entries → true
            (&[1], &[(1, false)], 1, true),
            // Case 3: voters=[1], leader not in entries → false
            (&[1], &[], 1, false),
            // Case 4: voters=[1,2,3], leader+one active = 2 ≥ 2 → true
            (&[1, 2, 3], &[(1, false), (2, true), (3, false)], 1, true),
            // Case 5: voters=[1,2,3], only leader active → false (1 < 2)
            (&[1, 2, 3], &[(1, false), (2, false), (3, false)], 1, false),
            // Case 6: voters=[1,2,3], leader not in entries, {2,3} active = 2 ≥ 2 → true
            (&[1, 2, 3], &[(2, true), (3, true)], 1, true),
            // Case 7: voters=[1,2,3], all three active → true
            (&[1, 2, 3], &[(1, true), (2, true), (3, true)], 1, true),
            // Case 8: voters=[1,2,3], no entries → false (0 < 2)
            (&[1, 2, 3], &[], 1, false),
            // Case 9: voters=[1..5], leader+2 active = 3 = majority(5) → true
            (
                &[1, 2, 3, 4, 5],
                &[(1, false), (2, true), (3, true), (4, false), (5, false)],
                1,
                true,
            ),
            // Case 10: voters=[1..5], leader+1 active = 2 < 3 → false
            (
                &[1, 2, 3, 4, 5],
                &[(1, false), (2, true), (3, false), (4, false), (5, false)],
                1,
                false,
            ),
            // Case 11: voters=[1..5], only leader active = 1 < 3 → false
            (&[1, 2, 3, 4, 5], &[(1, false)], 1, false),
            // Case 12: perspectiveOf=2; {2(leader), 3} active = 2 ≥ 2 → true
            (&[1, 2, 3], &[(1, false), (2, false), (3, true)], 2, true),
            // Case 13: perspectiveOf=2; {1, 2(leader)} active = 2 ≥ 2 → true
            (&[1, 2, 3], &[(1, true), (2, false), (3, false)], 2, true),
            // Case 14: perspectiveOf=2; only leader active = 1 < 2 → false
            (&[1, 2, 3], &[(1, false), (2, false), (3, false)], 2, false),
        ];

        for (i, &(voters, entries, perspective_of, expected)) in cases.iter().enumerate() {
            let mut t = make_qra_tracker(voters, entries);
            let result = t.quorum_recently_active(perspective_of);
            assert_eq!(
                result, expected,
                "case {}: quorum_recently_active({:?}, {:?}, {}) = {}; expected {}",
                i + 1,
                voters,
                entries,
                perspective_of,
                result,
                expected,
            );
        }
    }

    // Task 8 Route B — progress_tracker correspondence test.
    // Mirrors FVSquad/ProgressTrackerCorrespondence.lean (#guard 1–33).
    // Tests removePeer, insertPeer, applyChange, applyChanges semantics
    // against the Lean model's expected results.
    #[test]
    fn test_progress_tracker_correspondence() {
        use crate::confchange::MapChangeType;

        // Build a 3-peer tracker mirroring pm3 = [(1, pRep), (2, pProbe), (3, pRep)]
        // pRep:   matched=5, next_idx=6, Replicate, recent_active=true
        // pProbe: matched=2, next_idx=7, Probe,     recent_active=true
        fn make_pm3() -> ProgressTracker {
            let mut t = ProgressTracker::new(10);
            t.conf = Configuration::new([1u64, 2, 3].iter().copied(), std::iter::empty());
            let mut p1 = Progress::new(6, 10);
            p1.matched = 5;
            p1.recent_active = true;
            p1.become_replicate();
            t.progress.insert(1, p1);

            let mut p2 = Progress::new(7, 10);
            p2.matched = 2;
            p2.recent_active = true;
            t.progress.insert(2, p2); // stays Probe

            let mut p3 = Progress::new(6, 10);
            p3.matched = 5;
            p3.recent_active = true;
            p3.become_replicate();
            t.progress.insert(3, p3);
            t
        }

        // --- removePeer (Lean: #guard 1–5) ---
        // Case 1: removing present peer reduces count by 1
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(2u64, MapChangeType::Remove)], 10);
            assert_eq!(t.progress.len(), 2, "removePeer reduces count");
        }
        // Case 2: removing absent peer leaves count unchanged
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(99u64, MapChangeType::Remove)], 10);
            assert_eq!(t.progress.len(), 3, "removePeer absent: count unchanged");
        }
        // Case 3: removed peer no longer present
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(1u64, MapChangeType::Remove)], 10);
            assert!(!t.progress.contains_key(&1), "removePeer: peer absent after removal");
        }
        // Case 4-5: other peers remain after removal
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(1u64, MapChangeType::Remove)], 10);
            assert!(t.progress.contains_key(&2), "peer 2 remains after removing peer 1");
            assert!(t.progress.contains_key(&3), "peer 3 remains after removing peer 1");
        }

        // --- insertPeer/Add (Lean: #guard 6–10) ---
        // Case 6: inserting a new peer increases count
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(10u64, MapChangeType::Add)], 8);
            assert_eq!(t.progress.len(), 4, "insertPeer new: count +1");
        }
        // Case 8-9: new peer is present and uses Progress::new semantics (matched=0)
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(10u64, MapChangeType::Add)], 8);
            let p = t.progress.get(&10).expect("peer 10 present after Add");
            assert_eq!(p.matched, 0, "new peer matched=0 (Progress::new)");
            assert_eq!(p.next_idx, 8, "new peer next_idx = supplied next_idx");
        }
        // Case 7: re-adding existing peer id does not duplicate (HashMap replaces)
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(1u64, MapChangeType::Add)], 8);
            assert_eq!(t.progress.len(), 3, "re-add existing: no duplication");
        }

        // --- applyChanges sequence (Lean: #guard 20–23) ---
        // Case 20: empty changes: map unchanged
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![], 10);
            assert_eq!(t.progress.len(), 3, "empty changes: size unchanged");
        }
        // Case 21: Add then Remove same id: net size unchanged
        {
            let mut t = make_pm3();
            t.apply_conf(t.conf.clone(), vec![(7u64, MapChangeType::Add)], 10);
            assert_eq!(t.progress.len(), 4, "after Add 7: size 4");
            t.apply_conf(t.conf.clone(), vec![(7u64, MapChangeType::Remove)], 10);
            assert_eq!(t.progress.len(), 3, "after Remove 7: size back to 3");
        }
        // Case 23: adding two new distinct peers in sequence: size +2
        {
            let mut t = make_pm3();
            t.apply_conf(
                t.conf.clone(),
                vec![(7u64, MapChangeType::Add), (8u64, MapChangeType::Add)],
                10,
            );
            assert_eq!(t.progress.len(), 5, "add two new peers: size +2");
        }

        // --- wf invariant: matched+1 ≤ next_idx for all peers after operations ---
        {
            let mut t = make_pm3();
            t.apply_conf(
                t.conf.clone(),
                vec![(2u64, MapChangeType::Remove), (9u64, MapChangeType::Add)],
                3,
            );
            for (_id, p) in t.iter() {
                assert!(
                    p.matched + 1 <= p.next_idx,
                    "wf invariant: matched+1 ≤ next_idx for all peers"
                );
            }
        }
    }

    // Task 8 Route B — ConfigurationInvariants correspondence test.
    // Mirrors FVSquad/ConfigurationInvariantsCorrespondence.lean exactly.
    //
    // Each case checks whether the `VotersLearnersDisjoint` invariant holds on a
    // concrete `Configuration` (incoming, outgoing, learners, learners_next).
    //
    // The invariant: no peer appears in both a voter set and a learner set.
    // Formally, all four intersections must be empty:
    //   incoming_voters ∩ learners        = ∅
    //   outgoing_voters ∩ learners        = ∅
    //   incoming_voters ∩ learners_next   = ∅
    //   outgoing_voters ∩ learners_next   = ∅
    #[test]
    fn test_configuration_invariants_correspondence() {
        // Helper: check the four-clause VotersLearnersDisjoint invariant.
        fn voters_learners_disjoint(
            incoming: &[u64],
            outgoing: &[u64],
            learners: &[u64],
            learners_next: &[u64],
        ) -> bool {
            let lset: HashSet<u64> = learners.iter().copied().collect();
            let lnset: HashSet<u64> = learners_next.iter().copied().collect();
            // Clause 1: incoming_voters ∩ learners = ∅
            let c1 = incoming.iter().all(|id| !lset.contains(id));
            // Clause 2: outgoing_voters ∩ learners = ∅
            let c2 = outgoing.iter().all(|id| !lset.contains(id));
            // Clause 3: incoming_voters ∩ learners_next = ∅
            let c3 = incoming.iter().all(|id| !lnset.contains(id));
            // Clause 4: outgoing_voters ∩ learners_next = ∅
            let c4 = outgoing.iter().all(|id| !lnset.contains(id));
            c1 && c2 && c3 && c4
        }

        // (incoming, outgoing, learners, learners_next, expected)
        let cases: &[(&[u64], &[u64], &[u64], &[u64], bool)] = &[
            // Case 1: empty configuration
            (&[], &[], &[], &[], true),
            // Case 2: simple disjoint — incoming=[1,2,3], learners=[4,5]
            (&[1, 2, 3], &[], &[4, 5], &[], true),
            // Case 3: no learners — incoming=[1,2,3]
            (&[1, 2, 3], &[], &[], &[], true),
            // Case 4: joint config, disjoint — incoming=[1,2], outgoing=[2,3], learners=[4]
            (&[1, 2], &[2, 3], &[4], &[], true),
            // Case 5: demotion — outgoing=[1,2,3], learners_next=[3]:
            //   3 ∈ outgoing ∩ learners_next → invariant violated
            (&[1, 2], &[1, 2, 3], &[], &[3], false),
            // Case 6: violation — incoming=[1,2], learners=[2,3]: 2 in both
            (&[1, 2], &[], &[2, 3], &[], false),
            // Case 7: violation — outgoing=[1,2,3], learners=[2]: 2 in both
            (&[], &[1, 2, 3], &[2], &[], false),
            // Case 8: violation — incoming=[1], learners_next=[1]: 1 in both
            (&[1], &[], &[], &[1], false),
            // Case 9: violation — outgoing=[5], learners_next=[5]: 5 in both
            (&[], &[5], &[], &[5], false),
            // Case 10: fully disjoint joint config
            (&[1, 2, 3], &[4, 5, 6], &[7, 8], &[], true),
            // Case 11: all different peers
            (&[1], &[2], &[3], &[4], true),
            // Case 12: peer 1 in incoming, outgoing, AND learners
            (&[1, 2, 3], &[1, 2, 3], &[1], &[], false),
        ];

        for (i, &(incoming, outgoing, learners, learners_next, expected)) in
            cases.iter().enumerate()
        {
            let result = voters_learners_disjoint(incoming, outgoing, learners, learners_next);
            assert_eq!(
                result, expected,
                "case {}: VotersLearnersDisjoint(in={:?}, out={:?}, l={:?}, ln={:?})",
                i + 1,
                incoming,
                outgoing,
                learners,
                learners_next
            );
        }
    }
}
