// Copyright 2019 TiKV Project Authors. Licensed under Apache-2.0.

// Copyright 2016 The etcd Authors
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

use std::collections::VecDeque;

#[cfg(not(feature = "aeneas"))]
use slog::Logger;
#[cfg(feature = "aeneas")]
use crate::Logger;

use crate::eraftpb::Message;
use crate::{HashMap, HashSet};

/// Determines the relative safety of and consistency of read only requests.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum ReadOnlyOption {
    /// Safe guarantees the linearizability of the read only request by
    /// communicating with the quorum. It is the default and suggested option.
    #[default]
    Safe,
    /// LeaseBased ensures linearizability of the read only request by
    /// relying on the leader lease. It can be affected by clock drift.
    /// If the clock drift is unbounded, leader might keep the lease longer than it
    /// should (clock can move backward/pause without any bound). ReadIndex is not safe
    /// in that case.
    LeaseBased,
}

/// ReadState provides state for read only query.
///
/// It's caller's responsibility to send MsgReadIndex first before getting
/// this state from ready. It's also caller's duty to differentiate if this
/// state is what it requests through request_ctx, e.g. given a unique id as
/// request_ctx.
#[derive(Default, Debug, PartialEq, Eq, Clone)]
pub struct ReadState {
    /// The index of the read state.
    pub index: u64,
    /// A datagram consisting of context about the request.
    pub request_ctx: Vec<u8>,
}

#[derive(Default, Debug, Clone)]
pub struct ReadIndexStatus {
    pub req: Message,
    pub index: u64,
    pub acks: HashSet<u64>,
}

#[derive(Default, Debug, Clone)]
pub struct ReadOnly {
    pub option: ReadOnlyOption,
    pub pending_read_index: HashMap<Vec<u8>, ReadIndexStatus>,
    pub read_index_queue: VecDeque<Vec<u8>>,
}

impl ReadOnly {
    pub fn new(option: ReadOnlyOption) -> ReadOnly {
        ReadOnly {
            option,
            pending_read_index: HashMap::default(),
            read_index_queue: VecDeque::new(),
        }
    }

    /// Adds a read only request into readonly struct.
    ///
    /// `index` is the commit index of the raft state machine when it received
    /// the read only request.
    ///
    /// `m` is the original read only request message from the local or remote node.
    pub fn add_request(&mut self, index: u64, req: Message, self_id: u64) {
        let ctx = {
            let key: &[u8] = req.entries[0].data.as_ref();
            if self.pending_read_index.contains_key(key) {
                return;
            }
            key.to_vec()
        };
        let mut acks = HashSet::<u64>::default();
        acks.insert(self_id);
        let status = ReadIndexStatus { req, index, acks };
        self.pending_read_index.insert(ctx.clone(), status);
        self.read_index_queue.push_back(ctx);
    }

    /// Notifies the ReadOnly struct that the raft state machine received
    /// an acknowledgment of the heartbeat that attached with the read only request
    /// context.
    pub fn recv_ack(&mut self, id: u64, ctx: &[u8]) -> Option<&HashSet<u64>> {
        self.pending_read_index.get_mut(ctx).map(|rs| {
            rs.acks.insert(id);
            &rs.acks
        })
    }

    /// Advances the read only request queue kept by the ReadOnly struct.
    /// It dequeues the requests until it finds the read only request that has
    /// the same context as the given `ctx`.
    pub fn advance(&mut self, ctx: &[u8], logger: &Logger) -> Vec<ReadIndexStatus> {
        let mut rss = vec![];
        if let Some(i) = self.read_index_queue.iter().position(|x| {
            if !self.pending_read_index.contains_key(x) {
                fatal!(logger, "cannot find correspond read state from pending map");
            }
            *x == ctx
        }) {
            for _ in 0..=i {
                let rs = self.read_index_queue.pop_front().unwrap();
                let status = self.pending_read_index.remove(&rs).unwrap();
                rss.push(status);
            }
        }
        rss
    }

    /// Returns the context of the last pending read only request in ReadOnly struct.
    pub fn last_pending_request_ctx(&self) -> Option<Vec<u8>> {
        self.read_index_queue.back().cloned()
    }

    #[inline]
    pub fn pending_read_count(&self) -> usize {
        self.read_index_queue.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eraftpb::Entry;
    use crate::default_logger;

    /// Build a `Message` whose `entries[0].data` is `key` — matches how Raft
    /// calls `add_request` in practice (the context comes from the first entry's data).
    fn make_req(key: &[u8]) -> Message {
        let mut e = Entry::default();
        e.data = key.to_vec().into();
        let mut m = Message::default();
        m.entries = vec![e].into();
        m
    }

    /// Helper: collect acks for `ctx` from a ReadOnly (sorted for determinism).
    fn sorted_acks(ro: &ReadOnly, ctx: &[u8]) -> Vec<u64> {
        match ro.pending_read_index.get(ctx) {
            None => vec![],
            Some(rs) => {
                let mut v: Vec<u64> = rs.acks.iter().cloned().collect();
                v.sort_unstable();
                v
            }
        }
    }

    /// Correspondence test: mirrors the 14 `#guard` cases in
    /// `formal-verification/lean/FVSquad/ReadOnlyCorrespondence.lean`.
    ///
    /// Context mapping: Lean `Nat` k → Rust `vec![k as u8]`.
    #[test]
    fn test_read_only_correspondence() {
        let l = default_logger();

        // Case 1–2: empty state
        let ro = ReadOnly::new(ReadOnlyOption::Safe);
        assert_eq!(ro.pending_read_count(), 0, "case 1: empty count");
        assert_eq!(ro.last_pending_request_ctx(), None, "case 2: empty last_ctx");

        // Case 3: add one request
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            ro.add_request(100, make_req(&ctx1), 1);
            assert_eq!(ro.pending_read_count(), 1, "case 3: count");
            assert_eq!(ro.last_pending_request_ctx(), Some(ctx1.clone()), "case 3: last_ctx");
            assert_eq!(
                ro.pending_read_index.get(ctx1.as_slice()).map(|rs| rs.index),
                Some(100),
                "case 3: index"
            );
            assert_eq!(sorted_acks(&ro, &ctx1), vec![1], "case 3: acks");
        }

        // Case 4: duplicate add_request is idempotent
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            ro.add_request(100, make_req(&ctx1), 1);
            ro.add_request(200, make_req(&ctx1), 2); // duplicate — ignored
            assert_eq!(ro.pending_read_count(), 1, "case 4: idempotent count");
            assert_eq!(
                ro.pending_read_index.get(ctx1.as_slice()).map(|rs| rs.index),
                Some(100),
                "case 4: original index retained"
            );
        }

        // Case 5: add two distinct requests → queue=[1,2]
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            let ctx2 = vec![2u8];
            ro.add_request(100, make_req(&ctx1), 1);
            ro.add_request(101, make_req(&ctx2), 1);
            assert_eq!(ro.pending_read_count(), 2, "case 5: count=2");
            assert_eq!(ro.last_pending_request_ctx(), Some(ctx2.clone()), "case 5: last=2");
            assert_eq!(
                ro.read_index_queue.iter().cloned().collect::<Vec<_>>(),
                vec![ctx1, ctx2],
                "case 5: queue order"
            );
        }

        // Case 6: add three requests → count=3
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            ro.add_request(101, make_req(&[2u8]), 1);
            ro.add_request(102, make_req(&[3u8]), 1);
            assert_eq!(ro.pending_read_count(), 3, "case 6: count=3");
            assert_eq!(ro.last_pending_request_ctx(), Some(vec![3u8]), "case 6: last=3");
        }

        // Case 7: recv_ack on absent ctx → None
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let result = ro.recv_ack(7, &[99u8]);
            assert!(result.is_none(), "case 7: absent recv_ack");
        }

        // Case 8: recv_ack adds new id to ack set
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            ro.add_request(100, make_req(&ctx1), 1);
            let acks = ro.recv_ack(2, &ctx1).expect("case 8: should be Some");
            let mut sorted: Vec<u64> = acks.iter().cloned().collect();
            sorted.sort_unstable();
            assert_eq!(sorted, vec![1, 2], "case 8: acks=[1,2]");
        }

        // Case 9: recv_ack duplicate id is idempotent
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            ro.add_request(100, make_req(&ctx1), 1);
            ro.recv_ack(2, &ctx1);
            let acks = ro.recv_ack(2, &ctx1).expect("case 9: should be Some");
            let mut sorted: Vec<u64> = acks.iter().cloned().collect();
            sorted.sort_unstable();
            assert_eq!(sorted, vec![1, 2], "case 9: acks idempotent");
        }

        // Case 10: advance on absent ctx → no-op
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            let rss = ro.advance(&[99u8], &l);
            assert!(rss.is_empty(), "case 10: advance absent");
            assert_eq!(ro.pending_read_count(), 1, "case 10: count unchanged");
        }

        // Case 11: advance first of three
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            ro.add_request(101, make_req(&[2u8]), 1);
            ro.add_request(102, make_req(&[3u8]), 1);
            let rss = ro.advance(&[1u8], &l);
            assert_eq!(rss.len(), 1, "case 11: 1 status returned");
            assert_eq!(rss[0].index, 100, "case 11: index=100");
            assert_eq!(ro.pending_read_count(), 2, "case 11: count=2");
            let remaining: Vec<_> = ro.read_index_queue.iter().cloned().collect();
            assert_eq!(remaining, vec![vec![2u8], vec![3u8]], "case 11: queue=[2,3]");
        }

        // Case 12: advance second of three (middle)
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            ro.add_request(101, make_req(&[2u8]), 1);
            ro.add_request(102, make_req(&[3u8]), 1);
            let rss = ro.advance(&[2u8], &l);
            assert_eq!(rss.len(), 2, "case 12: 2 statuses returned");
            assert_eq!(rss[0].index, 100, "case 12: first index=100");
            assert_eq!(rss[1].index, 101, "case 12: second index=101");
            assert_eq!(ro.pending_read_count(), 1, "case 12: count=1");
        }

        // Case 13: advance last of three (drains all)
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            ro.add_request(101, make_req(&[2u8]), 1);
            ro.add_request(102, make_req(&[3u8]), 1);
            let rss = ro.advance(&[3u8], &l);
            assert_eq!(rss.len(), 3, "case 13: 3 statuses returned");
            assert_eq!(rss[0].index, 100, "case 13: index[0]=100");
            assert_eq!(rss[1].index, 101, "case 13: index[1]=101");
            assert_eq!(rss[2].index, 102, "case 13: index[2]=102");
            assert_eq!(ro.pending_read_count(), 0, "case 13: count=0");
        }

        // Case 14: advance then add new request
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            ro.add_request(100, make_req(&[1u8]), 1);
            ro.add_request(101, make_req(&[2u8]), 1);
            ro.advance(&[1u8], &l);
            ro.add_request(103, make_req(&[3u8]), 1);
            let q: Vec<_> = ro.read_index_queue.iter().cloned().collect();
            assert_eq!(q, vec![vec![2u8], vec![3u8]], "case 14: queue=[2,3]");
            assert_eq!(ro.pending_read_count(), 2, "case 14: count=2");
        }

        // Case 15 (bonus): recv_ack then advance returns enriched status
        {
            let mut ro = ReadOnly::new(ReadOnlyOption::Safe);
            let ctx1 = vec![1u8];
            ro.add_request(100, make_req(&ctx1), 1);
            ro.recv_ack(2, &ctx1);
            let rss = ro.advance(&ctx1, &l);
            assert_eq!(rss.len(), 1, "case 15: 1 status");
            let mut sorted: Vec<u64> = rss[0].acks.iter().cloned().collect();
            sorted.sort_unstable();
            assert_eq!(sorted, vec![1, 2], "case 15: acks=[1,2]");
            assert_eq!(ro.pending_read_count(), 0, "case 15: queue empty");
        }
    }
}
